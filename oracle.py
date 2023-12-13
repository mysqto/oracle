import argparse
import http.client
import ipaddress
import multiprocessing
import os.path
import random
import re
import signal
import string
import threading
import time
import uuid
from concurrent.futures import ThreadPoolExecutor
from configparser import ConfigParser

import cytoolz
import oci
import requests
from loguru import logger
from oci.config import validate_config
from oci.core import ComputeClient, VirtualNetworkClient
from oci.core.models import Instance, Subnet, Shape, Image, Vcn, Vnic, Ipv6, PublicIp, PrivateIp, SecurityList, \
    UpdateSecurityListDetails, IngressSecurityRule, TcpOptions, PortRange, UdpOptions, EgressSecurityRule, RouteTable, \
    InternetGateway, RouteRule, AddSubnetIpv6CidrDetails, AddVcnIpv6CidrDetails, UpdateRouteTableDetails
from oci.identity.models import Tenancy


def random_v6_subnet_cidr_block(base_cidr, subnet_cidr_block_size=64):
    base_network = ipaddress.IPv6Network(base_cidr)
    random_fill_bits = subnet_cidr_block_size - base_network.prefixlen
    random_bits = random.getrandbits(random_fill_bits)
    random_cidr_suffix = random_bits << subnet_cidr_block_size
    return ipaddress.IPv6Network((base_network.network_address + random_cidr_suffix, subnet_cidr_block_size))


class IPAddress:
    __v4__ = None
    __v6s__ = []

    def __init__(self, v4=None, v6s=None):
        self.v4 = v4
        self.v6s = v6s

    @property
    def v4(self):
        return self.__v4__

    @v4.setter
    def v4(self, v4):
        self.__v4__ = v4

    @property
    def v6s(self):
        return self.__v6s__

    @v6s.setter
    def v6s(self, v6s):
        self.__v6s__ = v6s

    def __str__(self):
        return '{"v4": "%s", "v6s": %s}' % (self.v4, '["%s"]' % '", "'.join(self.v6s) if len(self.v6s) > 0 else "[]")

    def pretty(self):
        prettied = "`%s` `%s`" % (self.v4, ('%s' % '` `'.join(self.v6s) if len(self.v6s) > 0 else ""))
        return prettied.replace("``", "").strip()


class TelegramBot:

    def __init__(self, token, api_host='api.telegram.org'):
        self.token = token
        self.api_host = api_host
        self.user_ids = {}

    @property
    def token(self):
        return self.__token__

    @token.setter
    def token(self, token):
        self.__token__ = token

    @property
    def user_ids(self):
        return self.__user_ids__

    @user_ids.setter
    def user_ids(self, user_ids):
        self.__user_ids__ = user_ids

    def add_user(self, user):
        self.__user_ids__[user] = True

    def remove_user(self, user):
        self.__user_ids__.pop(user)

    def disable_user(self, user):
        self.__user_ids__[user] = False

    @property
    def api_host(self):
        return self.__api_host__

    @api_host.setter
    def api_host(self, api_host):
        self.__api_host__ = api_host

    def send_message(self, message, user=None):
        if user is None:
            for u in self.user_ids:
                self.send_message(message, u)
            return
        if self.user_ids[user]:
            url = f'https://{self.api_host}/bot{self.token}/sendMessage'
            data = {'chat_id': user, 'text': message, 'parse_mode': 'Markdown'}
            try:
                requests.post(url, data=data)
            except Exception as e:
                print(e)


class SSHKey:
    def __init__(self, private_key, public_key, passphrase=None):
        self.private_key = private_key
        self.public_key = public_key
        self.passphrase = passphrase

    @property
    def private_key(self):
        return self.__private_key__

    @private_key.setter
    def private_key(self, private_key):
        self.__private_key__ = private_key

    @property
    def passphrase(self):
        return self.__passphrase__

    @passphrase.setter
    def passphrase(self, passphrase):
        self.__passphrase__ = passphrase

    @property
    def public_key(self):
        return self.__public_key__

    @public_key.setter
    def public_key(self, public_key):
        self.__public_key__ = public_key


class OCIStatus:
    def __init__(self, status, code, message):
        self.status = status
        self.code = code
        self.message = message

    def __str__(self):
        return '{"status":%d, "code": "%s", "message": "%s"}' % (self.status, self.code, self.message)

    def __repr__(self):
        return self.message

    def __eq__(self, other):
        return self.code == other.code

    @property
    def code(self):
        return self.__code__

    @code.setter
    def code(self, code):
        self.__code__ = code

    @property
    def message(self):
        return self.__message__

    @message.setter
    def message(self, message):
        self.__message__ = message

    @property
    def status(self):
        return self.__status__

    @status.setter
    def status(self, status):
        self.__status__ = status


def is_success(status):
    return status.status == http.client.OK and status.code == "Success"


def is_failed(status):
    return isinstance(status, OCIStatus) and not is_success(status)


def is_rate_limit(status):
    return (status.status == http.client.TOO_MANY_REQUESTS and
            status.code == "TooManyRequests" and
            status.message == "Too many requests for the user")


def is_out_of_host_capacity(status):
    return (status.status == http.client.INTERNAL_SERVER_ERROR and
            status.code == "InternalError" and
            status.message == "Out of host capacity.")


def is_quota_exceeded(status):
    return (status.status == http.client.BAD_REQUEST and (
            status.code == "QuotaExceeded" or status.code == "LimitExceeded"))


class TerraformParameter:
    def __init__(self, file_path: str | None) -> None:
        self.__availability_domain__ = None
        self.__ocpus__ = None
        self.__memory_in_gbs__ = None
        self.__hostname_label__ = None
        self.__compartment_id__ = None
        self.__assign_public_ip__ = None
        self.__subnet_id__ = None
        self.__display_name__ = None
        self.__source_id__ = None
        self.__boot_volume_vpus_per_gb__ = None
        self.__boot_volume_size__ = None
        self._ssh_authorized_keys_ = None
        self.__shape__ = None
        self.__file_buf__ = None
        if file_path is not None:
            self.parser(file_path)

    def parser(self, file_path):
        try:
            tf = open(file_path, "r")
            self.__file_buf__ = tf.read()
            tf.close()

        except Exception as e:
            logger.log("main.tf文件打开失败, 将无法执行创建操作", e)
            return

        shape_regex = re.compile('shape = "(.*)"')
        self.__shape__ = shape_regex.findall(self.__file_buf__).pop()

        compartment_id_regex = re.compile('compartment_id = "(.*)"')
        self.__compartment_id__ = compartment_id_regex.findall(self.__file_buf__).pop()

        # 内存
        try:
            memory_in_gbs_regex = re.compile('memory_in_gbs = "(.*)"')
            self.memory_in_gbs = float(memory_in_gbs_regex.findall(self.__file_buf__).pop())
        except IndexError:
            self.memory_in_gbs = 1
        # cpu
        try:
            cpu_regex = re.compile('ocpus = "(.*)"')
            self.ocpus = float(cpu_regex.findall(self.__file_buf__).pop())
        except IndexError:
            self.ocpus = 1

        # 可用域
        availability_domain_regex = re.compile('availability_domain = "(.*)"')

        self.availability_domain = availability_domain_regex.findall(self.__file_buf__).pop()

        # 子网id
        subnet_regex = re.compile('subnet_id = "(.*)"')
        self.subnet_id = subnet_regex.findall(self.__file_buf__).pop()

        # 实例名称
        display_name_regex = re.compile('display_name = "(.*)"')
        display_name = display_name_regex.findall(self.__file_buf__).pop()
        display_name = display_name.strip().replace(" ", "-")
        self.display_name = display_name
        self.hostname_label = display_name.replace("_", "-")

        try:
            assign_public_ip_regex = re.compile('assign_public_ip = "(.*)"')
            assign_public_ip = assign_public_ip_regex.findall(self.__file_buf__).pop()
            self.assign_public_ip = True if assign_public_ip == "true" else False
        except IndexError:
            self.assign_public_ip = False

        # source_id
        source_id_regex = re.compile('source_id = "(.*)"')
        self.source_id = source_id_regex.findall(self.__file_buf__)[0]
        # 硬盘大小
        boot_volume_size_in_gbs_regex = re.compile('boot_volume_size_in_gbs = "(.*)"')
        try:
            self.boot_volume_size_in_gbs = float(boot_volume_size_in_gbs_regex.findall(self.__file_buf__).pop())
        except IndexError:
            self.boot_volume_size_in_gbs = 50.0

        boot_volume_vpus_per_gb_regex = re.compile('boot_volume_vpus_per_gb = "(.*)"')
        try:
            self.boot_volume_vpus_per_gb = float(boot_volume_vpus_per_gb_regex.findall(self.__file_buf__).pop())
        except IndexError:
            logger.info("没有找到boot_volume_vpus_per_gb，使用默认值120")
            self.boot_volume_vpus_per_gb = 120

        ssh_authorized_keys_regex = re.compile('"ssh_authorized_keys" = "(.*)"')
        try:
            self.ssh_authorized_keys = ssh_authorized_keys_regex.findall(self.__file_buf__).pop()
        except IndexError as e:
            logger.info(f"没有找到ssh_authorized_keys {e}, 生成一个新的密钥")
            self.ssh_authorized_keys = generate_ssh_key(comments=f"oci-{self.display_name}").public_key

    @property
    def shape(self):
        return self.__shape__

    @shape.setter
    def shape(self, shape):
        self.__shape__ = shape

    @property
    def ssh_authorized_keys(self):
        return self._ssh_authorized_keys_.public_key

    def ssh_key(self):
        return self._ssh_authorized_keys_

    @ssh_authorized_keys.setter
    def ssh_authorized_keys(self, key):
        self._ssh_authorized_keys_ = key

    @property
    def boot_volume_size_in_gbs(self):
        return self.__boot_volume_size__

    @boot_volume_size_in_gbs.setter
    def boot_volume_size_in_gbs(self, size):
        self.__boot_volume_size__ = size

    @property
    def boot_volume_vpus_per_gb(self):
        return self.__boot_volume_vpus_per_gb__

    @boot_volume_vpus_per_gb.setter
    def boot_volume_vpus_per_gb(self, boot_volume_vpus_per_gb):
        self.__boot_volume_vpus_per_gb__ = boot_volume_vpus_per_gb

    @property
    def source_id(self):
        return self.__source_id__

    @source_id.setter
    def source_id(self, source_id):
        self.__source_id__ = source_id

    @property
    def display_name(self):
        return self.__display_name__

    @display_name.setter
    def display_name(self, display_name):
        self.__display_name__ = display_name

    @property
    def hostname_label(self):
        return self.__hostname_label__

    @hostname_label.setter
    def hostname_label(self, hostname):
        self.__hostname_label__ = hostname

    @property
    def subnet_id(self):
        return self.__subnet_id__

    @subnet_id.setter
    def subnet_id(self, subnet_id):
        self.__subnet_id__ = subnet_id

    @property
    def assign_public_ip(self):
        return self.__assign_public_ip__

    @assign_public_ip.setter
    def assign_public_ip(self, assign_public_ip):
        self.__assign_public_ip__ = assign_public_ip

    @property
    def compartment_id(self):
        return self.__compartment_id__

    @compartment_id.setter
    def compartment_id(self, cid):
        self.__compartment_id__ = cid

    @property
    def memory_in_gbs(self):
        return self.__memory_in_gbs__

    @memory_in_gbs.setter
    def memory_in_gbs(self, mm):
        self.__memory_in_gbs__ = mm

    @property
    def ocpus(self):
        return self.__ocpus__

    @ocpus.setter
    def ocpus(self, ocpus):
        self.__ocpus__ = ocpus

    @property
    def availability_domain(self):
        return self.__availability_domain__

    @availability_domain.setter
    def availability_domain(self, availability_domain):
        self.__availability_domain__ = availability_domain


class OciConfig:
    def __init__(self, oci_config_file="~/.oci/config", oci_profile="DEFAULT"):
        self.__config__ = None
        with open(oci_config_file) as ocf:
            parser = ConfigParser()
            parser.read_file(ocf)
            config = dict(parser[oci_profile])
            validate_config(config)
            self.__config__ = config

    @property
    def compartment_id(self):
        return self.__config__['tenancy']

    def __getitem__(self, item):
        return self.__config__[item]

    @staticmethod
    def keys():
        return "user", "fingerprint", "key_file", "tenancy", "region"


def generate_ssh_key(passphrase=None, comments="oci-arm"):
    import os
    import shutil
    import tempfile
    import subprocess

    if passphrase is None:
        # Generate a random passphrase with symbols.
        passphrase = ''.join(
            [random.choice(string.ascii_letters + string.digits + string.punctuation) for _ in range(16)])

    # Create a temporary directory.
    temp_dir = tempfile.mkdtemp()

    # Generate a new SSH keypair.
    ssh_keygen_process = subprocess.Popen(
        ['ssh-keygen', '-N', passphrase, '-t', 'rsa', '-b', '4096', '-C', comments, '-f',
         os.path.join(temp_dir, 'id_rsa'), '-q'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    ssh_keygen_process.communicate(input=b'\n\n\n')
    ssh_keygen_process.wait()

    # Copy the private key to the temporary directory.
    private_key_path = os.path.join(temp_dir, 'id_rsa')

    # Copy the public key to the temporary directory.
    public_key_path = os.path.join(temp_dir, 'id_rsa.pub')

    # Read the public key.
    with open(public_key_path, 'r') as public_key_file:
        public_key = public_key_file.read()

    # Read the private key.
    with open(private_key_path, 'r') as private_key_file:
        private_key = private_key_file.read()

    # Remove the temporary directory.
    shutil.rmtree(temp_dir)

    return SSHKey(private_key=private_key, public_key=public_key, passphrase=passphrase)


class OCIClient:
    __wait_time__ = 5.0
    __description__ = ""
    __oci_config__ = None
    __oci_client__ = None
    __instance_tf__ = None
    __instance_id__ = None
    __public_ip__ = None
    __network_client__ = None
    __identity_client__ = None
    __client_name__ = None
    __telegram_bot__ = None
    __oci_profile__ = None
    __thread_pool__ = None
    __exiting__ = None
    __start_counter__ = {}
    __create_counter__ = {}
    __ssh_authorized_keys__ = None

    def notify(self, text):
        self.telegram(text)
        self.log(text)

    def log(self, text):
        message = f"[{self.name().ljust(20)}] {text.replace('`', '')}"
        logger.info(message)

    def fatal(self, text):
        message = f"[{self.name().ljust(20)}] {text.replace('`', '')}"
        logger.error(message)
        self.telegram(message)

    def telegram(self, text):
        if self.telegram_bot is not None:
            self.telegram_bot.send_message(text)

    @property
    def description(self):
        return self.__description__

    @description.setter
    def description(self, description):
        self.__description__ = description

    def start_counter(self, machine=None):
        if machine not in self.__start_counter__:
            self.__start_counter__[machine] = 0
        return self.__start_counter__[machine]

    def increase_start_counter(self, machine=None):
        if machine not in self.__start_counter__:
            self.__start_counter__[machine] = 0
        self.__start_counter__[machine] += 1

    def create_counter(self, machine=None):
        if machine not in self.__create_counter__:
            self.__create_counter__[machine] = 0
        return self.__create_counter__[machine]

    def increase_create_counter(self, machine=None):
        if machine not in self.__create_counter__:
            self.__create_counter__[machine] = 0
        self.__create_counter__[machine] += 1

    @property
    def wait_time(self):
        return self.__wait_time__

    @wait_time.setter
    def wait_time(self, wait_time):
        self.__wait_time__ = wait_time

    @property
    def oci_config(self):
        return self.__oci_config__

    @oci_config.setter
    def oci_config(self, config):
        self.__oci_config__ = config

    @property
    def public_ip(self):
        return self.__public_ip__

    @public_ip.setter
    def public_ip(self, public_ip):
        self.__public_ip__ = public_ip

    @property
    def oci_client(self):
        return self.__oci_client__

    @oci_client.setter
    def oci_client(self, oci_client):
        self.__oci_client__ = oci_client

    @property
    def network_client(self):
        return self.__network_client__

    @network_client.setter
    def network_client(self, network_client):
        self.__network_client__ = network_client

    @property
    def identity_client(self):
        return self.__identity_client__

    @identity_client.setter
    def identity_client(self, identity_client):
        self.__identity_client__ = identity_client

    @property
    def instance_terraform(self):
        return self.__instance_tf__

    @instance_terraform.setter
    def instance_terraform(self, instance_terraform):
        self.__instance_tf__ = instance_terraform

    @property
    def compartment_id(self):
        return self.oci_config.compartment_id

    @property
    def thread_pool(self):
        return self.__thread_pool__

    @thread_pool.setter
    def thread_pool(self, thread_pool):
        self.__thread_pool__ = thread_pool

    @property
    def client_name(self):
        return self.__client_name__

    @client_name.setter
    def client_name(self, name):
        self.__client_name__ = name

    @property
    def oci_profile(self):
        return self.__oci_profile__

    @oci_profile.setter
    def oci_profile(self, oci_profile_name):
        self.__oci_profile__ = oci_profile_name

    @property
    def exiting(self):
        return self.__exiting__

    @exiting.setter
    def exiting(self, exiting):
        self.__exiting__ = exiting

    @property
    def ssh_authorized_keys(self):
        return self.__ssh_authorized_keys__

    @ssh_authorized_keys.setter
    def ssh_authorized_keys(self, ssh_authorized_keys):
        self.__ssh_authorized_keys__ = ssh_authorized_keys

    def pool(self):
        if self.thread_pool is None:
            # max_workers = 2 * multiprocessing.cpu_count() + 1
            self.thread_pool = ThreadPoolExecutor(max_workers=2 * multiprocessing.cpu_count() + 1)
        return self.thread_pool

    def name(self):
        if self.client_name is None:
            tenancy = self.get_tenancy()
            if isinstance(tenancy, Tenancy):
                name = f'{tenancy.home_region_key}-{tenancy.name}'.lower()
                self.client_name = name
        if self.client_name is None:
            if self.profile_name is not None:
                self.client_name = self.profile_name
            elif self.oci_config is not None and self.oci_config.compartment_id is not None:
                self.client_name = self.oci_config.compartment_id
            else:
                self.client_name = uuid.uuid4()
        return self.client_name

    def vcn_name(self):
        return f"{self.name()}-vcn"

    @property
    def telegram_bot(self):
        return self.__telegram_bot__

    @telegram_bot.setter
    def telegram_bot(self, telegram_bot):
        self.__telegram_bot__ = telegram_bot

    def add_log_file(self):
        file_name = f"{self.name()}.log"
        file_path = os.path.join("logs", file_name)
        if not os.path.exists("logs"):
            os.mkdir("logs")
        logger.add(file_path, filter=lambda record: self.name() in record['message'], rotation="1 day",
                   retention="7 days", level="DEBUG", compression="gz")

    def __init__(self, oci_config_file, oci_profile, ssh_authorized_keys=None, tf_filepath=None, telegram_bot=None,
                 thread_pool=None, exiting=None) -> None:
        self.profile_name = None
        self.public_ip = None
        self.telegram_bot = telegram_bot
        if not os.path.exists(oci_config_file):
            self.fatal(f"配置文件{oci_config_file}不存在,请检查配置文件路径")
        if oci_profile is None:
            oci_profile = "DEFAULT"
        self.oci_profile = oci_profile
        config = OciConfig(oci_config_file=os.path.abspath(oci_config_file), oci_profile=oci_profile)
        self.oci_config = config
        self.oci_client = ComputeClient(config=dict(config))
        self.network_client = VirtualNetworkClient(config=dict(config))
        self.identity_client = oci.identity.IdentityClient(config=dict(config))
        if tf_filepath is not None and os.path.exists(tf_filepath):
            self.instance_terraform = TerraformParameter(tf_filepath)
        # override ssh_authorized_keys
        if ssh_authorized_keys is not None and self.instance_terraform is not None:
            self.instance_terraform.ssh_authorized_keys = ssh_authorized_keys
        self.ssh_authorized_keys = ssh_authorized_keys
        # create a thread pool
        self.thread_pool = thread_pool
        self.exiting = exiting
        self.add_log_file()

    def create_instance_task(self, shape="VM.Standard.A1.Flex", instance_terraform=None):
        if shape is not None and instance_terraform is None and self.instance_terraform is None:
            instance_terraform = self.build_instance_terraform(shape=shape,
                                                               ssh_authorized_keys=self.ssh_authorized_keys)
        if instance_terraform is None and self.instance_terraform is not None:
            instance_terraform = self.instance_terraform

        if instance_terraform is None:
            return OCIStatus(http.client.BAD_REQUEST, "NoInstanceTerraform", "没有找到实例配置")

        key_message = "私钥文件: 单独提供，请自行保存"
        if instance_terraform.ssh_key().private_key is not None:
            # save private key to file
            private_key_file = f"{self.name()}_{instance_terraform.display_name}.pem"
            private_key_file = os.path.join(os.path.expanduser("~"), ".ssh", private_key_file)
            with open(private_key_file, "w") as pkf:
                pkf.write(instance_terraform.ssh_key().private_key)
            os.chmod(private_key_file, 0o600)
            self.log(f"开机操作-{instance_terraform.shape}, 保存私钥到文件{private_key_file}")
            key_message = f"私钥文件: {private_key_file}\n私钥密码: {instance_terraform.ssh_key().passphrase}"

        text = ("**🐢:抢🐔开始🐢**\n```\n"
                "Profile: {}\n"
                "区域:    {}\n"
                "实例:    {}\n"
                "机型:    {}\n"
                "CPU:     {}C\n"
                "内存:    {}G\n"
                "硬盘:    {}G\n"
                "{}\n```".format(self.name(), instance_terraform.availability_domain, instance_terraform.display_name,
                                 instance_terraform.shape, instance_terraform.ocpus, instance_terraform.memory_in_gbs,
                                 instance_terraform.boot_volume_size_in_gbs, key_message))
        self.telegram(text)
        instance_name = instance_terraform.display_name
        self.log(
            f"开机操作-第{self.create_counter(machine=instance_name):012d}次-{instance_terraform.shape}, 开始创建实例")
        while not self.exiting.is_set():
            try:
                result = self.create_instance(terraform=instance_terraform)
                self.increase_create_counter()
                if isinstance(result, OCIStatus):
                    if is_rate_limit(result):
                        if self.wait_time < 60:
                            self.wait_time += 2
                        self.log(f"开机操作-第{self.create_counter(machine=instance_name):012d}次-"
                                 f"{instance_terraform.shape}, 请求太快了，自动调整请求时间为{self.wait_time}s")
                        time.sleep(self.wait_time)
                    elif is_out_of_host_capacity(result):
                        # 没有被限速，恢复减少的时间
                        if self.wait_time > 15:
                            self.wait_time -= 10
                        self.log(
                            f"开机操作-第{self.create_counter(machine=instance_name):012d}次-{instance_terraform.shape}, "
                            f"目前没有请求限速,快马加刷中，当前请求间隔{self.wait_time}s")
                        time.sleep(self.wait_time)
                    elif is_quota_exceeded(result):
                        self.log(
                            f"开机操作-第{self.create_counter(machine=instance_name):012d}次-{instance_terraform.shape},"
                            f" 配额超限 {result.message}，脚本停止")
                        break
                    else:
                        self.log(f"开机操作-第{self.create_counter(machine=instance_name):012d}次-"
                                 f"{instance_terraform.shape}, 创建实例失败，错误信息:{result}")
                        break
                else:
                    result = self.wait_for_starting(instance_id=result.id)
                    if isinstance(result, OCIStatus):
                        self.log(
                            f"开机操作-第{self.create_counter(machine=instance_name):012d}次-{instance_terraform.shape},"
                            f"开机成功, 但是等待实例启动失败，错误信息:{result}")
                        break
                    public_ips = self.check_and_get_public_ips(instance_id=result.id, enable_ipv6=True)
                    if len(public_ips) == 0:
                        self.log(
                            f"开机操作-第{self.create_counter(machine=instance_name):012d}次-{instance_terraform.shape},"
                            f"开机成功, 但是没有找到公网IP, 机器状态`{result.lifecycle_state}`")
                        break
                    ip_str = " ".join([ip.pretty() for ip in public_ips])

                    allowed_ports = self.get_allowed_ports(instance_id=result.id)
                    allowed_ports_str = "tcp: `" + ", ".join(allowed_ports['tcp']) + "`, " + "udp: `" + ", ".join(
                        allowed_ports['udp']) + "`"

                    self.notify(f"开机操作-第{self.create_counter(machine=instance_name):012d}次-"
                                f"{instance_terraform.shape}, 开机成功, 机器IP: {ip_str}, 开放的端口: {allowed_ports_str}, "
                                f"机器状态`{result.lifecycle_state}`")
                    break
            except KeyboardInterrupt:
                self.log(f"开机操作-第{self.create_counter(machine=instance_name):012d}次-{instance_terraform.shape}, "
                         f"Received Ctrl+C. Shutting down...")
                break

    def allow_ports(self, instance_id, min_port, max_port, direction="INGRESS", protocol="ALL"):
        self.log(f"开启机器{instance_id}的{direction} {protocol} {min_port}-{max_port}")
        vcns = self.get_instance_vcns(instance_id)
        if isinstance(vcns, OCIStatus):
            self.log(
                f"开启机器{instance_id}的{direction} {protocol} {min_port}-{max_port}失败，没有找到机器的VCN: {vcns}")
            return
        for vcn in vcns:
            is_ipv6_enabled = vcn.ipv6_cidr_blocks is not None and len(vcn.ipv6_cidr_blocks) > 0
            self.allow_vcn_ports(vcn, min_port, max_port, direction=direction, protocol=protocol)
            if is_ipv6_enabled:
                self.allow_vcn_ports(vcn, min_port, max_port, is_ipv6=True, direction=direction, protocol=protocol)

    def allow_vcn_ports(self, vcn, min_port=None, max_port=None, is_ipv6=False, direction="INGRESS", protocol="ALL"):
        vcn_id = vcn.id
        vcn_name = vcn.display_name
        description = f"IPV{6 if is_ipv6 else 4} {direction} {protocol} port(s)"
        if min_port is None and max_port is not None:
            min_port = max_port
        if min_port is not None and max_port is None:
            max_port = min_port
        if min_port is not None and max_port is not None:
            description = f"{description} {min_port}-{max_port}"
        self.log(f"开启VCN-{vcn_name}的{description}")
        security_lists = self.get_vcn_security_list(vcn_id)
        if isinstance(security_lists, OCIStatus):
            self.log(
                f"开启VCN-{vcn_name}的{description}失败，没有找到机器的Security List: {security_lists}")
            return
        for security_list in security_lists:
            self.allow_security_list_ports(security_list.id, min_port, max_port, is_ipv6=is_ipv6, direction=direction,
                                           protocol=protocol)
        pass

    def allow_security_list_ports(self, security_list_id, min_port, max_port, is_ipv6=False, direction="INGRESS",
                                  protocol="ALL"):
        security_list = self.get_security_list(security_list_id)
        if is_failed(security_list):
            self.log(f"获取Security List-{security_list_id}失败, 错误信息:{security_list}")
            return
        security_list_name = security_list.display_name
        cidr_block = "0.0.0.0/0"
        if is_ipv6:
            cidr_block = "::/0"
        ingress_security_rules = []
        egress_security_rules = []
        if min_port is None and max_port is not None:
            min_port = max_port
        if min_port is not None and max_port is None:
            max_port = min_port

        description = f"IPV{6 if is_ipv6 else 4} {protocol} port {min_port}-{max_port}"
        if min_port is None and max_port is None:
            description = f"IPV{6 if is_ipv6 else 4} {protocol} ports"

        protocol_map = {"TCP": "6", "UDP": "17", "ICMP": "1", "ALL": "all"}

        self.log(f"开启Security List-{security_list_name}的{direction} {description}")

        if direction == "INGRESS":
            rule = IngressSecurityRule(protocol=protocol_map[protocol] if protocol in protocol_map else None,
                                       source_type="CIDR_BLOCK", source=cidr_block,
                                       description=f'Allow {description} by oci-arm')
            if protocol == "TCP" and min_port is not None and max_port is not None:
                rule.tcp_options = TcpOptions(destination_port_range=PortRange(min=min_port, max=max_port))
            if protocol == "UDP" and min_port is not None and max_port is not None:
                rule.udp_options = UdpOptions(destination_port_range=PortRange(min=min_port, max=max_port))
            ingress_security_rules.append(rule)
        else:
            rule = EgressSecurityRule(protocol=protocol_map[protocol] if protocol in protocol_map else None,
                                      destination_type="CIDR_BLOCK", destination=cidr_block,
                                      description=f'Allow {description} by oci-arm')
            if protocol == "TCP" and min_port is not None and max_port is not None:
                rule.tcp_options = TcpOptions(destination_port_range=PortRange(min=min_port, max=max_port))
            elif protocol == "UDP" and min_port is not None and max_port is not None:
                rule.udp_options = UdpOptions(destination_port_range=PortRange(min=min_port, max=max_port))
            egress_security_rules.append(rule)
        result = self.add_security_rule(security_list_id, ingress_security_rules, egress_security_rules)
        if is_failed(result):
            self.log(f"开启Security List-{security_list_name}的{direction} {protocol} {min_port}-{max_port}失败，"
                     f"错误信息:{result}")
        else:
            self.log(f"开启Security List-{security_list_name}的{direction} {protocol} {min_port}-{max_port}成功")

    def get_instance_vcns(self, instance_id) -> list[Vcn] | OCIStatus:
        vnics = self.list_vnics(instance_id)
        if isinstance(vnics, OCIStatus):
            return vnics
        vcns = []
        for vnic in vnics:
            subnet = self.get_subnet(vnic.subnet_id)
            if isinstance(subnet, OCIStatus):
                self.log(f"获取Subnet-{vnic.subnet_id}失败, 错误信息:{subnet}")
                continue
            vcn = self.get_vcn(subnet.vcn_id)
            if isinstance(vcn, OCIStatus):
                self.log(f"获取VCN-{subnet.vcn_id}失败, 错误信息:{vcn}")
                continue
            vcns.append(vcn)
        return vcns

    def get_vcn_security_list(self, vcn_id) -> list[SecurityList] | OCIStatus:
        try:
            return self.network_client.list_security_lists(compartment_id=self.compartment_id, vcn_id=vcn_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def get_security_list(self, security_list_id) -> SecurityList | OCIStatus:
        try:
            return self.network_client.get_security_list(security_list_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def add_security_rule(self, security_list_id, ingress_security_rules=None, egress_security_rules=None) -> OCIStatus:
        try:
            if (ingress_security_rules is None or len(ingress_security_rules) == 0) and (
                    egress_security_rules is None or len(egress_security_rules) == 0):
                return OCIStatus(http.client.BAD_REQUEST, "NoSecurityRules", "没有找到安全规则")
            security_list = self.get_security_list(security_list_id)
            if isinstance(security_list, OCIStatus):
                self.log(f"获取Security List-{security_list_id}失败, 错误信息:{security_list}")
                return security_list
            ingress_security_rules += security_list.ingress_security_rules
            egress_security_rules += security_list.egress_security_rules
            ingress_security_rules = list(cytoolz.unique(ingress_security_rules, key=lambda x: x.description))
            egress_security_rules = list(cytoolz.unique(egress_security_rules, key=lambda x: x.description))
            return self.network_client.update_security_list(security_list_id=security_list_id,
                                                            update_security_list_details=UpdateSecurityListDetails(
                                                                ingress_security_rules=ingress_security_rules,
                                                                egress_security_rules=egress_security_rules, )).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def get_allowed_ports(self, instance_id):
        allowed_tcp_ports = []
        allowed_udp_ports = []
        vcns = self.get_instance_vcns(instance_id)
        if isinstance(vcns, OCIStatus):
            self.log(f"获取机器{instance_id}的VCN失败, 错误信息:{vcns}")
            return
        for vcn in vcns:
            security_rules = self.list_security_rules(vcn.id)
            if isinstance(security_rules, OCIStatus):
                self.log(f"获取Subnet-{vcn.id}的Security Rules失败, 错误信息:{security_rules}")
                continue
            if security_rules is not None and len(security_rules) > 0:
                for rule in security_rules:
                    for ingress_rule in rule.ingress_security_rules:
                        if (ingress_rule.source_type == "CIDR_BLOCK" and (
                                ingress_rule.source == "0.0.0.0/0" or ingress_rule.source == "::/0")):
                            if ingress_rule.tcp_options is not None:
                                port_range = ingress_rule.tcp_options.destination_port_range
                                allowed_tcp_ports.append('{}-{}'.format(port_range.min, port_range.max))
                            elif ingress_rule.protocol == "all":
                                allowed_tcp_ports.append('{}-{}'.format(1, 65535))
                            if ingress_rule.udp_options is not None:
                                port_range = ingress_rule.udp_options.destination_port_range
                                allowed_udp_ports.append('{}-{}'.format(port_range.min, port_range.max))
                            elif ingress_rule.protocol == "all":
                                allowed_udp_ports.append('{}-{}'.format(1, 65535))
        allowed_ports = {'tcp': allowed_tcp_ports, 'udp': allowed_udp_ports}
        return allowed_ports

    def list_security_rules(self, vcn_id) -> list[SecurityList] | OCIStatus:
        try:
            return self.network_client.list_security_lists(compartment_id=self.compartment_id, vcn_id=vcn_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def list_vnics(self, instance_id) -> list[Vnic] | OCIStatus:
        vnic_attachments = self.list_vnic_attachments(instance_id)
        if isinstance(vnic_attachments, OCIStatus):
            return vnic_attachments

        vnics = []
        for vnic_attachment in vnic_attachments:
            vnic = self.get_vnic(vnic_attachment.vnic_id)
            if isinstance(vnic, OCIStatus):
                self.log(f"获取VNIC-{vnic_attachment.vnic_id}失败, 错误信息:{vnic}")
                continue
            vnics.append(vnic)
        return vnics

    def enable_instance_ipv6(self, instance_id):
        # get vnic
        instance = self.get_instance(instance_id)
        if isinstance(instance, OCIStatus):
            self.log(f"开启机器{instance_id}的IPv6失败，没有找到机器: {instance}")
            return
        self.log(f"开启机器{instance.display_name}的IPv6")
        vnics = self.list_vnics(instance_id)
        if isinstance(vnics, OCIStatus):
            self.log(f"开启机器{instance_id}的IPv6失败，没有找到机器的VNIC: {vnics}")
            return
        for vnic in vnics:
            self.enable_vnic_ipv6(vnic.id)

    def has_ipv6(self, vnic_id):
        return len(self.get_vnic_public_ip_v6(vnic_id)) > 0

    def get_vnic_vcn(self, vnic_id) -> Vcn | OCIStatus:
        vnic = self.get_vnic(vnic_id)
        if isinstance(vnic, OCIStatus):
            self.log(f"获取VNIC-{vnic_id}失败, 错误信息:{vnic}")
            return vnic
        subnet = self.get_subnet(vnic.subnet_id)
        if isinstance(subnet, OCIStatus):
            self.log(f"获取Subnet-{vnic.subnet_id}失败, 错误信息:{subnet}")
            return subnet
        vcn = self.get_vcn(subnet.vcn_id)
        if isinstance(vcn, OCIStatus):
            self.log(f"获取VCN-{subnet.vcn_id}失败, 错误信息:{vcn}")
            return vcn
        return vcn

    def enable_vnic_ipv6(self, vnic_id):
        if self.has_ipv6(vnic_id):
            self.log(f"VNIC-{vnic_id}已经开启IPv6, 检查是否开启了Subnet的IPv6")
            return
        vnic = self.get_vnic(vnic_id)
        if isinstance(vnic, OCIStatus):
            self.log(f"开启VNIC-{vnic_id}的IPv6失败，没有找到VNIC: {vnic}")
            return

        vnic_name = vnic.display_name
        vcn = self.get_vnic_vcn(vnic.id)
        if isinstance(vcn, OCIStatus):
            self.log(f"开启VNIC-{vnic_name}的IPv6失败，没有找到VNIC-{vnic_name}的VCN: {vcn}")
            return

        vcn_id = vcn.id
        vcn_name = vcn.display_name
        result = self.enable_vcn_ipv6(vcn_id, with_subnet=True)

        if isinstance(result, OCIStatus):
            self.log(f"开启VNIC-{vnic_name}的IPv6失败，开启VCN-{vcn_name}的IPV6: {result}")
            return

        result = self.add_ipv6_to_vnic(vnic.id)
        if isinstance(result, OCIStatus):
            self.log(f"开启VNIC-{vnic_name}的IPv6失败, {result}")
            return
        self.log(f"开启VNIC-{vnic_name}的IPv6成功, {result.ip_address}")

    def add_ipv6_to_vnic(self, vnic_id) -> Ipv6 | OCIStatus:
        try:
            return self.network_client.create_ipv6(oci.core.models.CreateIpv6Details(vnic_id=vnic_id)).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def add_ipv6_cidr_to_subnet(self, subnet_id, cidr_block=None) -> OCIStatus:
        try:
            self.network_client.add_ipv6_subnet_cidr(subnet_id=subnet_id,
                                                     add_subnet_ipv6_cidr_details=AddSubnetIpv6CidrDetails(
                                                         ipv6_cidr_block=cidr_block))
            return OCIStatus(http.client.OK, "Success", "Success")
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def enable_vcn_ipv6(self, vcn_id, with_subnet=True) -> Vcn | OCIStatus:
        vcn = self.get_vcn(vcn_id)
        if is_failed(vcn):
            self.log(f"开启IPv6失败，没有找到VCN-{vcn_id}: {vcn}")
            return vcn
        vcn_name = vcn.display_name
        if vcn.ipv6_cidr_blocks is not None and len(vcn.ipv6_cidr_blocks) > 0:
            if with_subnet:
                self.log(f"VCN-{vcn_name}已经开启IPv6: {vcn.ipv6_cidr_blocks[0]}，尝试开启Subnet的IPv6")
                self.check_and_enable_vcn_subnets_ipv6(vcn_id)
            else:
                self.log(f"VCN-{vcn_name}已经开启IPv6")
        else:
            self.log(f"没有找到VCN-{vcn_name}的ipv6_cidr_blocks, 尝试开启ipv6")
            result = self.add_ipv6_cidr_to_vcn(vcn_id)
            if isinstance(result, OCIStatus) and is_failed(result):
                self.log(f"开启VCN-{vcn_name}的IPv6失败，错误信息:{result}")
                return result
            self.log(f"开启VCN-{vcn_name}的IPv6成功")
        self.log(f"等待15s, 开始检测VCN-{vcn_name}的subnet")
        time.sleep(15)
        if with_subnet:
            self.log(f"开启VCN-{vcn_name}的Subnet的IPv6")
            self.check_and_enable_vcn_subnets_ipv6(vcn_id)
        self.log(f"等待15s, 开始检测VCN-{vcn_name}的security list")
        # refresh vcn
        vcn = self.get_vcn(vcn_id)
        if isinstance(vcn, OCIStatus):
            self.log(f"开启IPv6失败，没有找到VCN-{vcn_id}: {vcn}")
            return vcn
        self.check_route_and_security_rules(vcn)
        return self.get_vcn(vcn_id)

    def check_and_enable_vcn_subnets_ipv6(self, vcn_id):
        vcn = self.get_vcn(vcn_id)
        if isinstance(vcn, OCIStatus):
            self.log(f"开启VCN-{vcn_id}的IPv6失败，没有找到VCN-{vcn_id}: {vcn}")
            return
        vcn_name = vcn.display_name
        subnets = self.list_subnets(vcn_id)
        if isinstance(subnets, OCIStatus):
            self.log(f"开启VCN-{vcn_name}的Subnet的IPv6失败，没有找到Subnet: {subnets}")
            return
        if len(subnets) == 0:
            self.log(f"开启VCN-{vcn_name}的Subnet的IPv6，没有找到Subnet, 尝试创建Subnet")
            result = self.create_subnet(vcn_id=vcn_id)
            if isinstance(result, OCIStatus):
                self.log(f"开启VCN-{vcn_name}的Subnet的IPv6失败，创建Subnet失败: {result}")
                return
            subnets = [result]
        for subnet in subnets:
            if subnet.ipv6_cidr_blocks is not None and len(subnet.ipv6_cidr_blocks) > 0:
                self.log(f"Subnet-{subnet.display_name}已经开启IPv6:`{subnet.ipv6_cidr_blocks[0]}`, 跳过")
                continue
            vcn_cidr_block = vcn.ipv6_cidr_blocks[0]
            subnet_cidr_block = str(random_v6_subnet_cidr_block(vcn_cidr_block, 64))
            result = self.add_ipv6_cidr_to_subnet(subnet.id, cidr_block=subnet_cidr_block)
            if is_failed(result):
                self.log(f"开启VCN-{vcn_name}的Subnet的IPv6失败，添加IPv6 CIDR失败: {result}")
                continue
            self.log(f"开启VCN-{vcn_name}的Subnet-{subnet.display_name}的IPv6成功，添加IPv6 CIDR: {subnet_cidr_block}")

    def add_ipv6_cidr_to_vcn(self, vcn_id) -> OCIStatus:
        try:
            self.network_client.add_ipv6_vcn_cidr(vcn_id=vcn_id,
                                                  add_vcn_ipv6_cidr_details=AddVcnIpv6CidrDetails(
                                                      is_oracle_gua_allocation_enabled=True))
            return OCIStatus(http.client.OK, "Success", "Success")
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def default_vnic(self, instance_id) -> Vnic | OCIStatus:
        try:
            attachments = self.oci_client.list_vnic_attachments(compartment_id=self.oci_config.compartment_id,
                                                                instance_id=instance_id)
            data = attachments.data
            if len(data) != 0:
                vnic_id = data[0].vnic_id
                return self.network_client.get_vnic(vnic_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def wait_for_starting(self, instance_id, timeout=300) -> Instance | OCIStatus:
        start_time = time.time()
        count = 0
        instance_name = None
        while time.time() - start_time < timeout:
            result = self.get_instance(instance_id)
            if isinstance(result, OCIStatus):
                self.log(f"获取实例{instance_name}状态失败,第{count}次重试, 错误信息:{result}")
                count += 1
                time.sleep(5)
            if isinstance(result, Instance):
                if instance_name is None:
                    instance_name = result.display_name
                if result.lifecycle_state == "RUNNING":
                    return result
                elif result.lifecycle_state == "PROVISIONING" or result.lifecycle_state == "STARTING":
                    self.log(f"等待实例{instance_name}启动中，当前状态{result.lifecycle_state}, 第{count}次重试")
                    count += 1
                    time.sleep(5)
                else:
                    self.log(f"实例{instance_name}状态异常，当前状态{result.lifecycle_state}, 第{count}次重试")
                    return OCIStatus(http.client.BAD_REQUEST, "BadInstanceStatus", "实例状态异常")
        return OCIStatus(http.client.REQUEST_TIMEOUT, "RequestTimeout", "请求超时")

    def get_instance(self, instance_id) -> Instance | OCIStatus:
        try:
            return self.oci_client.get_instance(instance_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def check_and_get_public_ips(self, instance_id=None, enable_ipv6=False) -> list[IPAddress]:
        ips = self.get_public_ips(instance_id)
        need_enable_ipv6 = False
        for ip in ips:
            if enable_ipv6 and len(ip.v6s) == 0:
                need_enable_ipv6 = True
                break
        if need_enable_ipv6:
            self.enable_instance_ipv6(instance_id)

        return self.get_public_ips(instance_id)

    def get_primary_ipv4(self, instance_id) -> str | None:
        primary_vnic = self.get_primary_vnic(instance_id)
        if isinstance(primary_vnic, OCIStatus):
            self.log(f"获取实例{instance_id}的主网卡失败, 错误信息:{primary_vnic}")

        return primary_vnic.public_ip

    def get_primary_ipv6(self, instance_id) -> list[str]:
        primary_vnic = self.get_primary_vnic(instance_id)
        if isinstance(primary_vnic, OCIStatus):
            self.log(f"获取实例{instance_id}的主网卡失败, 错误信息:{primary_vnic}")

        return self.get_vnic_public_ip_v6(primary_vnic.id)

    def get_primary_vnic(self, instance_id) -> Vnic | OCIStatus:
        attachments = self.list_vnic_attachments(instance_id)
        if isinstance(attachments, OCIStatus):
            return attachments
        if len(attachments) == 0:
            return OCIStatus(http.client.NOT_FOUND, "NoVnicAttachment", "没有找到网卡")
        for attachment in attachments:
            vnic = self.get_vnic(attachment.vnic_id)
            if isinstance(vnic, OCIStatus):
                self.log(f"获取实例{instance_id}的网卡失败, 错误信息:{vnic}")
                continue
            if vnic.is_primary:
                return vnic
        return OCIStatus(http.client.NOT_FOUND, "NoPrimaryVnic", "没有找到主网卡")

    def change_instance_ip(self, instance_id, lifetime="EPHEMERAL"):
        vnics = self.list_vnics(instance_id)
        if isinstance(vnics, OCIStatus):
            self.log(f"获取实例{instance_id}的VNIC失败, 错误信息:{vnics}")
            return
        for vnic in vnics:
            self.change_vnic_ip_v4(vnic.id, lifetime=lifetime)

    def change_vnic_ip_v4(self, vnic_id, lifetime="EPHEMERAL"):
        vnic = self.get_vnic(vnic_id)
        if isinstance(vnic, OCIStatus):
            self.log(f"获取VNIC-{vnic_id}失败, 错误信息:{vnic}")
            return
        ip_info = self.get_public_ip_info(vnic.public_ip)
        private_ip_id = ip_info.private_ip_id if ip_info is not None else None
        if ip_info is None:
            self.log(f"没有找到公网IP信息-{vnic.display_name}, 开始新建IP")
            private_ip = self.get_private_ip_info(vnic_id, vnic.private_ip)
            if private_ip is None:
                self.log(f"没有找到私网IP信息-{vnic.display_name}, 请检查配置")
                return
            private_ip_id = private_ip.id
            self.log(f"开始创建新的公网IP, 网卡{vnic.display_name}, 私网IP: {private_ip.ip_address}")
        elif ip_info.lifetime == "EPHEMERAL":
            self.log(f"公网IP-{vnic.public_ip}是临时IP，删除并重新创建")
            result = self.delete_public_ip(ip_info.id)
            if is_failed(result):
                self.log(f"删除公网IP失败，错误信息:{result}")
                return
            self.log(f"删除公网IP成功")
        elif ip_info.lifetime == "RESERVED":
            self.log(f"公网IP-{vnic.public_ip}是保留IP，释放并重新创建")
            result = self.unassign_static_public_ip(ip_info.id)
            if is_failed(result):
                self.log(f"释放公网IP失败，错误信息:{result}")
                return
            self.log(f"释放公网IP成功")
        self.log(f"等待10s开始创建公网IP")
        time.sleep(10)
        self.log(f"开始创建公网IP")
        result = self.create_public_ip(lifetime=lifetime, private_ip_id=private_ip_id)
        if is_failed(result):
            if is_quota_exceeded(result) and lifetime == "RESERVED":
                self.log(f"分配保留IP失败, 超过了最大配额，尝试从已有的保留IP中获取")
                self.use_existing_reserved_public_ip(private_ip_id)
                return
            self.log(f"创建公网IP失败，错误信息:{result}")
            return
        self.log(f"创建公网IP成功, 新的公网IP: {result.ip_address}")

    def use_existing_reserved_public_ip(self, private_ip_id):
        result = self.list_reserved_public_ips()
        if isinstance(result, OCIStatus):
            self.log(f"获取保留IP失败，错误信息:{result}")
            return
        for ip in result:
            if ip.lifecycle_state == "AVAILABLE":
                self.log(f"找到可用的保留IP: {ip.ip_address}")
                result = self.assign_static_public_ip(ip.id, private_ip_id)
                if is_failed(result):
                    self.log(f"使用已有的公网IP失败，错误信息:{result}")
                    return
                self.log(f"使用已有的公网IP-{ip.ip_address}成功")

    def unassign_static_public_ip(self, public_ip_id):
        try:
            self.network_client.update_public_ip(public_ip_id=public_ip_id,
                                                 update_public_ip_details=oci.core.models.UpdatePublicIpDetails(
                                                     private_ip_id=""))
            return OCIStatus(http.client.OK, "Success", "Success")
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def assign_static_public_ip(self, public_ip_id, private_ip_id):
        try:
            self.network_client.update_public_ip(public_ip_id=public_ip_id,
                                                 update_public_ip_details=oci.core.models.UpdatePublicIpDetails(
                                                     private_ip_id=private_ip_id))
            return OCIStatus(http.client.OK, "Success", "Success")
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def delete_public_ip(self, public_ip_id=None) -> OCIStatus:
        try:
            self.network_client.delete_public_ip(public_ip_id=public_ip_id)
            return OCIStatus(http.client.OK, "Success", "Success")
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def create_public_ip(self, lifetime="EPHEMERAL", private_ip_id=None) -> PublicIp | OCIStatus:
        try:
            return self.network_client.create_public_ip(
                oci.core.models.CreatePublicIpDetails(compartment_id=self.oci_config.compartment_id, lifetime=lifetime,
                                                      private_ip_id=private_ip_id)).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def get_public_ip_info(self, ip_address):
        public_ips = self.list_public_ips()
        if isinstance(public_ips, OCIStatus):
            self.log(f"获取公网IP失败, 错误信息:{public_ips}")
            return None
        for public_ip in public_ips:
            if public_ip.ip_address == ip_address:
                return public_ip
        return None

    def get_private_ip_info(self, vnic_id, ip_address):
        private_ips = self.list_private_ips(vnic_id=vnic_id)
        if isinstance(private_ips, OCIStatus):
            self.log(f"获取私网IP失败, 错误信息:{private_ips}")
            return None
        for private_ip in private_ips:
            if private_ip.ip_address == ip_address:
                return private_ip
        return None

    def has_public_ip_v4(self, vnic_id) -> bool:
        return self.get_vnic_public_ip_v4(vnic_id) is not None

    def get_vnic_public_ip_v4(self, vnic_id) -> str:
        try:
            return self.network_client.get_vnic(vnic_id).data.public_ip
        except oci.exceptions.ServiceError as e:
            self.log(f"获取网卡{vnic_id}的公网IP失败, 错误信息:{OCIStatus(e.status, e.code, e.message)}")
            return ""

    def get_public_ips(self, instance_id) -> list[IPAddress]:
        public_ips = []
        attachments = self.list_vnic_attachments(instance_id=instance_id)
        if isinstance(attachments, OCIStatus):
            self.log(f"获取实例{instance_id}的公网IP失败, 错误信息:{attachments}")
            return public_ips
        for attachment in attachments:
            vnic_id = attachment.vnic_id
            vnic = self.get_vnic(vnic_id)
            if isinstance(vnic, OCIStatus):
                self.log(f"获取实例{instance_id}的公网IP失败, 获取网卡{vnic_id}信息失败, 错误信息:{vnic}")
                continue
            v4addr = vnic.public_ip
            ipv6s = self.get_vnic_public_ip_v6(vnic_id)
            public_ips.append(IPAddress(v4=v4addr, v6s=ipv6s))
        return public_ips

    def get_vnic_public_ip_v6(self, vnic_id) -> list[str]:
        try:
            ipv6s = self.network_client.list_ipv6s(vnic_id=vnic_id).data
            return [ipv6.ip_address for ipv6 in ipv6s]
        except oci.exceptions.ServiceError as e:
            self.log(f"获取网卡{vnic_id}的IPv6失败, 错误信息:{OCIStatus(e.status, e.code, e.message)}")
            return []

    def get_vnic(self, vnic_id) -> Vnic | OCIStatus:
        try:
            return self.network_client.get_vnic(vnic_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def list_vnic_attachments(self, instance_id=None):
        try:
            return self.oci_client.list_vnic_attachments(compartment_id=self.oci_config.compartment_id,
                                                         instance_id=instance_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def build_instance_terraform(self, shape='VM.Standard.A1.Flex', ocpus=None, memory_in_gbs=None, subnet_id=None,
                                 source_id=None, display_name=None, boot_volume_size_in_gbs=None,
                                 boot_volume_vpus_per_gb=None, ssh_authorized_keys=None, assign_public_ip=True):
        instance_terraform = TerraformParameter(None)
        shapes = self.list_shape_names()
        if shape not in shapes:
            self.fatal("机型不正确，请检查机型")
            return

        if subnet_id is None:
            subnet = self.default_subnet()
            subnet_id = subnet.id if isinstance(subnet, Subnet) else None

        if subnet_id is None:
            self.fatal("没有找到子网，请检查网络配置")
            return

        if source_id is None:
            source_id = self.default_ubuntu_image(shape).id

        if display_name is None:
            display_name = "{}-{}".format(shape, time.strftime("%Y%m%d%H%M%S", time.localtime()))
        display_name = display_name.replace(".", "-")

        if ocpus is None:
            if shape == "VM.Standard.A1.Flex":
                ocpus = 4
            else:
                ocpus = 1

        if memory_in_gbs is None:
            if shape == "VM.Standard.A1.Flex":
                memory_in_gbs = 24
            else:
                memory_in_gbs = 1

        if boot_volume_size_in_gbs is None:
            if shape == "VM.Standard.A1.Flex":
                boot_volume_size_in_gbs = 100.0
            else:
                boot_volume_size_in_gbs = 50.0

        if boot_volume_vpus_per_gb is None:
            boot_volume_vpus_per_gb = 120

        if ssh_authorized_keys is None:
            ssh_authorized_keys = generate_ssh_key()
        else:
            ssh_authorized_keys = SSHKey(private_key=None, passphrase=None, public_key=ssh_authorized_keys.strip())

        instance_terraform.shape = shape
        instance_terraform.ocpus = ocpus
        instance_terraform.memory_in_gbs = memory_in_gbs
        instance_terraform.subnet_id = subnet_id
        instance_terraform.source_id = source_id
        instance_terraform.display_name = display_name
        instance_terraform.boot_volume_size_in_gbs = boot_volume_size_in_gbs
        instance_terraform.boot_volume_vpus_per_gb = boot_volume_vpus_per_gb
        instance_terraform.ssh_authorized_keys = ssh_authorized_keys
        instance_terraform.assign_public_ip = assign_public_ip
        if self.oci_config is not None:
            instance_terraform.compartment_id = self.oci_config.compartment_id

        instance_terraform.availability_domain = self.default_availability_domain().name
        # check if the shape is valid
        return instance_terraform

    def create_instance(self, shape=None, terraform=None) -> Instance | OCIStatus:
        if shape is not None and terraform is None:
            terraform = self.build_instance_terraform(shape=shape,
                                                      ssh_authorized_keys=self.ssh_authorized_keys)
        if terraform is None:
            return OCIStatus(http.client.BAD_REQUEST, "NoInstanceTerraform", "没有找到实例配置")
        try:
            return self.oci_client.launch_instance(
                oci.core.models.LaunchInstanceDetails(display_name=terraform.display_name,
                                                      compartment_id=terraform.compartment_id,
                                                      shape=terraform.shape,
                                                      shape_config=oci.core.models.LaunchInstanceShapeConfigDetails(
                                                          ocpus=terraform.ocpus,
                                                          memory_in_gbs=terraform.memory_in_gbs),
                                                      availability_domain=terraform.availability_domain,
                                                      create_vnic_details=oci.core.models.CreateVnicDetails(
                                                          subnet_id=terraform.subnet_id,
                                                          hostname_label=terraform.hostname_label,
                                                          assign_public_ip=terraform.assign_public_ip),
                                                      source_details=oci.core.models.InstanceSourceViaImageDetails(
                                                          image_id=terraform.source_id,
                                                          boot_volume_size_in_gbs=terraform.boot_volume_size_in_gbs,
                                                          boot_volume_vpus_per_gb=terraform.boot_volume_vpus_per_gb),
                                                      metadata=dict(
                                                          ssh_authorized_keys=terraform.ssh_authorized_keys),
                                                      is_pv_encryption_in_transit_enabled=True, )).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def list_availability_domains(self):
        return self.identity_client.list_availability_domains(self.compartment_id).data

    def default_availability_domain(self):
        availability_domains = self.list_availability_domains()
        if len(availability_domains) == 0:
            return
        return availability_domains[0]

    def get_tenancy(self) -> Tenancy | OCIStatus:
        try:
            return self.identity_client.get_tenancy(self.compartment_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def list_subnets(self, vcn_id=None) -> list[Subnet] | OCIStatus:
        try:
            return self.network_client.list_subnets(self.compartment_id, vcn_id=vcn_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def has_subnet(self) -> bool:
        subnets = self.list_subnets()
        if isinstance(subnets, OCIStatus):
            return False
        return len(subnets) > 0

    def list_vcns(self) -> list[Vcn] | OCIStatus:
        try:
            return self.network_client.list_vcns(self.compartment_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def list_reserved_public_ips(self) -> list[PublicIp] | OCIStatus:
        try:
            return self.network_client.list_public_ips(scope="REGION", compartment_id=self.compartment_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def list_public_ips(self) -> list[PublicIp] | OCIStatus:
        try:
            ephemeral_ips = (self.network_client.
                             list_public_ips(scope="AVAILABILITY_DOMAIN",
                                             availability_domain=self.default_availability_domain().name,
                                             compartment_id=self.compartment_id).data)

            reserved_ips = self.network_client.list_public_ips(scope="REGION", compartment_id=self.compartment_id).data
            return ephemeral_ips + reserved_ips
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def list_private_ips(self, subnet_id=None, vnic_id=None) -> list[PrivateIp] | OCIStatus:
        try:
            return self.network_client.list_private_ips(subnet_id=subnet_id, vnic_id=vnic_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def has_vcn(self) -> bool:
        vcns = self.list_vcns()
        if isinstance(vcns, OCIStatus):
            return False
        return len(vcns) > 0

    def list_shapes(self) -> list[Shape] | OCIStatus:
        try:
            return self.oci_client.list_shapes(self.compartment_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def list_shape_names(self) -> list[str]:
        shapes = self.list_shapes()
        names = []
        if isinstance(shapes, OCIStatus):
            return names
        for shape in shapes:
            names.append(shape.shape)
        return names

    def list_images(self, shape=None, operating_system=None) -> list[Image] | OCIStatus:
        try:
            return self.oci_client.list_images(self.compartment_id, shape=shape, operating_system=operating_system).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def default_ubuntu_image(self, shape):
        images = self.list_images(shape=shape, operating_system="Canonical Ubuntu")
        if isinstance(images, OCIStatus):
            return None
        if len(images) == 0:
            return None
        return images[0]

    def get_subnet(self, subnet_id) -> Subnet | OCIStatus:
        try:
            return self.network_client.get_subnet(subnet_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def default_subnet(self) -> Subnet | OCIStatus:
        result = self.default_vcn()
        if isinstance(result, OCIStatus):
            return result
        listed = self.list_subnets(vcn_id=result.id)
        if isinstance(listed, OCIStatus):
            return listed
        if len(listed) > 0:
            return listed[0]
        self.log(f"没有找到VCN{result.display_name}的子网，开始创建子网")
        return self.create_subnet(result.id)

    def default_vcn(self) -> Vcn | OCIStatus:
        result = self.list_vcns()
        if isinstance(result, OCIStatus):
            return result
        if len(result) > 0:
            vcn = result[0]
        else:
            self.log(f"没有找到VCN，开始创建VCN")
            vcn = self.create_vcn()
            if isinstance(vcn, OCIStatus):
                self.log(f"创建VCN失败，错误信息:{vcn}")
        vcn_name = vcn.display_name
        self.log(f"创建VCN-{vcn_name}成功, 开始检查Subnet")
        subnets = self.list_subnets(vcn_id=vcn.id)
        if isinstance(subnets, OCIStatus):
            self.log(f"获取VCN-{vcn_name}的Subnet失败，错误信息:{subnets}")
            return vcn
        if len(subnets) == 0:
            self.log(f"没有找到VCN-{vcn_name}的Subnet，开始创建Subnet")
            subnet = self.create_subnet(vcn.id)
            if isinstance(subnet, OCIStatus):
                self.log(f"创建Subnet失败，错误信息:{subnet}")
            else:
                self.log(f"创建Subnet成功, subnet: {subnet.display_name}")
        else:
            self.log(f"VCN-{vcn_name}的Subnet已存在, subnet: {subnets[0].display_name}")
        return self.get_vcn(vcn.id)

    def check_route_and_security_rules(self, vcn, allow_traffic=True):
        self.log(f"等待15s, 检测并创建Internet Gateway")
        vcn_id = vcn.id
        internet_gateways = self.list_internet_gateways(vcn_id=vcn_id)
        if isinstance(internet_gateways, OCIStatus):
            self.log(f"获取Internet Gateway失败，错误信息:{internet_gateways}")
            return
        if len(internet_gateways) == 0:
            self.log(f"没有找到Internet Gateway，开始创建Internet Gateway")
            gateway = self.create_internet_gateway(vcn_id)
            if isinstance(gateway, OCIStatus):
                self.log(f"创建Internet Gateway失败，错误信息:{gateway}")
                return
            self.log(f"创建Internet Gateway[{gateway.display_name}]成功, 等待15s")
            internet_gateways = [gateway]
            time.sleep(15)
        for gateway in internet_gateways:
            self.check_route_table(vcn, gateway)
        if allow_traffic:
            self.allow_vcn_inbound_ports(vcn, min_port=1024, max_port=65535)
            self.allow_vcn_outbound(vcn)

    def allow_vcn_inbound_ports(self, vcn, min_port=1024, max_port=65535):
        self.log(f"开启VCN-{vcn.display_name}的安全规则，端口范围{min_port}-{max_port}")
        is_ipv6_enabled = vcn.ipv6_cidr_blocks is not None and len(vcn.ipv6_cidr_blocks) > 0
        self.allow_vcn_ports(vcn, min_port=min_port, max_port=max_port, protocol="TCP")  # TCP
        self.allow_vcn_ports(vcn, min_port=min_port, max_port=max_port, protocol="UDP")  # UDP
        if is_ipv6_enabled:
            self.allow_vcn_ports(vcn, min_port=min_port, max_port=max_port, is_ipv6=True, protocol="TCP")  # TCP
            self.allow_vcn_ports(vcn, min_port=min_port, max_port=max_port, is_ipv6=True, protocol="UDP")  # UDP

    def allow_vcn_outbound(self, vcn):
        self.log(f"开启VCN-{vcn.display_name}的安全规则，允许所有出站流量")
        is_ipv6_enabled = vcn.ipv6_cidr_blocks is not None and len(vcn.ipv6_cidr_blocks) > 0
        self.allow_vcn_ports(vcn, direction="EGRESS")
        if is_ipv6_enabled:
            self.allow_vcn_ports(vcn, direction="EGRESS", is_ipv6=True)

    def check_route_table(self, vcn, gateway):
        self.log(f"检测Route Table是否存在")
        route_table_id = vcn.default_route_table_id
        is_ipv6_enabled = vcn.ipv6_cidr_blocks is not None and len(vcn.ipv6_cidr_blocks) > 0
        if route_table_id is None:
            self.log(f"没有找到Route Table，开始创建Route Table")
            route_table = self.create_route_table(vcn.id, with_ipv6=is_ipv6_enabled, internet_gateway_id=gateway.id)
            if isinstance(route_table, OCIStatus):
                self.log(f"创建Route Table失败，错误信息:{route_table}")
                return
            self.log(f"创建Route Table[{route_table.display_name}]成功")
            route_table_id = route_table.id
        route_table = self.get_route_table(route_table_id)
        if isinstance(route_table, OCIStatus):
            self.log(f"获取Route Table失败，错误信息:{route_table}")
            return
        self.log(f"检测Route Table[{route_table.display_name}]的路由规则")
        has_v4_route = False
        has_v6_route = False
        if len(route_table.route_rules) > 0:
            for rule in route_table.route_rules:
                if rule.destination == "0.0.0.0/0":
                    has_v4_route = True
                if rule.destination == "::/0":
                    has_v6_route = True
        if not has_v4_route:
            self.log(f"没有找到IPv4的路由规则，开始创建IPv4的路由规则")
            result = self.create_route_rule(route_table_id, gateway.id, "0.0.0.0/0")
            if isinstance(result, OCIStatus):
                self.log(f"创建IPv4的路由规则失败，错误信息:{result}")
            else:
                self.log(f"创建IPv4的路由规则成功")
        else:
            self.log(f"IPV4的路由规则已存在")
        if not has_v6_route and is_ipv6_enabled:
            self.log(f"没有找到IPv6的路由规则，开始创建IPv6的路由规则")
            result = self.create_route_rule(route_table_id, gateway.id, "::/0")
            if isinstance(result, OCIStatus):
                self.log(f"创建IPv6的路由规则失败，错误信息:{result}")
            else:
                self.log(f"创建IPv6的路由规则成功")
        else:
            self.log(f"IPV6的路由规则已存在")

    def create_route_table(self, vcn_id, with_ipv6=False, internet_gateway_id=None) -> RouteTable | OCIStatus:
        try:
            route_rules = None
            if internet_gateway_id is not None:
                route_rules = [
                    RouteRule(destination="0.0.0.0/0", destination_type="CIDR_BLOCK", cidr_block="0.0.0.0/0/",
                              network_entity_id=internet_gateway_id, route_type="STATIC")]
                if with_ipv6:
                    route_rules.append(RouteRule(destination="::/0", destination_type="CIDR_BLOCK", cidr_block="::/0",
                                                 network_entity_id=internet_gateway_id, route_type="STATIC"))
            return self.network_client.create_route_table(
                oci.core.models.CreateRouteTableDetails(compartment_id=self.compartment_id, vcn_id=vcn_id,
                                                        display_name=f"{self.name()}-route-table",
                                                        route_rules=route_rules)).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def create_route_rule(self, route_table_id, network_entity_id, cidr_block) -> RouteTable | OCIStatus:
        try:
            route_table = self.get_route_table(route_table_id)
            if isinstance(route_table, OCIStatus):
                self.log(f"获取Route Table-{route_table_id}失败，错误信息:{route_table}")
                return route_table
            route_rules = route_table.route_rules
            route_rules.append(
                RouteRule(destination=cidr_block, destination_type="CIDR_BLOCK", network_entity_id=network_entity_id,
                          route_type="STATIC"))
            return self.network_client.update_route_table(rt_id=route_table_id,
                                                          update_route_table_details=UpdateRouteTableDetails(
                                                              route_rules=route_rules)).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def create_internet_gateway(self, vcn_id, route_table_id=None) -> InternetGateway | OCIStatus:
        try:
            return self.network_client.create_internet_gateway(
                oci.core.models.CreateInternetGatewayDetails(compartment_id=self.compartment_id, vcn_id=vcn_id,
                                                             route_table_id=route_table_id, is_enabled=True,
                                                             display_name=f"{self.name()}-internet-gateway", )).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def create_vcn(self, enable_ipv6=False) -> Vcn | OCIStatus:
        try:
            return self.network_client.create_vcn(
                create_vcn_details=oci.core.models.CreateVcnDetails(cidr_block="10.0.0.0/24",
                                                                    is_ipv6_enabled=enable_ipv6,
                                                                    compartment_id=self.compartment_id,
                                                                    display_name=f"{self.name()}-vcn", )).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def get_vcn(self, vcn_id) -> Vcn | OCIStatus:
        try:
            return self.network_client.get_vcn(vcn_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def get_route_table(self, route_table_id) -> RouteTable | OCIStatus:
        try:
            return self.network_client.get_route_table(rt_id=route_table_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def get_internet_gateway(self, internet_gateway_id) -> InternetGateway | OCIStatus:
        try:
            return self.network_client.get_internet_gateway(internet_gateway_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def list_internet_gateways(self, vcn_id=None) -> list[InternetGateway] | OCIStatus:
        try:
            return self.network_client.list_internet_gateways(compartment_id=self.compartment_id, vcn_id=vcn_id).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def get_vcn_internet_gateways(self, vcn_id):
        gateways = self.list_internet_gateways(vcn_id=vcn_id)
        if isinstance(gateways, OCIStatus):
            self.log(f"获取VCN{vcn_id}的Internet Gateway失败, 错误信息:{gateways}")
            return []
        return gateways

    def has_internet_gateway(self, vcn_id) -> bool:
        return len(self.get_vcn_internet_gateways(vcn_id)) > 0

    def create_subnet(self, vcn_id, is_ipv6_enabled=True) -> Subnet | OCIStatus:
        try:
            ipv6_cidr_block = None
            if is_ipv6_enabled:
                vcn = self.get_vcn(vcn_id)
                if isinstance(vcn, Vcn) and vcn.ipv6_cidr_blocks is not None and len(vcn.ipv6_cidr_blocks) > 0:
                    # 2603:c026:4501:9700::/56 create a subnet with /64
                    ipv6_cidr_block = vcn.ipv6_cidr_blocks[0].replace("/56", "/64")
            return self.network_client.create_subnet(
                create_subnet_details=oci.core.models.CreateSubnetDetails(compartment_id=self.compartment_id,
                                                                          display_name=f"{self.name()}-subnet",
                                                                          vcn_id=vcn_id, cidr_block="10.0.0.0/24",
                                                                          ipv6_cidr_block=ipv6_cidr_block, )).data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def list_instances(self, status=None) -> list[Instance] | OCIStatus:
        match_instances = []

        try:
            instances = self.oci_client.list_instances(self.compartment_id).data
            for instance in instances:
                if status is None or instance.lifecycle_state == status:
                    match_instances.append(instance)
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)
        return match_instances

    def list_stopped_instances(self) -> list[Instance] | OCIStatus:
        return self.list_instances(status="STOPPED")

    def start_instance(self, instance_id) -> Instance | OCIStatus:
        try:
            return self.oci_client.instance_action(instance_id, "START").data
        except oci.exceptions.ServiceError as e:
            return OCIStatus(e.status, e.code, e.message)

    def start_instance_task(self, instance):
        instance_id = instance.id
        instance_name = instance.display_name

        message = f"`{self.name()}` 开始启动实例:`{instance_name}` - `{self.get_primary_ipv4(instance_id)}`"
        self.notify(message)
        while not self.exiting.is_set():
            try:
                result = self.start_instance(instance_id)
                self.increase_start_counter(machine=instance_name)
                if isinstance(result, OCIStatus):
                    if is_rate_limit(result):
                        # 被限速了，改一下时间
                        if self.wait_time < 60:
                            self.wait_time += 2
                        self.log(f"启动实例-第{self.start_counter(machine=instance_name):012d}次-`{instance_name}`: "
                                 f"请求太快了，自动调整请求时间为{self.wait_time}s")
                        time.sleep(self.wait_time)
                    elif is_out_of_host_capacity(result):
                        # 没有被限速，恢复减少的时间
                        if self.wait_time > 15:
                            self.wait_time -= 10
                        self.log(f"启动实例-第{self.start_counter(machine=instance_name):012d}次-`{instance_name}`: "
                                 f"{result.message}，目前没有请求限速,快马加刷中，当前请求间隔{self.wait_time}s")
                        time.sleep(self.wait_time)
                    else:
                        self.log(f"启动实例-第{self.start_counter(machine=instance_name):012d}次-`{instance_name}`: "
                                 f"操作失败，错误信息:{result}")
                        break
                else:
                    result = cli.wait_for_starting(instance_id=instance_id)
                    if isinstance(result, OCIStatus):
                        self.log(f"启动实例-第{self.start_counter(machine=instance_name):012d}次-`{instance_name}`: "
                                 f"等待启动失败，错误信息:{result}, 继续等待")
                        continue
                    message = (f"`{self.name()}` 启动实例-第{self.start_counter(machine=instance_name):012d}次-`"
                               f"{instance_name}`: 操作成功, 机器状态`{result.lifecycle_state}`")
                    self.notify(message)
                    break
            except KeyboardInterrupt:
                self.log(f"启动实例-第{self.start_counter(machine=instance_name):012d}次-`{instance_name}`: "
                         f"Received Ctrl+C. Shutting down...")
                break

    def create(self, shapes=None, skip_amd=False):
        if shapes is None:
            shapes = [
                {
                    'shape': 'VM.Standard.A1.Flex',
                    'ocpus': 4,
                    'memory_in_gbs': 24,
                    'boot_volume_size_in_gbs': 100.0,
                },
                {
                    'shape': 'VM.Standard.E2.1.Micro',
                    'ocpus': 1,
                    'memory_in_gbs': 1,
                    'boot_volume_size_in_gbs': 50.0,
                },
                {
                    'shape': 'VM.Standard.E2.1.Micro',
                    'ocpus': 1,
                    'memory_in_gbs': 1,
                    'boot_volume_size_in_gbs': 50.0,
                },
            ]
        for shape in shapes:
            if skip_amd and shape['shape'] == 'VM.Standard.E2.1.Micro':
                continue
            instance_terraform = self.build_instance_terraform(**shape, ssh_authorized_keys=self.ssh_authorized_keys)
            self.submit(self.create_instance_task, instance_terraform=instance_terraform)

    def start(self):
        result = self.list_stopped_instances()
        if isinstance(result, OCIStatus):
            self.telegram(f"启动实例-{self.name()}, 获取已经停止的实例失败，错误信息:{result}")
            return
        if len(result) == 0:
            self.telegram(f"启动实例-{self.name()}, 没有找到已经停止的实例")
            return
        # start threads for each instance to start until all started
        for instance in result:
            self.submit(self.start_instance_task, instance)

    def submit(self, fn, *args, **kwargs):
        try:
            self.pool().submit(fn, *args, **kwargs)
        except KeyboardInterrupt:
            self.log(f"Received Ctrl+C. Shutting down...")


def all_profiles(oci_config_file="~/.oci/config"):
    _profiles = []
    with open(oci_config_file) as ocf:
        parser = ConfigParser()
        parser.read_file(ocf)
        for section in parser.sections():
            _profiles.append(section)
    if len(_profiles) == 0:
        _profiles.append("DEFAULT")
    return _profiles


def parse_arguments():
    parser = argparse.ArgumentParser(description='Oracle CLI helper')

    parser.add_argument('--operation', '-o', '-op', choices=['create', 'start'],
                        help='Choose operation: create or start')
    parser.add_argument('--tf-filepath', '--tf', '-t', dest='tf_file', help='Terraform file path (main.tf)',
                        required=False)
    parser.add_argument('--config-file', '--config', '-c', dest='config_file', help='Config file path', required=True)
    parser.add_argument('--profile', '-p', dest='profile', help='Choose profile')
    parser.add_argument('--telegram-bot-token', '-tt', dest='telegram_bot_token', help='Telegram bot token')
    parser.add_argument('--telegram-user-id', '-tu', nargs='+', dest='telegram_user_id', help='Telegram user id')
    parser.add_argument('--telegram-api-host', '-th', dest='telegram_api_host', help='Telegram api host')
    parser.add_argument('--log-file', '-l', dest='log_file', help='Log file path')
    parser.add_argument('--ssh-authorized-keys', '-k', dest='ssh_authorized_keys', help='SSH authorized keys')
    cli_args = parser.parse_args()

    if cli_args.telegram_user_id is not None and cli_args.telegram_bot_token is None:
        # should ask for telegram token
        print("Telegram bot token is required to send message")
        exit(0)

    return cli_args


def start_client(oci_client, oci_operation=None):
    try:
        if operation is None:
            logger.info(f"开始操作: 没有指定操作，执行创建和启动")
            oci_client.create(skip_amd=True)
            oci_client.start()
        elif oci_operation == "create":
            oci_client.create(skip_amd=True)
        elif oci_operation == "start":
            oci_client.start()
        else:
            logger.info(f"不支持的操作{operation}")
            return
    except KeyboardInterrupt:
        logger.info("Received Ctrl+C. Shutting down...")
        return


if __name__ == "__main__":
    cmd_args = parse_arguments()

    if cmd_args.log_file is not None:
        logger.add(cmd_args.log_file, rotation="1day", retention="7 days", level="DEBUG", compression="gz")

    ssh_authorize_keys = cmd_args.ssh_authorized_keys
    if ssh_authorize_keys is not None and os.path.exists(ssh_authorize_keys):
        with open(ssh_authorize_keys) as f:
            ssh_authorize_keys = f.read().strip()

    if ssh_authorize_keys is not None and not ssh_authorize_keys.startswith("ssh-rsa"):
        logger.info(f"ssh-authorized-keys文件格式不正确")
        ssh_authorize_keys = None

    # Accessing the parsed arguments
    tf_file = cmd_args.tf_file
    operation = cmd_args.operation
    profile = cmd_args.profile
    config_file = cmd_args.config_file
    telegram_bot_token = cmd_args.telegram_bot_token
    telegram_user_id = cmd_args.telegram_user_id
    bot = None
    if telegram_bot_token is not None:
        bot = TelegramBot(token=telegram_bot_token)
        if telegram_user_id is not None:
            for user_id in telegram_user_id:
                bot.add_user(user_id)

    clients = {}
    profiles = all_profiles(oci_config_file=os.path.abspath(config_file))
    tp = ThreadPoolExecutor(max_workers=3 * len(profiles))

    ev = threading.Event()


    def signal_handler(signum, _):
        logger.info("Received signal %s, shutting down...", signum)
        ev.set()


    signal.signal(signal.SIGTERM, signal_handler)

    for profile in profiles:
        client = OCIClient(oci_config_file=os.path.abspath(config_file), oci_profile=profile,
                           ssh_authorized_keys=ssh_authorize_keys, tf_filepath=tf_file, telegram_bot=bot,
                           thread_pool=tp, exiting=ev)
        clients[client.name()] = client

    for _, cli in clients.items():
        logger.info(f"开始操作: {cli.name()}")
        start_client(cli, operation)

    try:
        while not ev.is_set():
            time.sleep(1)
    except KeyboardInterrupt:
        logger.info("Received Ctrl+C. Shutting down...")
        ev.set()

#!/usr/bin/env python3
__author__ = 'mysqto'
__version__ = '0.1.0'
__description__ = 'Oracle Cloud Infrastructure ARM'
__url__ = 'https://github.com/mysqto/oracle'
__license__ = 'MIT'
__email__ = 'my@mysq.to'

import argparse
import asyncio
import http.client
import ipaddress
import itertools
import json
import multiprocessing
import os
import os.path
import random
import re
import shutil
import signal
import socket
import string
import subprocess
import tempfile
import threading
import time
import uuid
from concurrent.futures import ThreadPoolExecutor, as_completed
from configparser import ConfigParser
from datetime import datetime
from typing import Callable

import cytoolz
import psutil
import requests
from CloudFlare import CloudFlare
from cpuinfo import cpuinfo
from loguru import logger
from oci import signer
from oci.config import validate_config, from_file
from oci.core import ComputeClient, VirtualNetworkClient, BlockstorageClient
from oci.core.models import Instance, Subnet, Shape, Image, Vcn, Vnic, Ipv6, PublicIp, PrivateIp, SecurityList, \
    UpdateSecurityListDetails, IngressSecurityRule, TcpOptions, PortRange, UdpOptions, EgressSecurityRule, RouteTable, \
    InternetGateway, RouteRule, AddSubnetIpv6CidrDetails, AddVcnIpv6CidrDetails, UpdateRouteTableDetails, \
    UpdateInstanceDetails, UpdateInstanceShapeConfigDetails, BootVolumeAttachment, BootVolume, \
    CreateBootVolumeDetails, BootVolumeSourceFromBootVolumeDetails, Volume, CreateVolumeDetails, \
    InstanceSourceViaImageDetails, CreateVnicDetails, LaunchInstanceShapeConfigDetails, LaunchInstanceDetails, \
    CreateRouteTableDetails, CreateInternetGatewayDetails, CreateVcnDetails, CreateSubnetDetails, CreateIpv6Details, \
    UpdatePublicIpDetails, CreatePublicIpDetails, VolumeAttachment, UpdateBootVolumeDetails, \
    AttachParavirtualizedVolumeDetails, IcmpOptions, CreateSecurityListDetails, CreateInstanceConsoleConnectionDetails
from oci.database.models import ConsoleConnection
from oci.exceptions import InvalidPrivateKey, MissingPrivateKeyPassphrase, ServiceError
from oci.identity import IdentityClient
from oci.identity.models import Tenancy, Region
from oci.limits import LimitsClient
from oci.limits.models import LimitValueSummary, ServiceSummary
from oci.object_storage import ObjectStorageClient
from oci.object_storage.models import CreateBucketDetails, Bucket
from oci.util import to_dict
from telegram import Update, User
from telegram.constants import ParseMode, ChatType
from telegram.ext import ApplicationBuilder, ContextTypes, CommandHandler, MessageHandler, filters, \
    ConversationHandler, PicklePersistence, ApplicationHandlerStop, TypeHandler
from telegram.helpers import escape_markdown

iso_3166_1 = {
    # see: https://www.iso.org/iso-3166-country-codes.html
    "AF": True, "AX": True, "AL": True, "DZ": True, "AS": True,
    "AD": True, "AO": True, "AI": True, "AQ": True, "AG": True,
    "AR": True, "AM": True, "AW": True, "AU": True, "AT": True,
    "AZ": True, "BS": True, "BH": True, "BD": True, "BB": True,
    "BY": True, "BE": True, "BZ": True, "BJ": True, "BM": True,
    "BT": True, "BO": True, "BQ": True, "BA": True, "BW": True,
    "BV": True, "BR": True, "IO": True, "BN": True, "BG": True,
    "BF": True, "BI": True, "KH": True, "CM": True, "CA": True,
    "CV": True, "KY": True, "CF": True, "TD": True, "CL": True,
    "CN": True, "CX": True, "CC": True, "CO": True, "KM": True,
    "CG": True, "CD": True, "CK": True, "CR": True, "CI": True,
    "HR": True, "CU": True, "CW": True, "CY": True, "CZ": True,
    "DK": True, "DJ": True, "DM": True, "DO": True, "EC": True,
    "EG": True, "SV": True, "GQ": True, "ER": True, "EE": True,
    "ET": True, "FK": True, "FO": True, "FJ": True, "FI": True,
    "FR": True, "GF": True, "PF": True, "TF": True, "GA": True,
    "GM": True, "GE": True, "DE": True, "GH": True, "GI": True,
    "GR": True, "GL": True, "GD": True, "GP": True, "GU": True,
    "GT": True, "GG": True, "GN": True, "GW": True, "GY": True,
    "HT": True, "HM": True, "VA": True, "HN": True, "HK": True,
    "HU": True, "IS": True, "IN": True, "ID": True, "IR": True,
    "IQ": True, "IE": True, "IM": True, "IL": True, "IT": True,
    "JM": True, "JP": True, "JE": True, "JO": True, "KZ": True,
    "KE": True, "KI": True, "KP": True, "KR": True, "KW": True,
    "KG": True, "LA": True, "LV": True, "LB": True, "LS": True,
    "LR": True, "LY": True, "LI": True, "LT": True, "LU": True,
    "MO": True, "MK": True, "MG": True, "MW": True, "MY": True,
    "MV": True, "ML": True, "MT": True, "MH": True, "MQ": True,
    "MR": True, "MU": True, "YT": True, "MX": True, "FM": True,
    "MD": True, "MC": True, "MN": True, "ME": True, "MS": True,
    "MA": True, "MZ": True, "MM": True, "NA": True, "NR": True,
    "NP": True, "NL": True, "NC": True, "NZ": True, "NI": True,
    "NE": True, "NG": True, "NU": True, "NF": True, "MP": True,
    "NO": True, "OM": True, "PK": True, "PW": True, "PS": True,
    "PA": True, "PG": True, "PY": True, "PE": True, "PH": True,
    "PN": True, "PL": True, "PT": True, "PR": True, "QA": True,
    "RE": True, "RO": True, "RU": True, "RW": True, "BL": True,
    "SH": True, "KN": True, "LC": True, "MF": True, "PM": True,
    "VC": True, "WS": True, "SM": True, "ST": True, "SA": True,
    "SN": True, "RS": True, "SC": True, "SL": True, "SG": True,
    "SX": True, "SK": True, "SI": True, "SB": True, "SO": True,
    "ZA": True, "GS": True, "SS": True, "ES": True, "LK": True,
    "SD": True, "SR": True, "SJ": True, "SZ": True, "SE": True,
    "CH": True, "SY": True, "TW": True, "TJ": True, "TZ": True,
    "TH": True, "TL": True, "TG": True, "TK": True, "TO": True,
    "TT": True, "TN": True, "TR": True, "TM": True, "TC": True,
    "TV": True, "UG": True, "UA": True, "AE": True, "GB": True,
    "US": True, "UM": True, "UY": True, "UZ": True, "VU": True,
    "VE": True, "VN": True, "VG": True, "VI": True, "WF": True,
    "EH": True, "YE": True, "ZM": True, "ZW": True, "XK": True,
}


def is_country_code(s: str) -> bool:
    return s.upper() in iso_3166_1


def in_country(region: dict, country_code: str) -> bool:
    if region is None:
        return False
    return region['country_code'] == country_code.upper()


__base_dir__ = ".oci"

skip_prefixes = [
    '-----BEGIN PRIVATE KEY-----',
    '-----BEGIN ENCRYPTED PRIVATE KEY-----'
]

skip_suffixes = [
    '-----END PRIVATE KEY-----',
    '-----END ENCRYPTED PRIVATE KEY-----'
]


def uptime():
    boot_time = psutil.boot_time()
    system_uptime = int(time.time()) - int(boot_time)

    days = system_uptime // (24 * 3600)
    system_uptime = system_uptime % (24 * 3600)
    hours = system_uptime // 3600
    system_uptime %= 3600
    minutes = system_uptime // 60
    system_uptime %= 60
    seconds = system_uptime
    days_text = "days" if days > 1 else "day"

    if days > 0:
        return '%d %s %02d:%02d:%02d' % (days, days_text, hours, minutes, seconds)
    else:
        return '%02d:%02d:%02d' % (hours, minutes, seconds)


def readable_speed(n):
    return f'{readable_bytes(n)}/s'


_symbols = ('B', 'KB', 'MB', 'GB', 'TB', 'PB', 'EB', 'ZB', 'YB')


def readable_bytes(n, fmt="%(value).1f%(symbol)s"):
    prefix = {}
    for i, s in enumerate(_symbols[1:]):
        prefix[s] = 1 << (i + 1) * 10
    for symbol in reversed(_symbols[1:]):
        if abs(n) >= prefix[symbol]:
            value = float(n) / prefix[symbol]
            return fmt % locals()
    return fmt % dict(symbol=_symbols[0], value=n)


def readable_size(n, base_unit='B', fmt="%(value).1f%(symbol)s"):
    base_unit = base_unit.upper()
    if base_unit not in _symbols:
        raise ValueError(f"base_unit {base_unit} is not supported")

    index = _symbols.index(base_unit)
    return readable_bytes(n * (1024 ** index), fmt)


async def ping(host, ipv6=False, count=8, markdown=True) -> str:
    ipv6 = validate_ipv6_address(host) or ipv6
    # check macOS or Linux
    uname = os.uname().sysname
    if uname == 'Linux':
        cmd = 'ping6' if ipv6 else 'ping4'
    else:
        cmd = 'ping6' if ipv6 else 'ping'

    # use subprocess to ping and capture the output and redirect to stdout
    result = subprocess.run([cmd, '-c', str(count), host],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if markdown:
        icon = '✅️' if result.returncode == 0 else '❗'
        return f'{icon} `{host}`\n```bash\n{result.stdout.decode("utf-8")}\n```'
    result.stdout.decode('utf-8')


FLAGS_OFFSET = 127397
A = 65
Z = 90


def emoji(country):
    first = ord(country[0])
    second = ord(country[1])

    if (len(country) != 2) or (first > Z or first < A) or (second > Z or second < A):
        return country

    return chr(first + FLAGS_OFFSET) + chr(second + FLAGS_OFFSET)


def redact(s: str) -> str:
    if s.startswith('/'):
        return s
    # remove all spaces and new lines
    for prefix in skip_prefixes:
        if s.startswith(prefix):
            s = s[len(prefix):]
            break
    for suffix in skip_suffixes:
        if s.endswith(suffix):
            s = s[:-len(suffix)]
            break
    s = re.sub(r'\s+', '', s).strip()
    if len(s) < 3:
        return s
    # mask the middle and expose the first and last 3 chars
    if len(s) == 3:
        return s[0] + '*' * 8 + s[2]
    if len(s) == 4:
        return s[0:2] + '*' * 7 + s[3]
    if len(s) == 5:
        return s[0:2] + '*' * 6 + s[-2:]
    if len(s) == 6:
        return s[0:2] + '*' * 6 + s[-2:]
    return s[0:3] + '*' * 4 + s[-3:]


def snake_to_camel(s: str) -> str:
    return ''.join(word.title() for word in s.split('_'))


def _sorted(data: dict) -> dict:
    for k, v in data.items():
        if type(v) is dict:
            data[k] = _sorted(v)
    return {k: data[k] for k in sorted(data)}


def unique_security_rules(rules: list[IngressSecurityRule | EgressSecurityRule]) \
        -> list[IngressSecurityRule | EgressSecurityRule]:
    if rules is None or len(rules) == 0:
        return []

    # unique with security_rule_equal
    return list(filter(lambda x: not any(security_rule_equal(x, y) for y in rules[:rules.index(x)]), rules))


def fix(p: PortRange) -> PortRange:
    if p.min is None and p.max is not None:
        p.min = p.max
    if p.max is None and p.min is not None:
        p.max = p.min
    return p


def port_range_equal(p1: PortRange, p2: PortRange) -> bool:
    if p1 is None and p2 is None:
        return True
    if p1 is None or p2 is None:
        return False
    p1 = fix(p1)
    p2 = fix(p2)
    return p1.min == p2.min and p1.max == p2.max


def icmp_options_equal(o1: IcmpOptions, o2: IcmpOptions) -> bool:
    if o1 is None and o2 is None:
        return True
    if o1 is None or o2 is None:
        return False

    return o1.code == o2.code and o1.type == o2.type


def options_equal(o1: TcpOptions | UdpOptions, o2: TcpOptions | UdpOptions) -> bool:
    if o1 is None and o2 is None:
        return True
    if o1 is None or o2 is None:
        return False
    return port_range_equal(o1.destination_port_range, o2.destination_port_range) and \
        port_range_equal(o1.source_port_range, o2.source_port_range)


def bool_equal(b1: bool, b2: bool) -> bool:
    b1 = False if b1 is None else b1
    b2 = False if b2 is None else b2
    return b1 == b2


def security_rule_equal(r1: IngressSecurityRule | EgressSecurityRule,
                        r2: IngressSecurityRule | EgressSecurityRule) -> bool:
    if type(r1) is not type(r2):
        return False
    return r1.protocol == r2.protocol and \
        options_equal(r1.tcp_options, r2.tcp_options) and \
        options_equal(r1.udp_options, r2.udp_options) and \
        icmp_options_equal(r1.icmp_options, r2.icmp_options) and \
        bool_equal(r1.is_stateless, r2.is_stateless) and \
        ((r1.source == r2.source and r1.source_type == r2.source_type) if isinstance(r1, IngressSecurityRule)
         else (r1.description == r2.description and r1.destination_type == r2.destination_type))


class Status:
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


def random_v6_subnet_cidr_block(base_cidr, subnet_cidr_block_size=64):
    base_network = ipaddress.IPv6Network(base_cidr)
    random_fill_bits = subnet_cidr_block_size - base_network.prefixlen
    random_bits = random.getrandbits(random_fill_bits)
    random_cidr_suffix = random_bits << subnet_cidr_block_size
    return ipaddress.IPv6Network((base_network.network_address + random_cidr_suffix, subnet_cidr_block_size))


def validate_ip_address(ip: str) -> bool:
    try:
        _ = ipaddress.ip_address(ip)
        return True
    except ValueError:
        return False


def validate_ipv6_address(ip: str) -> bool:
    try:
        ipaddress.IPv6Address(ip)
        return True
    except ValueError:
        return False


def filter_cf_records(records: list[dict], record_filters: list[str]) -> list[dict]:
    if records is None or len(records) == 0:
        return []

    if record_filters is None or len(record_filters) == 0:
        return records

    def match(r, rfs: list[str]):
        for rf in rfs:
            if rf in r["name"] or rf in r["content"]:
                return True

    if record_filters is not None and len(record_filters) > 0:
        records = list(cytoolz.filter(lambda r: match(r, record_filters), records))

    return records


cpu_codenames = {
    'AMD': 'lisa',
    'Intel': 'mole',
    'Ampere': 'rma',
}

available_shapes = {
    # Always-Free
    'AMD': 'VM.Standard.E2.1.Micro',
    'VM.Standard.E2.1.Micro': 'VM.Standard.E2.1.Micro',
    'E2.1': 'VM.Standard.E2.1.Micro',
    'ARM': 'VM.Standard.A1.Flex',
    'VM.Standard.A1.Flex': 'VM.Standard.A1.Flex',

    # Free-trial available
    'VM.Standard3.Flex': 'VM.Standard3.Flex',
    '3Flex': 'VM.Standard3.Flex',
    'Intel': 'VM.Standard3.Flex',

    'VM.Standard.E4.Flex': 'VM.Standard.E4.Flex',
    'AMD_E4': 'VM.Standard.E4.Flex',
    'E4': 'VM.Standard.E4.Flex',

    'VM.Standard.E5.Flex': 'VM.Standard.E5.Flex',
    'AMD_E5': 'VM.Standard.E5.Flex',
    'E5': 'VM.Standard.E5.Flex',

    # Previous generation
    'VM.Standard.E2.1': 'VM.Standard.E2.1',
    'SE2.1': 'VM.Standard.E2.1',
    'VM.Standard.E2.2': 'VM.Standard.E2.2',
    'SE2.2': 'VM.Standard.E2.2',
    'VM.Standard.E2.4': 'VM.Standard.E2.4',
    'SE2.4': 'VM.Standard.E2.4',
    'VM.Standard.E2.8': 'VM.Standard.E2.8',
    'SE2.8': 'VM.Standard.E2.8',

    'VM.Standard.E3.Flex': 'VM.Standard.E3.Flex',
    'E3Flex': 'VM.Standard.E3.Flex',
    'AMD_E3': 'VM.Standard.E3.Flex',

    # VM.Standard1
    'VM.Standard1.1': 'VM.Standard1.1',
    'S1.1': 'VM.Standard1.1',
    'VM.Standard1.2': 'VM.Standard1.2',
    'S1.2': 'VM.Standard1.2',
    'VM.Standard1.4': 'VM.Standard1.4',
    'S1.4': 'VM.Standard1.4',
    'VM.Standard1.8': 'VM.Standard1.8',
    'S1.8': 'VM.Standard1.8',
    'VM.Standard1.16': 'VM.Standard1.16',
    'S1.16': 'VM.Standard1.16',

    # VM.Standard2
    'VM.Standard2.1': 'VM.Standard2.1',
    'S2.1': 'VM.Standard2.1',
    'VM.Standard2.2': 'VM.Standard2.2',
    'S2.2': 'VM.Standard2.2',
    'VM.Standard2.4': 'VM.Standard2.4',
    'S2.4': 'VM.Standard2.4',
    'VM.Standard2.8': 'VM.Standard2.8',
    'S2.8': 'VM.Standard2.8',
    'VM.Standard2.16': 'VM.Standard2.16',
    'S2.16': 'VM.Standard2.16',
    'VM.Standard2.24': 'VM.Standard2.24',
    'S2.24': 'VM.Standard2.24',

    # VM.Standard.B1
    'VM.Standard.B1.1': 'VM.Standard.B1.1',
    'SB1.1': 'VM.Standard.B1.1',
    'VM.Standard.B1.2': 'VM.Standard.B1.2',
    'SB1.2': 'VM.Standard.B1.2',
    'VM.Standard.B1.4': 'VM.Standard.B1.4',
    'SB1.4': 'VM.Standard.B1.4',
    'VM.Standard.B1.8': 'VM.Standard.B1.8',
    'SB1.8': 'VM.Standard.B1.8',
    'VM.Standard.B1.16': 'VM.Standard.B1.16',

}


def codename(cpu: str) -> str:
    for vendor, code in cpu_codenames.items():
        if vendor in cpu:
            return code
    return 'unknown'


def pretty(array: list[any]) -> str:
    if array is None or len(array) == 0:
        return "[]"
    pretty_array = ""
    for item in array:
        pretty_array += f"`{escape_markdown_v2(item)}`"
        pretty_array += ", " if item != array[-1] else ""
    return pretty_array


oci_regions = {
    "eu-amsterdam-1": {
        "country_code": "NL",
        "city": "Amsterdam",
    },
    "eu-stockholm-1": {
        "country_code": "SE",
        "city": "Stockholm",
    },
    "me-abudhabi-1": {
        "country_code": "AE",
        "city": "Abu Dhabi",
    },
    "sa-bogota-1": {
        "country_code": "CO",
        "city": "Bogota",
    },
    "ap-mumbai-1": {
        "country_code": "IN",
        "city": "Mumbai",
    },
    "eu-paris-1": {
        "country_code": "FR",
        "city": "Paris",
    },
    "uk-cardiff-1": {
        "country_code": "GB",
        "city": "Cardiff",
    },
    "me-dubai-1": {
        "country_code": "AE",
        "city": "Dubai",
    },
    "eu-frankfurt-1": {
        "country_code": "DE",
        "city": "Frankfurt",
    },
    "sa-saopaulo-1": {
        "country_code": "BR",
        "city": "Sao Paulo",
    },
    "ap-hyderabad-1": {
        "country_code": "IN",
        "city": "Hyderabad",
    },
    "us-ashburn-1": {
        "country_code": "US",
        "city": "Ashburn",
    },
    "iad": {
        "country_code": "US",
        "city": "Ashburn",
    },
    "ap-seoul-1": {
        "country_code": "KR",
        "city": "Seoul",
    },
    "me-jeddah-1": {
        "country_code": "SA",
        "city": "Jeddah",
    },
    "me-riyadh-1": {
        "country_code": "SA",
        "city": "Riyadh",
    },
    "af-johannesburg-1": {
        "country_code": "ZA",
        "city": "Johannesburg",
    },
    "ap-osaka-1": {
        "country_code": "JP",
        "city": "Osaka",
    },
    "uk-london-1": {
        "country_code": "GB",
        "city": "London",
    },
    "eu-milan-1": {
        "country_code": "IT",
        "city": "Milan",
    },
    "eu-madrid-1": {
        "country_code": "ES",
        "city": "Madrid",
    },
    "ap-melbourne-1": {
        "country_code": "AU",
        "city": "Melbourne",
    },
    "eu-marseille-1": {
        "country_code": "FR",
        "city": "Marseille",
    },
    "mx-monterrey-1": {
        "country_code": "MX",
        "city": "Monterrey",
    },
    "il-jerusalem-1": {
        "country_code": "IL",
        "city": "Jerusalem",
    },
    "ap-tokyo-1": {
        "country_code": "JP",
        "city": "Tokyo",
    },
    "us-chicago-1": {
        "country_code": "US",
        "city": "Chicago",
    },
    "us-phoenix-1": {
        "country_code": "US",
        "city": "Phoenix",
    },
    "phx": {
        "country_code": "US",
        "city": "Phoenix",
    },
    "mx-queretaro-1": {
        "country_code": "MX",
        "city": "Queretaro",
    },
    "sa-santiago-1": {
        "country_code": "CL",
        "city": "Santiago",
    },
    "ap-singapore-1": {
        "country_code": "SG",
        "city": "Singapore",
    },
    "ap-singapore-2": {
        "country_code": "SG",
        "city": "Singapore",
    },
    "us-sanjose-1": {
        "country_code": "US",
        "city": "San Jose",
    },
    "ap-sydney-1": {
        "country_code": "AU",
        "city": "Sydney",
    },
    "sa-valparaiso-1": {
        "country_code": "CL",
        "city": "Valparaiso",
    },
    "sa-vinhedo-1": {
        "country_code": "BR",
        "city": "Vinhedo",
    },
    "ap-chuncheon-1": {
        "country_code": "KR",
        "city": "Chuncheon",
    },
    "ca-montreal-1": {
        "country_code": "CA",
        "city": "Montreal",
    },
    "ca-toronto-1": {
        "country_code": "CA",
        "city": "Toronto",
    },
    "eu-zurich-1": {
        "country_code": "CH",
        "city": "Zurich",
    },
}


def city(region: str) -> str:
    if region not in oci_regions:
        return region
    return oci_regions[region]['city']


def flag(region: str) -> str:
    if region not in oci_regions:
        return region
    return emoji(oci_regions[region]['country_code'].upper())


def flagged_city(region: str) -> str:
    if region not in oci_regions:
        return region
    oci_region = oci_regions[region]
    return f'{flag(region)}{oci_region["city"]}'


def escape_markdown_v2(text: any, version: int = 2) -> str:
    if text is not str:
        return escape_markdown(str(text), version=version)
    return escape_markdown(text, version=version)


def markdown_list(array: list[any], level=0) -> str:
    if array is None or len(array) == 0:
        return ""
    md = ""
    prefix = " " * level * 2
    for e in array:
        if type(e) is str:
            md += f"{prefix}•  `{escape_markdown_v2(e)}`\n"
        elif type(e) is list:
            md += f"{prefix}•  {markdown_list(e, level=level + 1)}\n"
        elif type(e) is dict:
            md += f"{prefix}•  {markdown_dict(e, level=level + 1)}\n"
        else:
            md += f"{prefix}•  `{escape_markdown_v2(str(e))}`\n"
    return md


def markdown_dict(d: dict, level=0) -> str:
    md = ""
    prefix = " " * level * 2
    key_adjust = max([len(k) for k in d.keys()]) + 2
    for k, v in d.items():
        if type(v) is str:
            md += f"{prefix}•  `{escape_markdown_v2(k).ljust(key_adjust)}` : `{escape_markdown_v2(v)}`\n"
        elif type(v) is list:
            md += f"{prefix}•  `{escape_markdown_v2(k).ljust(key_adjust)}` : {pretty(v)}\n"
        elif type(v) is dict:
            md += f"{prefix}•  `{escape_markdown_v2(k).ljust(key_adjust)}` : {markdown_dict(v, level=level + 1)}\n"
        else:
            md += f"{prefix}•  `{escape_markdown_v2(k).ljust(key_adjust)}` : `{escape_markdown_v2(str(v))}`\n"
    return md


def value_map(d: dict):
    rd = {}
    for k, v in d.items():
        if v not in rd:
            rd[v] = [k]
        else:
            rd[v].append(k)
            rd[v] = sorted(set(rd[v]))
    return rd


class IPChange:
    __old__: str
    __new__: str
    __type__: str
    __dns_records__: dict

    def __init__(self, old=None, new=None, ip_type=None, dns_records=None):
        self.old = old
        self.new = new
        self.type = ip_type
        self.dns_records = dns_records

    @property
    def old(self):
        return self.__old__

    @old.setter
    def old(self, old):
        self.__old__ = old

    @property
    def new(self):
        return self.__new__

    @new.setter
    def new(self, new):
        self.__new__ = new

    @property
    def type(self):
        return self.__type__

    @type.setter
    def type(self, ip_type):
        self.__type__ = ip_type

    @property
    def dns_records(self):
        return self.__dns_records__

    @dns_records.setter
    def dns_records(self, dns_records):
        self.__dns_records__ = dns_records

    def add_record(self, record, ip):
        if self.__dns_records__ is None:
            self.__dns_records__ = {}
        self.__dns_records__[record] = ip

    def __str__(self):
        return f'{self.old} -> {self.new}'

    def markdown(self):
        prefix = ""

        if self.new is None:
            prefix = f'`{escape_markdown_v2(self.old)}`  ➡️ '
        md = f'•  {prefix}`{self.new}`'
        if self.dns_records is None or len(self.dns_records) == 0:
            return md

        md += ', dns records\n'
        for record, ip in self.dns_records.items():
            record_desc = ip
            icon = '🟢'
            if ip == self.old:
                icon = '🔴'
                record_desc = f'~~{record_desc}~~'
            md += f'{icon} `{record}` *↠* `{record_desc}`\n'
        return md

    def changed(self):
        return self.new is not None and self.old != self.new


class CloudFlareClient:
    __api_key__: str = None
    __api_email__: str = None
    __api_token__: str = None
    __zone_id__: str = None
    __api_client__: CloudFlare = None

    def __init__(self, api_key, email, zone_id, token=None):
        self.api_key = api_key
        self.email = email
        self.token = token
        self.zone_id = zone_id
        self.api_client = CloudFlare(key=api_key, email=email)

    @property
    def api(self):
        if self.__api_client__ is None:
            self.__api_client__ = CloudFlare(key=self.api_key, email=self.email)
        return self.__api_client__

    @property
    def api_key(self):
        return self.__api_key__

    @api_key.setter
    def api_key(self, api_key):
        self.__api_key__ = api_key

    @property
    def email(self):
        return self.__api_email__

    @email.setter
    def email(self, api_email):
        self.__api_email__ = api_email

    @property
    def token(self):
        return self.__api_token__

    @token.setter
    def token(self, api_token):
        self.__api_token__ = api_token

    def __getitem__(self, item):
        return getattr(self, item)

    @staticmethod
    def keys():
        return "api_key", "email", "token", "zone_id"

    def zone_name(self):
        return self.api.zones.get(self.zone_id)['name']

    def dns_records(self, ip=None, name=None) -> list[dict]:
        if self.api_key is None or self.email is None or self.zone_id is None:
            return []
        record_type = None if ip is None else 'A' if ip.count('.') == 3 else 'AAAA'
        records = []
        try:
            records = self.api.zones.dns_records.get(self.zone_id,
                                                     params={'type': record_type,
                                                             'content': ip,
                                                             'name': name,
                                                             'per_page': 50000})

        except Exception as e:
            logger.warning(f"failed to get dns records for {ip}, exception: {e}")

        return records

    def list_dns_records(self, ips: list[str] = None):
        if self.api_key is None or self.email is None or self.zone_id is None:
            return []
        records = []
        for ip in ips:
            record_type = None if ip is None else 'A' if ip.count('.') == 3 else 'AAAA'
            try:
                records = self.api.zones.dns_records.get(self.zone_id,
                                                         params={'type': record_type,
                                                                 'content': ip,
                                                                 'per_page': 50000})

            except Exception as e:
                logger.warning(f"failed to get dns records for {ip}, exception: {e}")

        return records

    def dns_record_names(self, ip) -> list[any]:
        records = self.dns_records(ip)
        if records is None or len(records) == 0:
            return []

        return list(cytoolz.unique([r['name'] for r in records]))

    def create_dns_record(self, record_name, ip) -> dict | Status:
        if self.api_key is None or self.email is None or self.zone_id is None:
            return Status(http.client.BAD_REQUEST, "BadRequest", "api_key, email, zone_id is required")
        try:
            return self.api.zones.dns_records.post(self.zone_id,
                                                   data={'name': record_name,
                                                         'type': 'A' if ip.count('.') == 3 else 'AAAA',
                                                         'content': ip,
                                                         'proxied': False,
                                                         'comment':
                                                             f'created by oci-arm @{datetime.now()}'})
        except Exception as e:
            return Status(http.client.INTERNAL_SERVER_ERROR, "InternalError", str(e))

    def delete_dns_records(self, records: list[dict]) -> list[dict]:
        if records is None or len(records) == 0:
            return []
        failed = []
        for record in records:
            try:
                self.api.zones.dns_records.delete(self.zone_id, record['id'])
            except Exception as e:
                logger.warning(f"failed to delete dns record {record['name']}, exception: {e}")
                failed.append(record)
        return failed

    def delete_dns_record(self, record_id) -> dict | Status:
        if self.api_key is None or self.email is None or self.zone_id is None:
            return Status(http.client.BAD_REQUEST, "BadRequest", "api_key, email, zone_id is required")

        try:
            return self.api.zones.dns_records.delete(self.zone_id, record_id)
        except Exception as e:
            return Status(http.client.INTERNAL_SERVER_ERROR, "InternalError", str(e))

    def update_dns_record(self, record, ip) -> dict | Status:
        record_name = record['name']
        try:
            now = datetime.now()
            return self.api.zones.dns_records.put(self.zone_id, record['id'],
                                                  data={'content': ip,
                                                        'name': record['name'],
                                                        'type': 'A' if ip.count('.') == 3 else 'AAAA',
                                                        'proxied': record[
                                                            'proxied'] if 'proxied' in record else False,
                                                        'comment': f'updated by oci-arm @{now}'})
        except Exception as e:
            logger.warning(f"failed to update dns record {record_name} to {ip}, exception: {e}")
            return Status(http.client.INTERNAL_SERVER_ERROR, "InternalError", str(e))

    def next_index(self, record_code_name, location, record_type='A') -> str:
        records = self.dns_records()
        if records is None or len(records) == 0:
            return 'a'

        matched = [r['name'] for r in records if r['name'].startswith(f'oc-{record_code_name}-') and
                   location in r['name'] and r['type'] == record_type]

        if len(matched) == 0:
            return 'a'

        matched.sort()
        # sort by name A-Z order
        last = matched[-1]
        index = last.split('.')[0].split('-')[-1]
        return chr(ord(index) + 1)

    def __str__(self):
        return f"api_key: {self.api_key}, api_email: {self.email}, api_token: {self.token}, zone_id: {self.zone_id}"


class InstanceLimit:
    __cpu_cores__: float
    __memory_in_gbs__: float
    __boot_volume_size_in_gbs__: float

    def __init__(self, cpu_cores, memory_in_gbs, boot_volume_size_in_gbs):
        self.cpu_cores = cpu_cores
        self.memory_in_gbs = memory_in_gbs
        self.boot_volume_size_in_gbs = boot_volume_size_in_gbs

    @property
    def cpu_cores(self):
        return self.__cpu_cores__

    @cpu_cores.setter
    def cpu_cores(self, cpu_cores):
        self.__cpu_cores__ = cpu_cores

    @property
    def memory_in_gbs(self):
        return self.__memory_in_gbs__

    @memory_in_gbs.setter
    def memory_in_gbs(self, memory_in_gbs):
        self.__memory_in_gbs__ = memory_in_gbs

    @property
    def boot_volume_size_in_gbs(self):
        return self.__boot_volume_size_in_gbs__

    @boot_volume_size_in_gbs.setter
    def boot_volume_size_in_gbs(self, boot_volume_size_in_gbs):
        self.__boot_volume_size_in_gbs__ = boot_volume_size_in_gbs

    def __str__(self):
        return '{"cpu_cores": %f, "memory_in_gbs": %f, "boot_volume_size_in_gbs": %f}' % (
            self.cpu_cores, self.memory_in_gbs, self.boot_volume_size_in_gbs)


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
        prettied = "`%s` `%s`" % (
            escape_markdown_v2(self.v4), ('%s' % '` `'.join(self.v6s) if len(self.v6s) > 0 else ""))
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

    def send_message(self, message, chat_id=None, reply_to_message_id=None):
        if chat_id is None:
            logger.warning("chat_id is None, message will not be sent")
            return

        url = f'https://{self.api_host}/bot{self.token}/sendMessage'
        data = {
            'chat_id': chat_id,
            'text': message,
            'parse_mode': 'MarkdownV2',
            'reply_to_message_id': reply_to_message_id
        }
        try:
            response = requests.post(url, data=data)
            logger.debug(response.text)
            if response.status_code != 200:
                logger.warning(f"send message [{message}] failed, status code: {response.status_code}, "
                               f"response: {response.text}")
            else:
                logger.info(f"send message success, message: {message}")
        except Exception as e:
            logger.warning(f"send message {message} failed, exception: {e}")


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

    @staticmethod
    def keys():
        return "private_key", "public_key", "passphrase"

    def __str__(self):
        return f"private_key: {self.private_key}, public_key: {self.public_key}, passphrase: {self.passphrase}"

    def from_dict(self, d: dict):
        for k, v in d.items():
            setattr(self, k, v)

    def save(self) -> None | str:
        if self.private_key is None or self.public_key is None:
            return None
        try:
            # Create a temporary directory.
            temp_dir = tempfile.mkdtemp()
            private_key_file = os.path.join(temp_dir, f'oci-arm-{uuid.uuid4()}.pem')
            with open(private_key_file, 'w') as pkf:
                pkf.write(self.private_key)
                os.chmod(private_key_file, 0o600)
            return private_key_file
        except Exception as e:
            logger.error(f"failed to save private key, exception: {e}")
            return None


def is_success(status):
    return status.status == http.client.OK and status.code == "Success"


def is_failed(status):
    return isinstance(status, Status) and not is_success(status)


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


class CreateInstanceDetails:
    def __init__(self, **kwargs) -> None:
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
        for k, v in kwargs.items():
            setattr(self, k, v)

    def from_terraform(self, terraform_file_path):
        __file_buf__ = ""
        try:
            tf = open(terraform_file_path, "r")
            __file_buf__ = tf.read()
            tf.close()

        except Exception as e:
            logger.error(f"failed to read terraform parameter file {terraform_file_path}, exception: {e}")
            return

        shape_regex = re.compile('shape = "(.*)"')
        self.__shape__ = shape_regex.findall(__file_buf__).pop()

        compartment_id_regex = re.compile('compartment_id = "(.*)"')
        self.__compartment_id__ = compartment_id_regex.findall(__file_buf__).pop()

        # memory
        try:
            memory_in_gbs_regex = re.compile('memory_in_gbs = "(.*)"')
            self.memory_in_gbs = float(memory_in_gbs_regex.findall(__file_buf__).pop())
        except IndexError:
            self.memory_in_gbs = 1
        # cpu
        try:
            cpu_regex = re.compile('ocpus = "(.*)"')
            self.ocpus = float(cpu_regex.findall(__file_buf__).pop())
        except IndexError:
            self.ocpus = 1

        # availability_domain
        availability_domain_regex = re.compile('availability_domain = "(.*)"')

        self.availability_domain = availability_domain_regex.findall(__file_buf__).pop()

        # subnet_id
        subnet_regex = re.compile('subnet_id = "(.*)"')
        self.subnet_id = subnet_regex.findall(__file_buf__).pop()

        # instance_name
        display_name_regex = re.compile('display_name = "(.*)"')
        display_name = display_name_regex.findall(__file_buf__).pop()
        display_name = display_name.strip().replace(" ", "-")
        self.display_name = display_name
        self.hostname_label = display_name.replace("_", "-")

        try:
            assign_public_ip_regex = re.compile('assign_public_ip = "(.*)"')
            assign_public_ip = assign_public_ip_regex.findall(__file_buf__).pop()
            self.assign_public_ip = True if assign_public_ip == "true" else False
        except IndexError:
            self.assign_public_ip = False

        # source_id
        source_id_regex = re.compile('source_id = "(.*)"')
        self.source_id = source_id_regex.findall(__file_buf__)[0]
        # boot_volume_size_in_gbs
        boot_volume_size_in_gbs_regex = re.compile('boot_volume_size_in_gbs = "(.*)"')
        try:
            self.boot_volume_size_in_gbs = float(boot_volume_size_in_gbs_regex.findall(__file_buf__).pop())
        except IndexError:
            self.boot_volume_size_in_gbs = 50.0

        boot_volume_vpus_per_gb_regex = re.compile('boot_volume_vpus_per_gb = "(.*)"')
        try:
            self.boot_volume_vpus_per_gb = float(boot_volume_vpus_per_gb_regex.findall(__file_buf__).pop())
        except IndexError:
            logger.info("`boot_volume_vpus_per_gb` not found，use default value 120")
            self.boot_volume_vpus_per_gb = 120

        ssh_authorized_keys_regex = re.compile('"ssh_authorized_keys" = "(.*)"')
        try:
            self.ssh_authorized_keys = ssh_authorized_keys_regex.findall(__file_buf__).pop()
        except IndexError:
            logger.info(f"ssh_authorized_keys not found, generate a new ssh key")
            self.ssh_authorized_keys = generate_ssh_key(comments=f"oci-{self.display_name}")

    @staticmethod
    def keys():
        return "availability_domain", "ocpus", "memory_in_gbs", \
            "hostname_label", "compartment_id", "assign_public_ip", \
            "subnet_id", "display_name", "source_id", "boot_volume_size_in_gbs", \
            "boot_volume_vpus_per_gb", "ssh_authorized_keys", "shape"

    def __getitem__(self, item):
        return getattr(self, item)

    def to_dict(self):
        return {k: getattr(self, k) for k in self.keys()}

    @property
    def shape(self):
        return self.__shape__

    @shape.setter
    def shape(self, shape):
        self.__shape__ = shape

    @property
    def ssh_authorized_keys(self):
        return self._ssh_authorized_keys_.public_key

    def ssh_private_key(self):
        return self._ssh_authorized_keys_.private_key

    def ssh_passphrase(self):
        return self._ssh_authorized_keys_.passphrase

    @ssh_authorized_keys.setter
    def ssh_authorized_keys(self, key):
        if isinstance(key, str) and key.startswith("ssh-rsa"):
            self._ssh_authorized_keys_ = SSHKey(private_key=None, public_key=key)
        else:
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
    __config__: dict = None

    def __init__(self, **kwargs):
        self.__config__ = {}
        for key, value in kwargs.items():
            self.__config__[key] = value
        self.__config__['additional_user_agent'] = f"oci-arm/{__version__}"
        validate_config(self.__config__)

    @property
    def compartment_id(self):
        return self.__config__['tenancy']

    @property
    def region(self):
        return self.__config__['region']

    @property
    def fingerprint(self):
        return self.__config__['fingerprint']

    @property
    def key_file(self):
        return self.__config__['key_file']

    @property
    def user(self):
        return self.__config__['user']

    @property
    def pass_phrase(self):
        return self.__config__['pass_phrase']

    @property
    def additional_user_agent(self):
        return self.__config__['additional_user_agent']

    @property
    def tenancy(self):
        return self.__config__['tenancy']

    def __getitem__(self, item):
        return self.__config__[item]

    @staticmethod
    def keys():
        return "user", "fingerprint", "key_file", "tenancy", "region", "pass_phrase", "additional_user_agent"


def config_from_file(oci_config_file, oci_profile) -> OciConfig | None:
    try:
        if os.path.exists(oci_config_file):
            config = from_file(oci_config_file, oci_profile)
            return OciConfig(**config)
    except Exception as e:
        logger.error(f"failed to load oci config from file {oci_config_file}, exception: {e}")
    return None


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
    __oci_client__ = None
    __oci_config__: OciConfig = None
    __limits_client__ = None
    __instance_tf__ = None
    __instance_id__ = None
    __public_ip__ = None
    __network_client__ = None
    __block_storage_client__ = None
    __object_storage_client__ = None
    __identity_client__ = None
    __client_name__ = None
    __telegram_bot__ = None
    __telegram_admin_chat_id__ = None
    __oci_profile__ = None
    __thread_pool__ = None
    __start_counter__ = {}
    __create_counter__ = {}
    __ssh_authorized_keys__ = None
    __cloudflare_config__ = None
    __cloudflare__ = None
    __ready__ = False  # Track if connection is warmed up and ready
    __method_cache__ = {}  # Cache for frequently called methods
    __cache_ttl__ = 15  # Default TTL for method caching (seconds)
    __auth_failure_count__ = 0  # Track authentication failures
    __max_auth_failures__ = 5  # Max failures before marking as dead
    __is_dead__ = False  # Mark profile as dead after repeated auth failures

    def notify(self, message: str, update: Update = None):
        self.warning(message)
        self.telegram(message=message, update=update)

    def info(self, text):
        message = f"[{self.name().ljust(20)}] {text.replace('`', '')}"
        logger.info(message)

    def warning(self, text):
        message = f"[{self.name().ljust(20)}] {text.replace('`', '')}"
        logger.warning(message)

    def fatal(self, message: str, update: Update = None):
        message = f"[{self.name().ljust(20)}] {message.replace('`', '')}"
        logger.error(message)
        self.telegram(message=message, update=update)

    def telegram(self, message, update: Update = None):
        if self.telegram_bot is None:
            logger.warning(f"telegram_bot is None, message will not be sent, please set telegram_bot")
            return

        reply_to_message_id = None
        if update is not None:
            chat_id = str(update.effective_user.id)
            reply_to_message_id = str(update.message.message_id)
        else:
            chat_id = self.admin_chat_id

        if chat_id is None:
            self.warning(f"chat_id is None, message will not be sent, please set admin_chat_id, update: {update}")
            return

        self.telegram_bot.send_message(chat_id=chat_id, message=message, reply_to_message_id=reply_to_message_id)

    @property
    def admin_chat_id(self):
        return self.__telegram_admin_chat_id__

    @admin_chat_id.setter
    def admin_chat_id(self, chat_id):
        self.__telegram_admin_chat_id__ = chat_id

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
        """Lazy initialization of ComputeClient for faster startup"""
        if self.__oci_client__ is None:
            self.__oci_client__ = ComputeClient(config=dict(self.oci_config))
        return self.__oci_client__

    @oci_client.setter
    def oci_client(self, oci_client):
        self.__oci_client__ = oci_client

    @property
    def network_client(self):
        """Lazy initialization of VirtualNetworkClient for faster startup"""
        if self.__network_client__ is None:
            self.__network_client__ = VirtualNetworkClient(config=dict(self.oci_config))
        return self.__network_client__

    @network_client.setter
    def network_client(self, network_client):
        self.__network_client__ = network_client

    @property
    def block_storage_client(self):
        """Lazy initialization of BlockstorageClient for faster startup"""
        if self.__block_storage_client__ is None:
            self.__block_storage_client__ = BlockstorageClient(config=dict(self.oci_config))
        return self.__block_storage_client__

    @block_storage_client.setter
    def block_storage_client(self, block_storage_client):
        self.__block_storage_client__ = block_storage_client

    @property
    def object_storage_client(self):
        """Lazy initialization of ObjectStorageClient for faster startup"""
        if self.__object_storage_client__ is None:
            self.__object_storage_client__ = ObjectStorageClient(config=dict(self.oci_config))
        return self.__object_storage_client__

    @object_storage_client.setter
    def object_storage_client(self, object_storage_client):
        self.__object_storage_client__ = object_storage_client

    @property
    def limits_client(self):
        """Lazy initialization of LimitsClient for faster startup"""
        if self.__limits_client__ is None:
            self.__limits_client__ = LimitsClient(config=dict(self.oci_config))
        return self.__limits_client__

    @limits_client.setter
    def limits_client(self, limits_client):
        self.__limits_client__ = limits_client

    @property
    def identity_client(self):
        """Lazy initialization of IdentityClient for faster startup"""
        if self.__identity_client__ is None:
            self.__identity_client__ = IdentityClient(config=dict(self.oci_config))
        return self.__identity_client__

    @identity_client.setter
    def identity_client(self, identity_client):
        self.__identity_client__ = identity_client

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
    def ssh_authorized_keys(self):
        return self.__ssh_authorized_keys__

    @ssh_authorized_keys.setter
    def ssh_authorized_keys(self, ssh_authorized_keys):
        self.__ssh_authorized_keys__ = ssh_authorized_keys

    @property
    def pool(self) -> ThreadPoolExecutor:
        if self.thread_pool is None:
            # Optimized fallback thread pool for I/O-bound OCI operations
            cpu_count = multiprocessing.cpu_count() or 4
            # Use CPU count * 2 for I/O-bound work, capped at reasonable limits
            max_workers = min(cpu_count * 2, 50)  # Cap at 50 for fallback
            max_workers = max(max_workers, 4)      # Minimum 4 threads
            self.thread_pool = ThreadPoolExecutor(
                max_workers=max_workers,
                thread_name_prefix=f"oci_fallback_{self.name()}"
            )
        return self.thread_pool

    @property
    def cloudflare(self):
        return self.__cloudflare__

    @cloudflare.setter
    def cloudflare(self, cloudflare_client):
        self.__cloudflare__ = cloudflare_client
    
    @property
    def ready(self):
        """Check if this OCI client connection is warmed up and ready"""
        return self.__ready__
    
    @ready.setter
    def ready(self, value):
        """Set the ready status of this OCI client"""
        self.__ready__ = value
    
    @property
    def is_dead(self):
        """Check if this profile is marked as dead (too many auth failures)"""
        return self.__is_dead__
    
    @property
    def auth_failure_count(self):
        """Get the authentication failure count"""
        return self.__auth_failure_count__
    
    def record_auth_failure(self):
        """Record an authentication failure and mark as dead if threshold exceeded"""
        self.__auth_failure_count__ += 1
        if self.__auth_failure_count__ >= self.__max_auth_failures__:
            self.__is_dead__ = True
            self.warning(f"Profile marked as DEAD after {self.__auth_failure_count__} authentication failures")
            return True  # Newly marked as dead
        else:
            self.warning(f"Authentication failure #{self.__auth_failure_count__}/{self.__max_auth_failures__}")
            return False
    
    def reset_auth_failures(self):
        """Reset failure count (e.g., after successful authentication)"""
        if self.__auth_failure_count__ > 0:
            self.info(f"Resetting auth failure count (was {self.__auth_failure_count__})")
            self.__auth_failure_count__ = 0
            self.__is_dead__ = False
    
    def mark_as_dead(self, dead=True):
        """Manually mark or unmark this profile as dead/not dead"""
        if dead:
            self.__auth_failure_count__ = self.__max_auth_failures__
            self.__is_dead__ = True
            self.warning(f"Profile manually marked as DEAD")
        else:
            self.reset_auth_failures()
            self.info(f"Profile manually marked as ALIVE")
    
    def handle_api_result(self, result):
        """Handle API result - check for auth failures and mark dead if needed"""
        if isinstance(result, Status):
            # Check for authentication failures
            if ((result.status == http.client.NOT_FOUND and result.code == 'NotAuthorizedOrNotFound') or
                    (result.status == http.client.UNAUTHORIZED and result.code == 'NotAuthenticated')):
                self.record_auth_failure()
            else:
                # Other error - reset counter on any non-auth error
                # This prevents marking as dead for transient issues
                pass
        else:
            # Successful call - reset failure counter
            self.reset_auth_failures()
        return result
    
    def _get_cached_method_result(self, method_name, key, ttl=None):
        """Get cached result of a method call"""
        cache_key = f"{method_name}_{key}"
        if cache_key in self.__method_cache__:
            timestamp, value = self.__method_cache__[cache_key]
            if time.time() - timestamp < (ttl or self.__cache_ttl__):
                return value
        return None
    
    def _set_cached_method_result(self, method_name, key, value):
        """Set cached result of a method call"""
        cache_key = f"{method_name}_{key}"
        self.__method_cache__[cache_key] = (time.time(), value)

    def name(self, skip_api_call=False):
        """Get client name, optionally skipping API calls for faster initialization"""
        if self.client_name is None:
            # Try to get name from tenancy, but only if we're ready or not skipping API calls
            if not skip_api_call and self.ready:
                tenancy = self.get_tenancy()
                if isinstance(tenancy, Tenancy):
                    name = f'{flagged_city(self.oci_config.region)}-{tenancy.name}'.lower()
                    self.client_name = name
        
        if self.client_name is None:
            # Fallback to profile name or compartment ID (no API calls needed)
            if self.profile_name is not None:
                self.client_name = self.profile_name
            elif self.oci_config is not None and self.oci_config.compartment_id is not None:
                # Use last part of compartment ID for brevity
                self.client_name = self.oci_config.compartment_id.split('.')[-1][:12]
            else:
                self.client_name = str(uuid.uuid4())[:8]
        return self.client_name

    def vcn_name(self):
        return f"{self.name()}-vcn"

    @property
    def telegram_bot(self):
        return self.__telegram_bot__

    @telegram_bot.setter
    def telegram_bot(self, telegram_bot):
        self.__telegram_bot__ = telegram_bot

    def add_log_file(self, skip_api_call=True):
        """Add a log file for this client, optionally skipping API calls during initialization"""
        # Skip log file creation during initialization for speed
        # All logs will go to the main log file
        # Individual client logs can be added later if needed
        return  # Defer log file creation to improve startup time

    def __init__(self,
                 config: OciConfig,
                 cloudflare: CloudFlareClient = None,
                 ssh_authorized_keys=None,
                 telegram_bot: TelegramBot = None,
                 telegram_admin_chat_id=None,
                 thread_pool=None) -> None:
        self.profile_name = None
        self.public_ip = None
        self.telegram_bot = telegram_bot
        self.admin_chat_id = telegram_admin_chat_id
        self.oci_config = config
        # Lazy initialization - don't create SDK clients until first use
        # This speeds up initialization from 21s to ~0.1s for 81 profiles!
        # self.oci_client = None  # Will be created on first access
        # self.network_client = None  # Will be created on first access
        # etc. - using properties below
        self.ssh_authorized_keys = ssh_authorized_keys
        # create a thread pool
        self.thread_pool = thread_pool
        # Add log file without making API calls (for fast initialization)
        self.add_log_file(skip_api_call=True)
        self.cloudflare = cloudflare

    def get_instance_records(self, instance: Instance) -> list[dict]:
        instance_id = instance.id
        instance_name = instance.display_name
        ips = self.get_public_ips(instance_id)
        if isinstance(ips, Status):
            self.warning(f"failed to get public ips for {instance_name}, details: {ips}")
            return []

        # Collect all IPs to fetch DNS records for
        all_ips = []
        for ip in ips:
            if ip.v4:
                all_ips.append(ip.v4)
            if ip.v6s is not None and len(ip.v6s) > 0:
                all_ips.extend(ip.v6s)
        
        if len(all_ips) == 0:
            return []
        
        # Parallelize DNS record fetching for better performance
        if len(all_ips) <= 1:
            # Single IP - no parallelization needed
            records = []
            for ip_addr in all_ips:
                records.extend(self.cloudflare.dns_records(ip_addr))
        else:
            # Multiple IPs - fetch in parallel
            with ThreadPoolExecutor(max_workers=min(len(all_ips), 10)) as executor:
                results = list(executor.map(self.cloudflare.dns_records, all_ips))
                records = [record for result in results for record in result]  # Flatten
        
        return records

    def update_dns_records(self, instance: Instance, changes: list[IPChange]) -> list[IPChange]:
        if self.cloudflare is None:
            return []

        instance_records = self.get_instance_records(instance)
        base_record_name = self.record_name(instance, record_type='A')
        
        # Parallelize DNS record operations for better performance
        def process_change(change):
            old_ip = change.old
            new_ip = change.new
            records = []
            if old_ip is not None:
                records = self.cloudflare.dns_records(old_ip)
            to_create = (records is None or len(records) == 0)
            
            if to_create:
                self.warning(f"no dns record found for {old_ip}, try to add it")
                record_names = [base_record_name]
                if instance_records is not None and len(instance_records) > 0:
                    record_names = [r['name'] for r in instance_records]
                
                for record_name in record_names:
                    result = self.cloudflare.create_dns_record(record_name=record_name, ip=new_ip)
                    if is_failed(result):
                        self.warning(f"failed to create dns record for {new_ip}, details: {result.message}")
                        change.add_record(record_name, old_ip)
                    else:
                        self.info(f"create dns record {result['name']} for {new_ip} success")
                        dns_record_name = result['name']
                        change.add_record(dns_record_name, new_ip)
            else:
                for record in records:
                    record_name = record['name']
                    result = self.cloudflare.update_dns_record(record=record, ip=new_ip)
                    if is_failed(result):
                        self.warning(f"failed to update dns record {record_name} to {new_ip}, details: {result.message}")
                        change.add_record(record_name, old_ip)
                    else:
                        self.info(f"update dns record {record_name} to {new_ip} success")
                        change.add_record(record_name, new_ip)
            return change
        
        if len(changes) <= 1:
            # Single change - no parallelization needed
            for change in changes:
                process_change(change)
        else:
            # Multiple changes - process in parallel
            with ThreadPoolExecutor(max_workers=min(len(changes), 10)) as executor:
                changes = list(executor.map(process_change, changes))
        
        return changes

    def record_name(self, instance: Instance, record_type='A') -> str | None:
        region = oci_regions[instance.region]
        if region is None:
            return None
        code = codename(instance.shape_config.processor_description)
        profile_city = region['city'].replace(' ', '').lower()
        country = region['country_code'].lower()
        location = f'{profile_city}.{country}'
        if country in ['sg']:
            location = country

        return f"oc-{code}-{self.cloudflare.next_index(code, location, record_type)}.{location}"

    def list_regions(self) -> list[Region] | Status:
        try:
            return self.identity_client.list_regions().data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def list_services(self) -> list[ServiceSummary] | Status:
        try:
            return self.limits_client.list_services(self.compartment_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def list_limits(self, service_name="compute", scope_type="AD") -> list[LimitValueSummary] | Status:
        try:
            availability_domain = self.default_availability_domain().name
            if scope_type == "REGION":
                availability_domain = None
            return self.limits_client.list_limit_values(compartment_id=self.compartment_id,
                                                        availability_domain=availability_domain,
                                                        service_name=service_name, scope_type=scope_type).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def get_resource_availability(self, limit_name, service_name="compute", scope_type="AD"):
        limits = self.list_limits(service_name=service_name, scope_type=scope_type)
        if isinstance(limits, Status):
            return limits

        # check cpu cores
        try:
            availability_domain = self.default_availability_domain().name
            if scope_type == "REGION":
                availability_domain = None
            return self.limits_client.get_resource_availability(compartment_id=self.compartment_id,
                                                                limit_name=limit_name, service_name=service_name,
                                                                availability_domain=availability_domain).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def get_availability(self, shape):
        cpu_limit_name = 'standard-a1-core-count'
        memory_limit_name = 'standard-a1-memory-count'
        boot_volume_limit_name = 'total-storage-gb'

        if shape == 'VM.Standard.E2.1.Micro':
            cpu_limit_name = 'standard-e2-1-core-count'
            memory_limit_name = 'standard-e2-1-memory-count'

        return InstanceLimit(cpu_cores=self.get_resource_availability(limit_name=cpu_limit_name).available,
                             memory_in_gbs=self.get_resource_availability(limit_name=memory_limit_name).available,
                             boot_volume_size_in_gbs=self.get_resource_availability(service_name='block-storage',
                                                                                    limit_name=boot_volume_limit_name).
                             available)

    def save_ssh_key(self, create_instance_details) -> str | None:
        if create_instance_details.ssh_private_key() is not None:
            private_key_file = f"{self.name()}_{create_instance_details.display_name}.pem"
            private_key_file = os.path.join(os.path.expanduser("~"), ".ssh", private_key_file)
            with open(private_key_file, "w") as pkf:
                pkf.write(create_instance_details.ssh_private_key())
            os.chmod(private_key_file, 0o600)
            return private_key_file
        return None

    def delete_instance_task(self, **kwargs):
        instance = kwargs.get("instance")
        update = kwargs.get("update")
        instance_id = instance.id
        instance_name = instance.display_name
        exiting = kwargs.get("exiting")
        task = kwargs.get("task")
        self.info(f"start to delete instance {instance_name}")
        result = self.oci_client.terminate_instance(instance_id=instance_id)
        if isinstance(result, Status):
            self.warning(f"failed to delete instance {instance_name}, details: {result.message}")
            return
        result = self.wait_for_instance_status(expected_status="TERMINATED", exiting=exiting, instance_id=instance_id)
        if isinstance(result, Status):
            self.warning(f"failed to wait instance {instance_id} to TERMINATED, details: {result.message}")
            if task is not None:
                task.fail()
            return
        instance_name = result.display_name
        self.notify(message=f"instance "
                            f"`{escape_markdown_v2(self.name())}`\\-"
                            f"`{escape_markdown_v2(instance_name)}` deleted", update=update)
        if task is not None:
            task.complete()

    def create_instance_task(self, **kwargs):
        shape = kwargs.get("shape")
        create_instance_details = kwargs.get("create_instance_details")
        exiting = kwargs.get("exiting")
        update = kwargs.get("update")
        task = kwargs.get("task")
        if shape is not None and create_instance_details is None:
            create_instance_details = self.build_create_instance_details(shape=shape,
                                                                         ssh_authorized_keys=self.ssh_authorized_keys)
        if exiting is None:
            return Status(http.client.BAD_REQUEST, "NoExitingEvent",
                          "exiting event not set, will not create instance")

        if create_instance_details is None:
            return Status(http.client.BAD_REQUEST, "NoCreateInstanceDetails", "create instance details not set")

        key_message = f"SSH Private Key            : use your own ssh key, please keep it in safe place"
        private_key_file = self.save_ssh_key(create_instance_details)
        # save private key to file
        if private_key_file is not None:
            self.info(f"start_instance\\-{create_instance_details.shape}, private key saved to {private_key_file}")
            key_message = (f"SSH Private Key            : {escape_markdown_v2(private_key_file)}\n"
                           f"SSH Private Key Passphrase : "
                           f"{escape_markdown_v2(create_instance_details.ssh_passphrase())}")

        message = ("**🐢`Create Instance` started 🐢**\n```\n"
                   "Profile                    : {}\n"
                   "Region                     : {}\n"
                   "Instance Name              : {}\n"
                   "Shape                      : {}\n"
                   "CPU                        : {}C\n"
                   "Memory                     : {}G\n"
                   "Boot Volume                : {}G\n"
                   "{}\n```".format(escape_markdown_v2(self.name()),
                                    escape_markdown_v2(create_instance_details.availability_domain),
                                    escape_markdown_v2(create_instance_details.display_name),
                                    escape_markdown_v2(create_instance_details.shape),
                                    escape_markdown_v2(create_instance_details.ocpus),
                                    escape_markdown_v2(create_instance_details.memory_in_gbs),
                                    escape_markdown_v2(create_instance_details.boot_volume_size_in_gbs),
                                    key_message))
        self.notify(message=message, update=update)
        instance_name = create_instance_details.display_name
        self.info(
            f"create_instance-No.{self.create_counter(machine=instance_name):012d}-{create_instance_details.shape}, "
            f"start to create instance")
        while not exiting.is_set():
            try:
                result = self.create_instance(create_instance_details=create_instance_details)
                self.increase_create_counter(machine=instance_name)
                if isinstance(result, Status):
                    if is_rate_limit(result):
                        if self.wait_time < 120:
                            self.wait_time += 15
                        self.warning(f"create_instance-No.{self.create_counter(machine=instance_name):012d}-"
                                     f"{create_instance_details.shape}, rate limit, wait {self.wait_time}s")
                        exiting.wait(self.wait_time)
                    elif is_out_of_host_capacity(result):
                        # no rate limit, but out of host capacity, can reduce wait time
                        if self.wait_time > 30:
                            self.wait_time -= 10
                        self.warning(f"create_instance-No.{self.create_counter(machine=instance_name):012d}-"
                                     f"{create_instance_details.shape}, "
                                     f"no rate limit, but out of host capacity, wait {self.wait_time}s")
                        exiting.wait(self.wait_time)
                    elif is_quota_exceeded(result):
                        self.notify(
                            message=f"create\\_instance\\-No\\.{self.create_counter(machine=instance_name):012d}\\-"
                                    f"`{escape_markdown_v2(self.name())}`\\-"
                                    f"`{escape_markdown_v2(create_instance_details.shape)}`, "
                                    f"quota exceeded, details: `{escape_markdown_v2(result.message)}`, "
                                    f"stop create instance",
                            update=update)
                        if task is not None:
                            task.fail()
                        break
                    else:
                        self.notify(
                            message=f"create\\_instance\\-No\\.{self.create_counter(machine=instance_name):012d}\\-"
                                    f"`{escape_markdown_v2(self.name())}`\\-"
                                    f"`{escape_markdown_v2(create_instance_details.shape)}`, "
                                    f"failed to create instance, details: `{escape_markdown_v2(result.message)}`, "
                                    f"wait {self.wait_time}s",
                            update=update)
                        exiting.wait(self.wait_time)
                else:
                    result = self.wait_for_instance_status(instance_id=result.id, exiting=exiting)
                    if isinstance(result, Status):
                        self.notify(
                            message=f"create\\_instance\\-No\\.{self.create_counter(machine=instance_name):012d}\\-"
                                    f"`{escape_markdown_v2(self.name())}`\\-"
                                    f"`{escape_markdown_v2(create_instance_details.shape)}`,"
                                    f"instance created "
                                    f"`{escape_markdown_v2(instance_name)}`, "
                                    f"but failed to wait provisioning, details: \n"
                                    f"`**{escape_markdown_v2(str(result.message))}**`",
                            update=update)
                        if task is not None:
                            task.fail()
                        break
                    public_ips = self.check_and_get_public_ips(instance_id=result.id, enable_ipv6=True)
                    if len(public_ips) == 0:
                        self.notify(
                            message=f"create\\_instance\\-No\\.{self.create_counter(machine=instance_name):012d}\\-"
                                    f"`{escape_markdown_v2(self.name())}`\\-"
                                    f"`{escape_markdown_v2(create_instance_details.shape)}`,"
                                    f"instance created "
                                    f"`{escape_markdown_v2(instance_name)}`: \n"
                                    f"•  *but no public ip found*, "
                                    f"•  instance status: `{escape_markdown_v2(result.lifecycle_state)}`",
                            update=update)
                        if task is not None:
                            task.fail()
                        break
                    ip_str = "\n".join([ip.pretty() for ip in public_ips])
                    ips = self.get_public_ips(result.id)
                    ip_changes = []
                    for ip in ips:
                        if ip.v4 is not None:
                            ip_changes.append(IPChange(None, ip.v4))
                        if ip.v6s is not None and len(ip.v6s) > 0:
                            for v6 in ip.v6s:
                                ip_changes.append(IPChange(None, v6))
                    ip_changes = self.update_dns_records(result, ip_changes)

                    allowed_ports = self.get_allowed_ports(instance_id=result.id)
                    allowed_ports_str = markdown_dict(allowed_ports)
                    dns_records_str = "".join(c.markdown() for c in ip_changes)

                    self.notify(
                        message=f"create\\_instance\\-No\\.{self.create_counter(machine=instance_name):012d}\\-"
                                f"`{escape_markdown_v2(self.name())}`\\-"
                                f"`{escape_markdown_v2(create_instance_details.shape)}`, instance created "
                                f"`{escape_markdown_v2(instance_name)}`: \n"
                                f"•  instance status: `{escape_markdown_v2(result.lifecycle_state)}`\n"
                                f"•  allowed ports: \n{allowed_ports_str}"
                                f"•  dns records: \n"
                                f"•  ip: {ip_str}\n"
                                f"{dns_records_str}",
                        update=update)
                    if task is not None:
                        task.complete()
                    break
            except Exception as e:
                self.warning(
                    f"create_instance-No.{self.create_counter(machine=instance_name):012d}"
                    f"-{create_instance_details.shape}, "
                    f"failed to create instance, details: {e}, "
                    f"wait {self.wait_time}s")
                exiting.wait(self.wait_time)

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
        self.info(f"start to allow port(s) for VCN-`{vcn_name}`: {description}")
        security_lists = self.get_vcn_security_list(vcn_id)
        if isinstance(security_lists, Status):
            self.warning(f"fail to allow port(s) for VCN-{vcn_name}: {description}，"
                         f"security list not found, details: {security_lists.message}")
            return
        if len(security_lists) == 0:
            self.warning(f"no security list found for VCN-{vcn_name}, "
                         f"try to create a new one")
            security_list = self.create_vcn_security_list(vcn)
            if isinstance(security_list, Status):
                self.warning(f"fail to create security list for VCN-{vcn_name}, details: {security_list.message}")
                return
            security_lists = [security_list]
        for security_list in security_lists:
            self.allow_security_list_ports(security_list.id, min_port, max_port, is_ipv6=is_ipv6, direction=direction,
                                           protocol=protocol)

    def allow_security_list_ports(self, security_list_id, min_port, max_port, is_ipv6=False, direction="INGRESS",
                                  protocol="ALL"):
        security_list = self.get_security_list(security_list_id)
        if is_failed(security_list):
            self.warning(f"fail to allow port(s) for Security List-{security_list_id}, "
                         f"security list not found, details: {security_list.message}")
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

        self.info(f"adding rule to Security List-{security_list_name}: {direction} {description}")

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
            self.warning(f"fail to add rule to Security List-{security_list_name}: "
                         f"{direction} {protocol} {min_port}-{max_port}，"
                         f"details:{result}")
        else:
            self.info(f"success to add rule to Security List-{security_list_name}: "
                      f"{direction} {protocol} {min_port}-{max_port}")

    def create_vcn_security_list(self, vcn: Vcn) -> SecurityList | Status:
        try:
            return self.network_client.create_security_list(
                create_security_list_details=CreateSecurityListDetails(
                    compartment_id=self.compartment_id,
                    vcn_id=vcn.id,
                    display_name=f"{vcn.display_name}-Security-List",
                )).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    async def clear_vcn_security_lists(self, vcn: Vcn):
        security_lists = self.get_vcn_security_list(vcn.id)
        if isinstance(security_lists, Status):
            self.warning(f"fail to clear Security Lists of VCN-{vcn.display_name}, details: {security_lists}")
            return security_lists
        for security_list in security_lists:
            result = self.clear_security_list_rules(security_list.id)
            if is_failed(result):
                self.warning(f"fail to clear Security List-{security_list.display_name}, details: {result}")
            else:
                self.info(f"success to clear Security List-{security_list.display_name}")

    def delete_security_list(self, security_list_id) -> Status:
        try:
            self.network_client.delete_security_list(security_list_id=security_list_id)
            return Status(http.client.OK, "Success", "success")
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def get_instance_vcns(self, instance_id) -> list[Vcn] | Status:
        vnics = self.list_vnics(instance_id)
        if isinstance(vnics, Status):
            return vnics
        
        # Parallelize subnet and VCN fetching
        def fetch_vcn(vnic):
            subnet = self.get_subnet(vnic.subnet_id)
            if isinstance(subnet, Status):
                self.warning(f"fail to get Subnet-{vnic.subnet_id}, details: {subnet}")
                return None
            vcn = self.get_vcn(subnet.vcn_id)
            if isinstance(vcn, Status):
                self.warning(f'fail to get VCN-{subnet.vcn_id}, details: {vcn}')
                return None
            return vcn
        
        if len(vnics) <= 1:
            # Single vnic - no parallelization needed
            vcns = []
            for vnic in vnics:
                vcn = fetch_vcn(vnic)
                if vcn is not None:
                    vcns.append(vcn)
        else:
            # Multiple vnics - fetch in parallel
            with ThreadPoolExecutor(max_workers=min(len(vnics), 5)) as executor:
                results = list(executor.map(fetch_vcn, vnics))
                vcns = [v for v in results if v is not None]
        
        return vcns

    def get_vcn_security_list(self, vcn_id) -> list[SecurityList] | Status:
        try:
            return self.network_client.list_security_lists(compartment_id=self.compartment_id, vcn_id=vcn_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def get_security_list(self, security_list_id) -> SecurityList | Status:
        try:
            return self.network_client.get_security_list(security_list_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def add_security_rule(self, security_list_id, ingress_security_rules=None, egress_security_rules=None) -> Status:
        try:
            if (ingress_security_rules is None or len(ingress_security_rules) == 0) and (
                    egress_security_rules is None or len(egress_security_rules) == 0):
                return Status(http.client.BAD_REQUEST, "NoSecurityRules", "no security rules")
            security_list = self.get_security_list(security_list_id)
            if isinstance(security_list, Status):
                self.warning(f"fail to get Security List-{security_list_id}, details: {security_list}")
                return security_list
            ingress_security_rules += security_list.ingress_security_rules
            egress_security_rules += security_list.egress_security_rules
            ingress_security_rules = unique_security_rules(ingress_security_rules)
            egress_security_rules = unique_security_rules(egress_security_rules)
            self.network_client.update_security_list(security_list_id=security_list_id,
                                                     update_security_list_details=UpdateSecurityListDetails(
                                                         ingress_security_rules=ingress_security_rules,
                                                         egress_security_rules=egress_security_rules, ))
            return Status(http.client.OK, "Success", "success")
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def clear_security_list_rules(self, security_list_id: str) -> Status:
        try:
            self.network_client.update_security_list(security_list_id=security_list_id,
                                                     update_security_list_details=UpdateSecurityListDetails(
                                                         ingress_security_rules=[],
                                                         egress_security_rules=[]))
            return Status(http.client.OK, "Success", "success")
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def get_allowed_ports(self, instance_id):
        allowed_tcp_ports = []
        allowed_udp_ports = []
        vcns = self.get_instance_vcns(instance_id)
        if isinstance(vcns, Status):
            self.warning(f'fail to get VCNs of instance-{instance_id}, details: {vcns}')
            return {'tcp': [], 'udp': []}
        
        # Parallelize security rules fetching for multiple VCNs
        def fetch_security_rules(vcn):
            security_rules = self.list_security_rules(vcn.id)
            if isinstance(security_rules, Status):
                self.warning(f'fail to get Security Rules of VCN-{vcn.id}, details: {security_rules}')
                return [], []
            
            tcp_ports = []
            udp_ports = []
            if security_rules is not None and len(security_rules) > 0:
                for rule in security_rules:
                    for ingress_rule in rule.ingress_security_rules:
                        if (ingress_rule.source_type == "CIDR_BLOCK" and (
                                ingress_rule.source == "0.0.0.0/0" or ingress_rule.source == "::/0")):
                            ip_version = 4
                            if ingress_rule.source == "::/0":
                                ip_version = 6
                            if ingress_rule.tcp_options is not None:
                                port_range = ingress_rule.tcp_options.destination_port_range
                                tcp_ports.append('IPv{}: {}-{}'.format(ip_version, port_range.min, port_range.max))
                            elif ingress_rule.protocol == "all":
                                tcp_ports.append('IPv{}: {}-{}'.format(ip_version, 1, 65535))
                            if ingress_rule.udp_options is not None:
                                port_range = ingress_rule.udp_options.destination_port_range
                                udp_ports.append('IPV{}: {}-{}'.format(ip_version, port_range.min, port_range.max))
                            elif ingress_rule.protocol == "all":
                                udp_ports.append('IPV{}: {}-{}'.format(ip_version, 1, 65535))
            return tcp_ports, udp_ports
        
        if len(vcns) <= 1:
            # Single VCN - no parallelization needed
            for vcn in vcns:
                tcp, udp = fetch_security_rules(vcn)
                allowed_tcp_ports.extend(tcp)
                allowed_udp_ports.extend(udp)
        else:
            # Multiple VCNs - fetch in parallel
            with ThreadPoolExecutor(max_workers=min(len(vcns), 5)) as executor:
                results = list(executor.map(fetch_security_rules, vcns))
                for tcp, udp in results:
                    allowed_tcp_ports.extend(tcp)
                    allowed_udp_ports.extend(udp)
        
        return {'tcp': allowed_tcp_ports, 'udp': allowed_udp_ports}

    def list_security_rules(self, vcn_id) -> list[SecurityList] | Status:
        try:
            return self.network_client.list_security_lists(compartment_id=self.compartment_id, vcn_id=vcn_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def list_vnics(self, instance_id) -> list[Vnic] | Status:
        vnic_attachments = self.list_vnic_attachments(instance_id)
        if isinstance(vnic_attachments, Status):
            return vnic_attachments

        # Parallelize vnic fetching for better performance
        vnics = []
        if len(vnic_attachments) <= 1:
            # Single vnic - no need for parallelization
            for vnic_attachment in vnic_attachments:
                vnic = self.get_vnic(vnic_attachment.vnic_id)
                if isinstance(vnic, Status):
                    self.warning(f"fail to get VNIC-{vnic_attachment.vnic_id}, details: {vnic}")
                    continue
                vnics.append(vnic)
        else:
            # Multiple vnics - fetch in parallel
            def fetch_vnic(vnic_attachment):
                vnic = self.get_vnic(vnic_attachment.vnic_id)
                if isinstance(vnic, Status):
                    self.warning(f"fail to get VNIC-{vnic_attachment.vnic_id}, details: {vnic}")
                    return None
                return vnic
            
            with ThreadPoolExecutor(max_workers=min(len(vnic_attachments), 5)) as executor:
                results = list(executor.map(fetch_vnic, vnic_attachments))
                vnics = [v for v in results if v is not None]
        
        return vnics

    def enable_instance_ipv6(self, instance_id):
        # get vnic
        instance = self.get_instance(instance_id)
        if isinstance(instance, Status):
            self.warning(f"fail to enable instance-{instance_id} ipv6, details: {instance}")
            return
        self.info(f"start to enable ipv6 on instance-{instance.display_name}")
        vnics = self.list_vnics(instance_id)
        if isinstance(vnics, Status):
            self.warning(f"fail to enable ipv6 on instance-{instance_id}, VNIC(s) not found, details: {vnics}")
            return
        for vnic in vnics:
            self.enable_vnic_ipv6(vnic.id)

    def has_ipv6(self, vnic_id):
        return len(self.get_vnic_ipv6_addresses(vnic_id)) > 0

    def get_vnic_vcn(self, vnic_id) -> Vcn | Status:
        vnic = self.get_vnic(vnic_id)
        if isinstance(vnic, Status):
            self.warning(f"fail to get VNIC-{vnic_id}, details: {vnic}")
            return vnic
        subnet = self.get_subnet(vnic.subnet_id)
        if isinstance(subnet, Status):
            self.warning(f"fail to get Subnet-{vnic.subnet_id}, details: {subnet}")
            return subnet
        vcn = self.get_vcn(subnet.vcn_id)
        if isinstance(vcn, Status):
            self.warning(f"fail to get VCN-{subnet.vcn_id}, details: {vcn}")
            return vcn
        return vcn

    def enable_vnic_ipv6(self, vnic_id) -> str | None:
        if self.has_ipv6(vnic_id):
            self.info(f'VNIC-{vnic_id} already has ipv6')
            return None
        vnic = self.get_vnic(vnic_id)
        if isinstance(vnic, Status):
            self.warning(f"fail to enable ipv6 on VNIC-{vnic_id}, details: {vnic}")
            return None

        vnic_name = vnic.display_name
        vcn = self.get_vnic_vcn(vnic.id)
        if isinstance(vcn, Status):
            self.warning(f"fail to enable ipv6 on VNIC-{vnic_id}, VNIC `{vnic_name}` not found, details: {vcn}")
            return None

        vcn_id = vcn.id
        vcn_name = vcn.display_name
        result = self.enable_vcn_ipv6(vcn_id, with_subnet=True)

        if isinstance(result, Status):
            self.warning(
                f"fail to enable ipv6 on VNIC-{vnic_name}, enable ipv6 on VCN-{vcn_name} failed, details: {result}")
            return None

        result = self.add_ipv6_to_vnic(vnic.id)
        if isinstance(result, Status):
            self.warning(
                f"fail to enable ipv6 on VNIC-{vnic_name}, add ipv6 to VNIC-{vnic_name} failed, details: {result}")
            return None

        self.info(f"enable ipv6 on VNIC-{vnic_name} success, ipv6: {result.ip_address}")
        return result.ip_address

    def add_ipv6_to_vnic(self, vnic_id) -> Ipv6 | Status:
        try:
            return self.network_client.create_ipv6(CreateIpv6Details(vnic_id=vnic_id)).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def add_ipv6_cidr_to_subnet(self, subnet_id, cidr_block=None) -> Status:
        try:
            self.network_client.add_ipv6_subnet_cidr(subnet_id=subnet_id,
                                                     add_subnet_ipv6_cidr_details=AddSubnetIpv6CidrDetails(
                                                         ipv6_cidr_block=cidr_block))
            return Status(http.client.OK, "Success", "Success")
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def enable_vcn_ipv6(self, vcn_id, with_subnet=True) -> Vcn | Status:
        vcn = self.get_vcn(vcn_id)
        if is_failed(vcn):
            self.warning(f"fail to enable ipv6 on VCN-{vcn_id}, get VCN failed, details: {vcn}")
            return vcn
        vcn_name = vcn.display_name
        if vcn.ipv6_cidr_blocks is not None and len(vcn.ipv6_cidr_blocks) > 0:
            if with_subnet:
                self.info(f"VCN-{vcn_name} already has ipv6: {vcn.ipv6_cidr_blocks[0]}, try to enable ipv6 on subnet")
                self.check_and_enable_vcn_subnets_ipv6(vcn_id)
            else:
                self.info(f"VCN-{vcn_name} already has ipv6: {vcn.ipv6_cidr_blocks[0]}")
        else:
            self.info(f"VCN-{vcn_name} has no ipv6, try to enable ipv6 on VCN")
            result = self.add_ipv6_cidr_to_vcn(vcn_id)
            if isinstance(result, Status) and is_failed(result):
                self.warning(f"fail to enable ipv6 on VCN-{vcn_name}, details: {result}")
                return result
            self.info(f"enable ipv6 on VCN-{vcn_name} success")
        self.info(f'wait 15s, start to check VCN-{vcn_name}\'s subnet')
        time.sleep(15)
        if with_subnet:
            self.info(f"start to check VCN-{vcn_name}\'s subnet")
            self.check_and_enable_vcn_subnets_ipv6(vcn_id)
        self.info(f'wait 15s, start to check VCN-{vcn_name}\'s security list')
        # refresh vcn
        vcn = self.get_vcn(vcn_id)
        if isinstance(vcn, Status):
            self.warning(f"fail to enable ipv6 on VCN-{vcn_name}, get VCN `{vcn_name}` failed, details: {vcn}")
            return vcn
        self.check_route_and_security_rules(vcn)
        return self.get_vcn(vcn_id)

    def check_and_enable_vcn_subnets_ipv6(self, vcn_id):
        vcn = self.get_vcn(vcn_id)
        if isinstance(vcn, Status):
            self.warning(f"fail to enable ipv6 on VCN-{vcn_id}, get VCN `{vcn_id}` failed, details: {vcn}")
            return
        vcn_name = vcn.display_name
        subnets = self.list_subnets(vcn_id)
        if isinstance(subnets, Status):
            self.warning(f"fail to enable ipv6 on VCN-{vcn_name}, get Subnets failed, details: {subnets}")
            return
        if len(subnets) == 0:
            self.warning(f"enable ipv6 on VCN-{vcn_name}, no Subnets found, try to create Subnet")
            result = self.create_subnet(vcn_id=vcn_id)
            if isinstance(result, Status):
                self.warning(f"fail to enable ipv6 on VCN-{vcn_name}, create Subnet failed, details: {result}")
                return
            subnets = [result]
        for subnet in subnets:
            if subnet.ipv6_cidr_blocks is not None and len(subnet.ipv6_cidr_blocks) > 0:
                self.info(f"Subnet-{subnet.display_name} already has ipv6: {subnet.ipv6_cidr_blocks[0]}, skip")
                continue
            vcn_cidr_block = vcn.ipv6_cidr_blocks[0]
            subnet_cidr_block = str(random_v6_subnet_cidr_block(vcn_cidr_block, 64))
            result = self.add_ipv6_cidr_to_subnet(subnet.id, cidr_block=subnet_cidr_block)
            if is_failed(result):
                self.warning(f"fail to enable ipv6 on Subnet-{subnet.display_name}, details: {result}")
                continue
            self.info(f"enable ipv6 on Subnet-{subnet.display_name} success, add ipv6 cidr: {subnet_cidr_block}")

    def add_ipv6_cidr_to_vcn(self, vcn_id) -> Status:
        try:
            self.network_client.add_ipv6_vcn_cidr(vcn_id=vcn_id, add_vcn_ipv6_cidr_details=AddVcnIpv6CidrDetails(
                is_oracle_gua_allocation_enabled=True))
            return Status(http.client.OK, "Success", "Success")
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def default_vnic(self, instance_id) -> Vnic | Status:
        try:
            attachments = self.oci_client.list_vnic_attachments(compartment_id=self.oci_config.compartment_id,
                                                                instance_id=instance_id)
            data = attachments.data
            if len(data) != 0:
                vnic_id = data[0].vnic_id
                return self.network_client.get_vnic(vnic_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def wait_for_instance_status(self, instance_id,
                                 exiting: threading.Event,
                                 expected_status='RUNNING',
                                 timeout=300,
                                 ) -> Instance | Status:
        if exiting is None:
            return Status(http.client.BAD_REQUEST, "NoExitingEvent", "exiting event not set, will not wait instance")
        start_time = time.time()
        count = 0
        instance_name = None
        while time.time() - start_time < timeout and not exiting.is_set():
            result = self.get_instance(instance_id=instance_id)
            if isinstance(result, Status):
                self.warning(f'fail to get status for instance `{instance_name}`, try count:{count}, details: {result}')
                count += 1
                exiting.wait(5)
            if isinstance(result, Instance):
                status = result.lifecycle_state
                if instance_name is None:
                    instance_name = result.display_name
                if result.lifecycle_state == expected_status:
                    return result
                else:
                    self.warning(f'waiting for instance `{instance_name}`\'s status, '
                                 f'current status: {status}, expected status: {expected_status}, '
                                 f'try count:{count}')
                    count += 1
                    exiting.wait(5)
        return Status(http.client.REQUEST_TIMEOUT, "RequestTimeout", "Request timeout")

    def get_instance(self, instance_id) -> Instance | Status:
        # Cache for 10 seconds (instance status can change)
        cached = self._get_cached_method_result('get_instance', instance_id, ttl=10)
        if cached is not None:
            return cached
        
        try:
            instance = self.oci_client.get_instance(instance_id=instance_id).data
            self._set_cached_method_result('get_instance', instance_id, instance)
            return instance
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def resize_instance(self, **kwargs):
        instance = kwargs.get("instance")
        cpu_cores = kwargs.get("cpu_cores")
        memory_in_gbs = kwargs.get("memory_in_gbs")
        update = kwargs.get("update")
        exiting = kwargs.get("exiting")
        task = kwargs.get("task")
        instance_name = instance.display_name
        instance_id = instance.id
        old_cpu_cores = int(instance.shape_config.ocpus)
        old_memory_in_gbs = int(instance.shape_config.memory_in_gbs)
        self.info(f"start to resize instance-`{instance_name}`")
        result = self.update_instance(instance_id=instance.id,
                                      update_instance_details=UpdateInstanceDetails(
                                          shape=instance.shape,
                                          update_operation_constraint="ALLOW_DOWNTIME",
                                          shape_config=UpdateInstanceShapeConfigDetails(
                                              ocpus=cpu_cores,
                                              memory_in_gbs=memory_in_gbs
                                          )))
        if is_failed(result):
            self.notify(message=f"fai to resize instance\\-"
                                f"`{escape_markdown_v2(self.name())}`\\-"
                                f"`{escape_markdown_v2(instance_name)}`, "
                                f"details: {escape_markdown_v2(result.message)}",
                        update=update)
            if task is not None:
                task.fail()
            return

        self.info(f'success to resize instance-`{instance_name}`')

        result = self.wait_for_instance_status(instance_id=instance_id, exiting=exiting)
        if is_failed(result):
            self.notify(message=f"fai to wait instance\\-"
                                f"`{escape_markdown_v2(self.name())}`\\-"
                                f"`{escape_markdown_v2(instance_name)}` to "
                                f"`RUNNING`, details: {escape_markdown_v2(result.message)}",
                        update=update)
            if task is not None:
                task.fail()
            return

        if task is not None:
            task.complete()

        try:
            new_cpu_cores = int(result.shape_config.ocpus)
            new_memory_in_gbs = int(result.shape_config.memory_in_gbs)
            self.notify(message=f"instance\\-"
                                f"`{escape_markdown_v2(self.name())}`\\-"
                                f"`{escape_markdown_v2(instance_name)}` resized, from "
                                f"`{escape_markdown_v2(str(old_cpu_cores))}C"
                                f"{escape_markdown_v2(str(old_memory_in_gbs))}G` to "
                                f"`{escape_markdown_v2(str(new_cpu_cores))}C"
                                f"{escape_markdown_v2(str(new_memory_in_gbs))}G`",
                        update=update)
        except Exception as e:
            self.warning("fail to notify instance resized, details: {}".format(e))

    def update_instance(self, instance_id, update_instance_details: UpdateInstanceDetails) -> Instance | Status:
        if update_instance_details is None:
            return self.get_instance(instance_id)
        try:
            return self.oci_client.update_instance(instance_id, update_instance_details=update_instance_details).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def rename_instance(self, instance_id, name):
        return self.update_instance(instance_id, UpdateInstanceDetails(display_name=name))

    def list_instance_console_connections(self, instance_id) -> list[ConsoleConnection] | Status:
        try:
            return self.oci_client.list_instance_console_connections(
                compartment_id=self.compartment_id,
                instance_id=instance_id).data
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def instance_console_connection(self, instance: Instance) -> list[ConsoleConnection] | Status:
        console_connections = self.list_instance_console_connections(instance.id)
        if isinstance(console_connections, Status):
            return console_connections
        if len(console_connections) == 0:
            return Status(http.client.NOT_FOUND, "NoConsoleConnection", "console connection not found")

        console_connections = list(cytoolz.filter(lambda x: x.lifecycle_state == "ACTIVE", console_connections))
        if len(console_connections) == 0:
            return Status(http.client.NOT_FOUND, "NoActiveConsoleConnection", "active console connection not found")
        return console_connections[0]

    def delete_instance_console_connections(self, instance: Instance) -> list[ConsoleConnection] | Status:
        console_connections = self.list_instance_console_connections(instance.id)
        if isinstance(console_connections, Status):
            return console_connections
        if len(console_connections) == 0:
            return []

        deleted_connections = []
        console_connections = list(cytoolz.filter(lambda x: x.lifecycle_state == "ACTIVE", console_connections))
        success = True
        for console_connection in console_connections:
            result = self.delete_console_connection(instance_console_connection_id=console_connection.id)
            if is_failed(result):
                logger.warning(f"fail to delete console connection-{console_connection.id}, details: {result}")
                success = False
            else:
                deleted_connections.append(console_connection)
                logger.info(f"success to delete console connection-{console_connection.id}")
        if success:
            return deleted_connections
        else:
            return Status(http.client.BAD_REQUEST, "FailToDeleteConsoleConnections",
                          "fail to delete console connections")

    def create_console_connection(self, instance_id: str, public_key: str) -> ConsoleConnection | Status:
        try:
            return self.oci_client.create_instance_console_connection(
                create_instance_console_connection_details=CreateInstanceConsoleConnectionDetails(
                    instance_id=instance_id,
                    public_key=public_key,
                )).data
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def delete_console_connection(self, instance_console_connection_id: str) -> Status:
        try:
            self.oci_client.delete_instance_console_connection(
                instance_console_connection_id=instance_console_connection_id)
            return Status(http.client.OK, "Success", "success")
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def get_instance_console_connection(self, instance_console_connection_id: str) -> ConsoleConnection | Status:
        try:
            return (self.oci_client.
                    get_instance_console_connection(instance_console_connection_id=instance_console_connection_id).data)
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

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

    def get_primary_ipv4(self, instance_id) -> str:
        primary_vnic = self.get_primary_vnic(instance_id)
        if isinstance(primary_vnic, Status):
            self.warning(f'fail to get primary vnic for instance-{instance_id}, details: {primary_vnic}')
            return "☹️PrimaryVnicNotFound☹️"

        return primary_vnic.public_ip

    def get_primary_ipv6(self, instance_id) -> list[str]:
        primary_vnic = self.get_primary_vnic(instance_id)
        if isinstance(primary_vnic, Status):
            self.warning(f'fail to get primary vnic for instance-{instance_id}, details: {primary_vnic}')

        return self.get_vnic_ipv6_addresses(primary_vnic.id)

    def get_primary_vnic(self, instance_id) -> Vnic | Status:
        attachments = self.list_vnic_attachments(instance_id)
        if isinstance(attachments, Status):
            return attachments
        if len(attachments) == 0:
            return Status(http.client.NOT_FOUND, "NoVnicAttachment", "vnic attachments not found")
        for attachment in attachments:
            vnic = self.get_vnic(attachment.vnic_id)
            if isinstance(vnic, Status):
                self.warning(f'fail to get VNIC-{attachment.vnic_id} for instance {instance_id}, details: {vnic}')
                continue
            if vnic.is_primary:
                return vnic
        return Status(http.client.NOT_FOUND, "NoPrimaryVnic", "primary vnic not found")

    def change_ip(self, instance: Instance, ip_type="EPHEMERAL") -> list[IPChange]:
        instance_id = instance.id
        instance_name = instance.display_name
        changes = []
        vnics = self.list_vnics(instance_id)
        if isinstance(vnics, Status):
            self.warning(f"fai to get instance-{instance_name}\'s VNIC, details: {vnics}")
            return changes
        
        # Parallelize IP changing for multiple vnics
        def process_vnic(vnic):
            if ip_type != "V6":
                change = self.change_vnic_ip_v4(vnic, lifetime=ip_type)
                if change is not None and change.changed():
                    return [change]
                return []
            else:
                return self.change_vnic_ip_v6(vnic)
        
        if len(vnics) <= 1:
            # Single vnic - no parallelization needed
            for vnic in vnics:
                changes.extend(process_vnic(vnic))
        else:
            # Multiple vnics - process in parallel
            with ThreadPoolExecutor(max_workers=min(len(vnics), 5)) as executor:
                results = list(executor.map(process_vnic, vnics))
                changes = [change for result in results for change in result]  # Flatten
        
        return changes

    def change_vnic_ip_v6(self, vnic) -> list[IPChange]:
        vnic_id = vnic.id
        vnic_name = vnic.display_name
        ipv6s = self.get_vnic_ipv6s(vnic_id)
        if len(ipv6s) == 0:
            self.warning(f"VNIC-{vnic_name} has no ipv6, try to enable ipv6")
            ipv6 = self.enable_vnic_ipv6(vnic_id)
            if ipv6 is None:
                self.warning(f"fail to enable ipv6 on VNIC-{vnic_name}")
                return []
            return [IPChange(old=None, new=ipv6, ip_type="V6")]

        changes = []
        for ipv6 in ipv6s:
            self.info(f"start to change ipv6 for VNIC-{vnic_name}, current ipv6: {ipv6.ip_address}")
            result = self.delete_ipv6(ipv6.id)
            if is_failed(result):
                self.warning(f"fail to delete ipv6-{vnic_name}, details: {result}")
                continue
            self.info(f"delete ipv6 address {ipv6.ip_address} from {vnic_name} success")
            new_ipv6 = self.add_ipv6_to_vnic(vnic_id)
            if isinstance(ipv6, Status):
                self.warning(f"fail to add ipv6 to VNIC-{vnic_name}, details: {ipv6}")
                continue
            new_ipv6_address = new_ipv6.ip_address
            changes.append(IPChange(old=ipv6.ip_address, new=new_ipv6_address, ip_type="V6"))
            self.info(f"add ipv6-{new_ipv6_address} to VNIC-{vnic_name} success")
        return changes

    def change_vnic_ip_v4(self, vnic, lifetime="EPHEMERAL") -> IPChange:
        change = IPChange(ip_type="V4")
        ip_info = self.get_public_ip_info(vnic.public_ip)
        vnic_name = vnic.display_name
        public_ip = vnic.public_ip
        change.old = public_ip
        private_ip_id = ip_info.private_ip_id if ip_info is not None else None
        if ip_info is None:
            self.warning(f'fail to get public ip info for VNIC-{vnic_name}, start to create new public ip')
            private_ip = self.get_private_ip_info(vnic.id, vnic.private_ip)
            if private_ip is None:
                self.warning(f'fail to get private ip info for VNIC-{vnic_name}, please check configuration')
                return change
            private_ip_id = private_ip.id
            self.info(f'start to create new public ip for VNIC-{vnic_name}, private ip: {private_ip.ip_address}')
        elif ip_info.lifetime == "EPHEMERAL":
            self.info(f"VNIC-{vnic_name}\'s public ip `{public_ip}` is EPHEMERAL, delete and create new public ip")
            result = self.delete_public_ip(ip_info.id)
            if is_failed(result):
                self.warning(f'fail to delete public ip `{public_ip}`, details: {result}')
                return change
            self.info(f'delete public ip `{public_ip}` success')
        elif ip_info.lifetime == "RESERVED":
            self.info(f"VNIC-{vnic_name}\'s public ip `{public_ip}` is RESERVED, unassign and create new public ip")
            result = self.unassign_static_public_ip(ip_info.id)
            if is_failed(result):
                self.warning(f'fail to unassign public ip `{public_ip}`, details: {result}')
                return change
            self.info(f'unassign public ip `{public_ip}` success')
        time.sleep(10)
        self.info(f'start to create new public ip for VNIC-{vnic_name}, private ip: {private_ip_id}')
        result = self.create_public_ip(lifetime=lifetime, private_ip_id=private_ip_id)
        if is_failed(result):
            if is_quota_exceeded(result) and lifetime == "RESERVED":
                self.warning(f'fail to create new `RESERVED` public ip for VNIC-{vnic_name}, '
                             f'quota exceeded, try to get from existing `RESERVED` public ip')
                change.new = self.use_existing_reserved_public_ip(private_ip_id)
                return change
            self.warning(f"fail to create new public ip for VNIC-{vnic_name}, details: {result}")
            return change
        change.new = result.ip_address
        self.info(f"create new public ip `{result.ip_address}` for VNIC-{vnic_name} success")
        return change

    def use_existing_reserved_public_ip(self, private_ip_id) -> str | None:
        result = self.list_reserved_public_ips()
        if isinstance(result, Status):
            self.warning(f'fail to get reserved public ip, details: {result}')
            return None
        for ip in result:
            if ip.lifecycle_state == "AVAILABLE":
                self.info(f'available reserved public ip found: {ip.ip_address}')
                result = self.assign_static_public_ip(ip.id, private_ip_id)
                if is_failed(result):
                    self.warning(f'fail to assign public ip `{ip.ip_address}` to private ip `{private_ip_id}`,'
                                 f' details: {result}')
                    return None
                self.info(f'assign public ip {ip.ip_address} success')
                return ip.ip_address
        self.warning(f'no available reserved public ip found')
        return None

    def unassign_static_public_ip(self, public_ip_id):
        try:
            self.network_client.update_public_ip(public_ip_id=public_ip_id,
                                                 update_public_ip_details=UpdatePublicIpDetails(
                                                     private_ip_id=""))
            return Status(http.client.OK, "Success", "Success")
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def assign_static_public_ip(self, public_ip_id, private_ip_id):
        try:
            self.network_client.update_public_ip(public_ip_id=public_ip_id,
                                                 update_public_ip_details=UpdatePublicIpDetails(
                                                     private_ip_id=private_ip_id))
            return Status(http.client.OK, "Success", "Success")
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def delete_public_ip(self, public_ip_id=None) -> Status:
        try:
            self.network_client.delete_public_ip(public_ip_id=public_ip_id)
            return Status(http.client.OK, "Success", "Success")
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def create_public_ip(self, lifetime="EPHEMERAL", private_ip_id=None) -> PublicIp | Status:
        try:
            return self.network_client.create_public_ip(
                CreatePublicIpDetails(compartment_id=self.oci_config.compartment_id, lifetime=lifetime,
                                      private_ip_id=private_ip_id)).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def get_public_ip_info(self, ip_address):
        public_ips = self.list_public_ips()
        if isinstance(public_ips, Status):
            self.warning(f'fail to get public ip info for ip `{ip_address}`, details: {public_ips}')
            return None
        for public_ip in public_ips:
            if public_ip.ip_address == ip_address:
                return public_ip
        return None

    def get_private_ip_info(self, vnic_id, ip_address):
        private_ips = self.list_private_ips(vnic_id=vnic_id)
        if isinstance(private_ips, Status):
            self.warning(f'fail to get private ip info for ip `{ip_address}`, details: {private_ips}')
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
        except ServiceError as e:
            self.warning(f'fal to get public ip for VNIC-{vnic_id}, details: {Status(e.status, e.code, e.message)}')
            return ""

    def get_public_ips(self, instance_id) -> list[IPAddress]:
        # Check cache first (IPs don't change frequently unless explicitly changed)
        cached = self._get_cached_method_result('get_public_ips', instance_id, ttl=20)
        if cached is not None:
            return cached
        
        public_ips = []
        attachments = self.list_vnic_attachments(instance_id=instance_id)
        if isinstance(attachments, Status):
            self.warning(f'fail to get public ip for instance-{instance_id}, details: {attachments}')
            return public_ips
        
        # Parallelize vnic and IPv6 fetching for better performance
        def fetch_ip_address(attachment):
            vnic_id = attachment.vnic_id
            vnic = self.get_vnic(vnic_id)
            if isinstance(vnic, Status):
                self.warning(f'fail to get public ip for instance-{instance_id}, vnic-{vnic_id} not found, details: {vnic}')
                return None
            v4addr = vnic.public_ip
            ipv6s = self.get_vnic_ipv6_addresses(vnic_id)
            return IPAddress(v4=v4addr, v6s=ipv6s)
        
        if len(attachments) <= 1:
            # Single attachment - no parallelization needed
            for attachment in attachments:
                ip_addr = fetch_ip_address(attachment)
                if ip_addr is not None:
                    public_ips.append(ip_addr)
        else:
            # Multiple attachments - fetch in parallel
            with ThreadPoolExecutor(max_workers=min(len(attachments), 5)) as executor:
                results = list(executor.map(fetch_ip_address, attachments))
                public_ips = [ip for ip in results if ip is not None]
        
        # Cache the result
        self._set_cached_method_result('get_public_ips', instance_id, public_ips)
        return public_ips

    def get_instance_ipv6s(self, instance) -> list[Ipv6]:
        instance_id = instance.id
        instance_name = instance.display_name
        attachments = self.list_vnic_attachments(instance_id=instance_id)
        if isinstance(attachments, Status):
            self.warning(f'fail to get ipv6 for instance-{instance_name}, details: {attachments}')
            return []

        # Parallelize IPv6 fetching for better performance
        def fetch_ipv6s(attachment):
            vnic_id = attachment.vnic_id
            vnic = self.get_vnic(vnic_id)
            if isinstance(vnic, Status):
                self.warning(f'fail to get ipv6 for instance-{instance_name}, vnic-{vnic_id} not found, details: {vnic}')
                return []
            return self.get_vnic_ipv6s(vnic_id)
        
        if len(attachments) <= 1:
            # Single attachment - no parallelization needed
            ipv6s = []
            for attachment in attachments:
                ipv6s.extend(fetch_ipv6s(attachment))
        else:
            # Multiple attachments - fetch in parallel
            with ThreadPoolExecutor(max_workers=min(len(attachments), 5)) as executor:
                results = list(executor.map(fetch_ipv6s, attachments))
                ipv6s = [ip for result in results for ip in result]  # Flatten
        
        return ipv6s

    def get_vnic_ipv6_addresses(self, vnic_id) -> list[str]:
        results = self.get_vnic_ipv6s(vnic_id)
        if isinstance(results, Status):
            self.warning(f'fail to get ipv6 address for VNIC-{vnic_id}, details: {results}')
            return []
        return [ipv6.ip_address for ipv6 in results]

    def get_vnic_ipv6s(self, vnic_id) -> list[Ipv6] | Status:
        try:
            return self.network_client.list_ipv6s(vnic_id=vnic_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def delete_ipv6(self, ipv6_id) -> Status:
        try:
            self.network_client.delete_ipv6(ipv6_id=ipv6_id)
            return Status(http.client.OK, "Success", "Success")
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def get_vnic(self, vnic_id) -> Vnic | Status:
        try:
            return self.network_client.get_vnic(vnic_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def list_vnic_attachments(self, instance_id=None):
        try:
            return self.oci_client.list_vnic_attachments(compartment_id=self.oci_config.compartment_id,
                                                         instance_id=instance_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def build_create_instance_details(self,
                                      shape='VM.Standard.A1.Flex',
                                      ocpus=None,
                                      memory_in_gbs=None,
                                      subnet_id=None,
                                      source_id=None,
                                      display_name=None,
                                      boot_volume_size_in_gbs=None,
                                      boot_volume_vpus_per_gb=None,
                                      ssh_authorized_keys=None,
                                      assign_public_ip=True) -> CreateInstanceDetails | Status:
        shapes = self.list_shape_names()
        if shape not in shapes:
            return Status(http.client.BAD_REQUEST, "InvalidShape",
                          f"shape `{escape_markdown_v2(shape)}` not found, please check your configuration, "
                          f'available shapes: {escape_markdown_v2(str(shapes))}')

        if subnet_id is None:
            subnet = self.default_subnet()
            subnet_id = subnet.id if isinstance(subnet, Subnet) else None

        if subnet_id is None:
            return Status(http.client.UNPROCESSABLE_ENTITY, "NoSubnet",
                          "subnet not found, please check your configuration")

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

        return CreateInstanceDetails(shape=shape,
                                     ocpus=ocpus,
                                     memory_in_gbs=memory_in_gbs,
                                     subnet_id=subnet_id,
                                     source_id=source_id,
                                     display_name=display_name,
                                     boot_volume_size_in_gbs=boot_volume_size_in_gbs,
                                     boot_volume_vpus_per_gb=boot_volume_vpus_per_gb,
                                     ssh_authorized_keys=ssh_authorized_keys,
                                     assign_public_ip=assign_public_ip,
                                     compartment_id=self.oci_config.compartment_id,
                                     availability_domain=self.default_availability_domain().name)

    def delete_instance(self, instance_id) -> Status:
        try:
            return self.oci_client.terminate_instance(instance_id)
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def create_instance(self, shape=None, create_instance_details=None) -> Instance | Status:
        if shape is not None and create_instance_details is None:
            create_instance_details = self.build_create_instance_details(shape=shape,
                                                                         ssh_authorized_keys=self.ssh_authorized_keys)
        if create_instance_details is None:
            return Status(http.client.BAD_REQUEST, "NoCreateInstanceDetails", "no create instance details found")
        try:
            return self.oci_client.launch_instance(launch_instance_details=LaunchInstanceDetails(
                display_name=create_instance_details.display_name,
                compartment_id=create_instance_details.compartment_id,
                shape=create_instance_details.shape,
                shape_config=LaunchInstanceShapeConfigDetails(
                    ocpus=create_instance_details.ocpus,
                    memory_in_gbs=create_instance_details.memory_in_gbs),
                availability_domain=create_instance_details.availability_domain,
                create_vnic_details=CreateVnicDetails(
                    subnet_id=create_instance_details.subnet_id,
                    hostname_label=create_instance_details.hostname_label,
                    assign_public_ip=create_instance_details.assign_public_ip),
                source_details=InstanceSourceViaImageDetails(
                    image_id=create_instance_details.source_id,
                    boot_volume_size_in_gbs=create_instance_details.boot_volume_size_in_gbs,
                    boot_volume_vpus_per_gb=create_instance_details.boot_volume_vpus_per_gb),
                metadata=dict(
                    ssh_authorized_keys=create_instance_details.ssh_authorized_keys),
                is_pv_encryption_in_transit_enabled=True, )).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def list_availability_domains(self):
        return self.identity_client.list_availability_domains(self.compartment_id).data

    def default_availability_domain(self):
        availability_domains = self.list_availability_domains()
        if len(availability_domains) == 0:
            return
        return availability_domains[0]

    def get_tenancy(self) -> Tenancy | Status:
        # Skip dead profiles to avoid wasting time
        if self.is_dead:
            return Status(http.client.UNAUTHORIZED, "ProfileDead", 
                         f"Profile marked as dead after {self.auth_failure_count} auth failures")
        
        try:
            tenancy = self.identity_client.get_tenancy(self.compartment_id).data
            # Successful call - reset failure counter
            self.reset_auth_failures()
            return tenancy
        except ServiceError as e:
            result = Status(e.status, e.code, e.message)
            # Check and handle authentication failures
            self.handle_api_result(result)
            return result

    def list_subnets(self, vcn_id=None) -> list[Subnet] | Status:
        try:
            return self.network_client.list_subnets(self.compartment_id, vcn_id=vcn_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def has_subnet(self) -> bool:
        subnets = self.list_subnets()
        if isinstance(subnets, Status):
            return False
        return len(subnets) > 0

    def list_vcns(self) -> list[Vcn] | Status:
        try:
            return self.network_client.list_vcns(self.compartment_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def list_reserved_public_ips(self) -> list[PublicIp] | Status:
        try:
            return self.network_client.list_public_ips(scope="REGION", compartment_id=self.compartment_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def list_public_ips(self) -> list[PublicIp] | Status:
        try:
            availability_domain = self.default_availability_domain().name
            ephemeral_ips = (self.network_client.list_public_ips(scope="AVAILABILITY_DOMAIN",
                                                                 availability_domain=availability_domain,
                                                                 compartment_id=self.compartment_id).data)

            reserved_ips = self.network_client.list_public_ips(scope="REGION", compartment_id=self.compartment_id).data
            return ephemeral_ips + reserved_ips
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def list_private_ips(self, subnet_id=None, vnic_id=None) -> list[PrivateIp] | Status:
        try:
            return self.network_client.list_private_ips(subnet_id=subnet_id, vnic_id=vnic_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def has_vcn(self) -> bool:
        vcns = self.list_vcns()
        if isinstance(vcns, Status):
            return False
        return len(vcns) > 0

    def list_shapes(self) -> list[Shape] | Status:
        try:
            return self.oci_client.list_shapes(self.compartment_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def list_shape_names(self) -> list[str]:
        shapes = self.list_shapes()
        names = []
        if isinstance(shapes, Status):
            return names
        for shape in shapes:
            names.append(shape.shape)
        return names

    def list_images(self,
                    shape=None,
                    operating_system=None,
                    operating_system_version=None) -> list[Image] | Status:
        try:
            return self.oci_client.list_images(self.compartment_id,
                                               shape=shape,
                                               operating_system=operating_system,
                                               operating_system_version=operating_system_version).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def default_ubuntu_image(self, shape):
        images = self.list_images(shape=shape, operating_system="Canonical Ubuntu")
        if isinstance(images, Status):
            return None
        if len(images) == 0:
            return None
        return images[0]

    def get_subnet(self, subnet_id) -> Subnet | Status:
        try:
            return self.network_client.get_subnet(subnet_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def default_subnet(self) -> Subnet | Status:
        result = self.default_vcn()
        if isinstance(result, Status):
            return result
        listed = self.list_subnets(vcn_id=result.id)
        if isinstance(listed, Status):
            return listed
        if len(listed) > 0:
            return listed[0]
        self.warning(f'no subnet found for VCN-{result.display_name}, try to create new subnet')
        return self.create_subnet(result.id)

    def default_vcn(self) -> Vcn | Status:
        result = self.list_vcns()
        if isinstance(result, Status):
            return result
        if len(result) > 0:
            vcn = result[0]
            self.info(f'default VCN found: {vcn.display_name}')
        else:
            self.warning(f'no VCN found, try to create new VCN')
            vcn = self.create_vcn()
            if isinstance(vcn, Status):
                self.warning(f'fail to create VCN, details: {vcn}')
            else:
                self.info(f'create VCN success: {vcn.display_name}')
        vcn_name = vcn.display_name
        self.info(f'wait 15s, start to check VCN-{vcn_name}\'s subnet')
        subnets = self.list_subnets(vcn_id=vcn.id)
        if isinstance(subnets, Status):
            self.warning(f'fail to get subnet for VCN-{vcn_name}, details: {subnets}')
            return vcn
        if len(subnets) == 0:
            self.warning(f'no subnet found for VCN-{vcn_name}, try to create new subnet')
            subnet = self.create_subnet(vcn.id)
            if isinstance(subnet, Status):
                self.warning(f'fail to create subnet for VCN-{vcn_name}, details: {subnet}')
            else:
                self.info(f'create Subnet success: {subnet.display_name}')
        else:
            self.info(f'Subnet found for VCN-{vcn_name}: {subnets[0].display_name}')
        return self.get_vcn(vcn.id)

    def check_route_and_security_rules(self, vcn, allow_traffic=True):
        self.info(f'wait 15s, start to check VCN-{vcn.display_name}\'s Internet Gateway')
        vcn_id = vcn.id
        internet_gateways = self.list_internet_gateways(vcn_id=vcn_id)
        if isinstance(internet_gateways, Status):
            self.warning(f'fail to get Internet Gateway for VCN-{vcn.display_name}, details: {internet_gateways}')
            return
        if len(internet_gateways) == 0:
            self.warning(f'no Internet Gateway found for VCN-{vcn.display_name}, try to create new Internet Gateway')
            gateway = self.create_internet_gateway(vcn_id)
            if isinstance(gateway, Status):
                self.warning(f'fail to create Internet Gateway for VCN-{vcn.display_name}, details: {gateway}')
                return
            self.info(f'create Internet Gateway success: {gateway.display_name}, wait 15s, start to check Route Table')
            internet_gateways = [gateway]
            time.sleep(15)
        for gateway in internet_gateways:
            self.check_route_table(vcn, gateway)
        if allow_traffic:
            self.allow_vcn_inbound_ports(vcn, min_port=22, max_port=22)  # SSH
            self.allow_vcn_inbound_ports(vcn, min_port=1024, max_port=65535)  # unprivileged ports
            self.allow_vcn_outbound(vcn)

    def allow_vcn_inbound_ports(self, vcn, min_port=1024, max_port=65535):
        self.info(f'allow port(s) {min_port}-{max_port} for VCN-{vcn.display_name}')
        is_ipv6_enabled = vcn.ipv6_cidr_blocks is not None and len(vcn.ipv6_cidr_blocks) > 0
        self.allow_vcn_ports(vcn, min_port=min_port, max_port=max_port, protocol="TCP")  # TCP
        self.allow_vcn_ports(vcn, min_port=min_port, max_port=max_port, protocol="UDP")  # UDP
        if is_ipv6_enabled:
            self.allow_vcn_ports(vcn, min_port=min_port, max_port=max_port, is_ipv6=True, protocol="TCP")  # TCP
            self.allow_vcn_ports(vcn, min_port=min_port, max_port=max_port, is_ipv6=True, protocol="UDP")  # UDP

    def allow_vcn_outbound(self, vcn):
        self.info(f'allow all outbound traffic for VCN-{vcn.display_name}')
        is_ipv6_enabled = vcn.ipv6_cidr_blocks is not None and len(vcn.ipv6_cidr_blocks) > 0
        self.allow_vcn_ports(vcn, direction="EGRESS")
        if is_ipv6_enabled:
            self.allow_vcn_ports(vcn, direction="EGRESS", is_ipv6=True)

    def check_route_table(self, vcn, gateway):
        self.info(f'start to check VCN-{vcn.display_name}\'s Route Table')
        route_table_id = vcn.default_route_table_id
        is_ipv6_enabled = vcn.ipv6_cidr_blocks is not None and len(vcn.ipv6_cidr_blocks) > 0
        if route_table_id is None:
            self.warning(f'no Route Table found for VCN-{vcn.display_name}, try to create new Route Table')
            route_table = self.create_route_table(vcn.id, with_ipv6=is_ipv6_enabled, internet_gateway_id=gateway.id)
            if isinstance(route_table, Status):
                self.warning(f'fail to create Route Table for VCN-{vcn.display_name}, details: {route_table}')
                return
            self.info(f'create Route Table success: {route_table.display_name}')
            route_table_id = route_table.id
        route_table = self.get_route_table(route_table_id)
        if isinstance(route_table, Status):
            self.warning(f'fail to get Route Table for VCN-{vcn.display_name}, details: {route_table}')
            return
        self.info(f'Route Table found: {route_table.display_name}, start to check Route Rule')
        has_v4_route = False
        has_v6_route = False
        if len(route_table.route_rules) > 0:
            for rule in route_table.route_rules:
                if rule.destination == "0.0.0.0/0":
                    has_v4_route = True
                if rule.destination == "::/0":
                    has_v6_route = True
        if not has_v4_route:
            self.warning(f'no IPv4 Route Rule found for VCN-{vcn.display_name}, try to create new IPv4 Route Rule')
            result = self.create_route_rule(route_table_id, gateway.id, "0.0.0.0/0")
            if isinstance(result, Status):
                self.warning(f'fail to create IPv4 Route Rule for VCN-{vcn.display_name}, details: {result}')
            else:
                self.info(f'create IPv4 Route Rule for VCN-{vcn.display_name} success')
        else:
            self.info(f'IPv4 Route Rule found for VCN-{vcn.display_name}')
        if not has_v6_route and is_ipv6_enabled:
            self.info(f'no IPv6 Route Rule found for VCN-{vcn.display_name}, try to create new IPv6 Route Rule')
            result = self.create_route_rule(route_table_id, gateway.id, "::/0")
            if isinstance(result, Status):
                self.warning(f'fail to create IPv6 Route Rule for VCN-{vcn.display_name}, details: {result}')
            else:
                self.info(f'create IPv6 Route Rule for VCN-{vcn.display_name} success')
        else:
            self.info(f"IPv6 Route Rule found for VCN-{vcn.display_name}")

    def create_route_table(self, vcn_id, with_ipv6=False, internet_gateway_id=None) -> RouteTable | Status:
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
                CreateRouteTableDetails(compartment_id=self.compartment_id, vcn_id=vcn_id,
                                        display_name=f"{self.name()}-route-table",
                                        route_rules=route_rules)).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def create_route_rule(self, route_table_id, network_entity_id, cidr_block) -> RouteTable | Status:
        try:
            route_table = self.get_route_table(route_table_id)
            if isinstance(route_table, Status):
                self.warning(f'fail to get Route Table-{route_table_id}, details: {route_table}')
                return route_table
            route_rules = route_table.route_rules
            route_rules.append(
                RouteRule(destination=cidr_block, destination_type="CIDR_BLOCK", network_entity_id=network_entity_id,
                          route_type="STATIC"))
            return self.network_client.update_route_table(rt_id=route_table_id,
                                                          update_route_table_details=UpdateRouteTableDetails(
                                                              route_rules=route_rules)).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def create_internet_gateway(self, vcn_id, route_table_id=None) -> InternetGateway | Status:
        try:
            return self.network_client.create_internet_gateway(
                CreateInternetGatewayDetails(compartment_id=self.compartment_id, vcn_id=vcn_id,
                                             route_table_id=route_table_id, is_enabled=True,
                                             display_name=f"{self.name()}-internet-gateway", )).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def create_vcn(self, enable_ipv6=False) -> Vcn | Status:
        try:
            return self.network_client.create_vcn(
                create_vcn_details=CreateVcnDetails(cidr_block="10.0.0.0/24",
                                                    is_ipv6_enabled=enable_ipv6,
                                                    compartment_id=self.compartment_id,
                                                    display_name=f"{self.name()}-vcn", )).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def get_vcn(self, vcn_id) -> Vcn | Status:
        try:
            return self.network_client.get_vcn(vcn_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def get_route_table(self, route_table_id) -> RouteTable | Status:
        try:
            return self.network_client.get_route_table(rt_id=route_table_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def get_internet_gateway(self, internet_gateway_id) -> InternetGateway | Status:
        try:
            return self.network_client.get_internet_gateway(internet_gateway_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def list_internet_gateways(self, vcn_id=None) -> list[InternetGateway] | Status:
        try:
            return self.network_client.list_internet_gateways(compartment_id=self.compartment_id, vcn_id=vcn_id).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def get_vcn_internet_gateways(self, vcn_id):
        gateways = self.list_internet_gateways(vcn_id=vcn_id)
        if isinstance(gateways, Status):
            self.warning(f'fail to get Internet Gateway for VCN-{vcn_id}, details: {gateways}')
            return []
        return gateways

    def has_internet_gateway(self, vcn_id) -> bool:
        return len(self.get_vcn_internet_gateways(vcn_id)) > 0

    def create_subnet(self, vcn_id, is_ipv6_enabled=True) -> Subnet | Status:
        try:
            ipv6_cidr_block = None
            if is_ipv6_enabled:
                vcn = self.get_vcn(vcn_id)
                if isinstance(vcn, Vcn) and vcn.ipv6_cidr_blocks is not None and len(vcn.ipv6_cidr_blocks) > 0:
                    # 2603:c026:4501:9700::/56 create a subnet with /64
                    ipv6_cidr_block = vcn.ipv6_cidr_blocks[0].replace("/56", "/64")
            return self.network_client.create_subnet(
                create_subnet_details=CreateSubnetDetails(compartment_id=self.compartment_id,
                                                          display_name=f"{self.name()}-subnet",
                                                          vcn_id=vcn_id, cidr_block="10.0.0.0/24",
                                                          ipv6_cidr_block=ipv6_cidr_block, )).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def list_instances(self, status=None) -> list[Instance] | Status:
        # Skip dead profiles to avoid wasting time
        if self.is_dead:
            return Status(http.client.UNAUTHORIZED, "ProfileDead", 
                         f"Profile marked as dead after {self.auth_failure_count} auth failures")
        
        match_instances = []
        try:
            instances = self.oci_client.list_instances(self.compartment_id).data
            for instance in instances:
                if status is None or instance.lifecycle_state == status:
                    match_instances.append(instance)
            # Successful call - reset failure counter
            self.reset_auth_failures()
            return match_instances
        except ServiceError as e:
            result = Status(e.status, e.code, e.message)
            # Check and handle authentication failures
            self.handle_api_result(result)
            return result

    async def list_stopped_instances(self) -> list[Instance] | Status:
        return self.list_instances(status="STOPPED")

    def instance_action(self, instance_id, action="START") -> Instance | Status:
        try:
            return self.oci_client.instance_action(instance_id=instance_id, action=action).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def instance_action_task(self, **kwargs):
        instance = kwargs.get("instance")
        action = kwargs.get("action")
        exiting = kwargs.get("exiting")
        update = kwargs.get("update")
        task = kwargs.get("task")

        instance_id = instance.id
        instance_name = instance.display_name

        if exiting is None:
            message = f"can not {action} instance: " \
                      f"`{escape_markdown_v2(self.name())}`\\-" \
                      f"`{escape_markdown_v2(instance_name)}` \\- " \
                      f"`{escape_markdown_v2(self.get_primary_ipv4(instance_id))}`" \
                      f", exiting is None"
            self.notify(message, update)
            return

        expected_statuses = {
            "START": "RUNNING",
            "RESET": "RUNNING",
            "SOFTRESET": "RUNNING",
            "DIAGNOSTICREBOOT": "RUNNING",
            "STOP": "STOPPED",
            "SOFTSTOP": "STOPPED",
            "TERMINATE": "TERMINATED",
        }

        message = (f"`{escape_markdown_v2(self.name())}` start to `{escape_markdown(action)}` instance: "
                   f"`{escape_markdown_v2(instance_name)}` \\- "
                   f"`{escape_markdown_v2(self.get_primary_ipv4(instance_id))}`")
        self.notify(message=message, update=update)
        while not exiting.is_set():
            try:
                result = self.instance_action(instance_id, action=action)
                self.increase_start_counter(machine=instance_name)
                if isinstance(result, Status):
                    if is_rate_limit(result):
                        if self.wait_time < 120:
                            self.wait_time += 15
                        self.warning(f"[instance action({action})] - "
                                     f"No.{self.start_counter(machine=instance_name):012d}-`"
                                     f"{instance_name}`: "
                                     f"request rate limit, wait {self.wait_time}s")
                        exiting.wait(self.wait_time)
                    elif is_out_of_host_capacity(result):
                        if self.wait_time > 30:
                            self.wait_time -= 10
                        self.warning(
                            f"[instance action({action})] - "
                            f"No.{self.start_counter(machine=instance_name):012d}-`{instance_name}`: "
                            f"out of host capacity, wait {self.wait_time}s")
                        exiting.wait(self.wait_time)
                    else:
                        self.warning(
                            f"[instance action({action})] - "
                            f"No.{self.start_counter(machine=instance_name):012d}-`{instance_name}`: "
                            f"fail to do {action} on instance, details: {result}, "
                            f"wait {self.wait_time}s")
                        exiting.wait(self.wait_time)
                else:
                    result = self.wait_for_instance_status(instance_id=instance_id,
                                                           exiting=exiting,
                                                           expected_status=expected_statuses[action])
                    if isinstance(result, Status):
                        self.notify(message=f'\\[instance action\\({action}\\)\\] \\- '
                                            f'No\\.{self.start_counter(machine=instance_name):012d}\\-`'
                                            f"`{escape_markdown_v2(self.name())}`\\-"
                                            f'{escape_markdown_v2(instance_name)}`: '
                                            f'wait for starting instance failed, details: '
                                            f'{escape_markdown_v2(str(result))}, '
                                            f'please check manually', update=update)
                        self.warning(f"[instance action({action})] - "
                                     f"No.{self.start_counter(machine=instance_name):012d}-`{instance_name}`: "
                                     f"fail to do {action} on instance, details: {result}, "
                                     f"wait {self.wait_time}s")
                        exiting.wait(self.wait_time)
                        continue
                    message = (f'`{escape_markdown_v2(self.name())}` \\[instance action\\({action}\\)\\]  \\- '
                               f'No\\.{self.start_counter(machine=instance_name):012d}\\-`'
                               f"`{escape_markdown_v2(self.name())}`\\-"
                               f'{escape_markdown_v2(instance_name)}`: '
                               f'action `{action}` success, '
                               f'instance status: `{escape_markdown_v2(result.lifecycle_state)}`')
                    self.notify(message=message, update=update)
                    task.complete()
                    break
            except Exception as e:
                logger.warning(f"[instance action({action})] - "
                               f"No.{self.start_counter(machine=instance_name):012d}-`{instance_name}`: "
                               f"fail to do {action} on instance, details: {e}, "
                               f"wait {self.wait_time}s")
                exiting.wait(self.wait_time)

    def wait_for_console_connection(self,
                                    instance: Instance,
                                    console_connection: ConsoleConnection,
                                    exiting: threading.Event,
                                    expected_lifecycle_state="ACTIVE"
                                    ) -> ConsoleConnection | Status:
        wait_time = 5
        start_time = time.time()
        console_connection_id = console_connection.id
        while not exiting.is_set() and time.time() - start_time < 300:
            try:
                console_connection = self.get_instance_console_connection(console_connection_id)
                if isinstance(console_connection, Status):
                    self.warning(f"fail to get console connection [{instance.display_name}], "
                                 f"details: {console_connection}, wait {wait_time}s")
                    exiting.wait(wait_time)
                    continue
                lifecycle_state = console_connection.lifecycle_state
                if lifecycle_state != expected_lifecycle_state:
                    self.warning(f"waiting for console connection [{instance.display_name}] status, "
                                 f"expected: {expected_lifecycle_state}, actual: {lifecycle_state}, wait {wait_time}s")
                    exiting.wait(wait_time)
                else:
                    return console_connection
            except Exception as e:
                self.warning(f"fail to get console connection [{instance.display_name}], details: {e}, "
                             f"wait {wait_time}s")
                exiting.wait(wait_time)
        return Status(http.client.BAD_REQUEST, "Timeout", "timeout")

    def create_boot_volume(self, display_name=None, source_id=None) -> BootVolume | Status:
        try:
            return self.block_storage_client.create_boot_volume(
                create_boot_volume_details=CreateBootVolumeDetails(
                    compartment_id=self.compartment_id,
                    display_name=display_name,
                    source_details=BootVolumeSourceFromBootVolumeDetails(
                        type="bootVolume",
                        id=source_id,
                    )
                )).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def create_volume(self, display_name=None, size_in_gbs=50.0, source_id=None) -> Volume | Status:
        try:
            return self.block_storage_client.create_volume(
                create_volume_details=CreateVolumeDetails(
                    display_name=display_name,
                    size_in_gbs=size_in_gbs,
                    vpus_per_gb=120,
                    source_id=source_id,
                )).data
        except ServiceError as e:
            return Status(e.status, e.code, e.message)

    def list_boot_volume_attachments(self, instance_id=None,
                                     boot_volume_id=None) -> list[BootVolumeAttachment] | Status:
        try:
            availability_domain = self.default_availability_domain().name
            return self.oci_client.list_boot_volume_attachments(compartment_id=self.compartment_id,
                                                                availability_domain=availability_domain,
                                                                instance_id=instance_id,
                                                                boot_volume_id=boot_volume_id).data
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def list_volume_attachments(self, instance_id=None,
                                volume_id=None) -> list[VolumeAttachment] | Status:
        try:
            availability_domain = self.default_availability_domain().name
            return self.oci_client.list_volume_attachments(compartment_id=self.compartment_id,
                                                           availability_domain=availability_domain,
                                                           instance_id=instance_id,
                                                           volume_id=volume_id).data
        except ServiceError as ex:
            Status(ex.status, ex.code, ex.message)

    def get_volume_attachment(self, attachment_id) -> VolumeAttachment | Status:
        try:
            return self.oci_client.get_volume_attachment(attachment_id).data
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def list_boot_volumes(self, instance_id=None) -> list[BootVolume] | Status:
        try:
            availability_domain = self.default_availability_domain().name
            boot_volumes = self.block_storage_client.list_boot_volumes(compartment_id=self.compartment_id,
                                                                       availability_domain=availability_domain).data

            if instance_id is None:
                return boot_volumes

            boot_volume_attachments = self.list_boot_volume_attachments(instance_id=instance_id)

            if isinstance(boot_volume_attachments, Status):
                return boot_volume_attachments

            boot_volume_ids = [attachment.boot_volume_id for attachment in boot_volume_attachments if
                               attachment.instance_id == instance_id]
            return [boot_volume for boot_volume in boot_volumes if boot_volume.id in boot_volume_ids]
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def list_volumes(self, instance_id=None) -> list[Volume] | Status:
        try:
            volumes = self.block_storage_client.list_volumes(compartment_id=self.compartment_id).data
            if instance_id is None:
                return volumes
            volume_attachments = self.list_volume_attachments(instance_id=instance_id)
            if isinstance(volume_attachments, Status):
                return volume_attachments
            volume_ids = [attachment.volume_id for attachment in volume_attachments if
                          attachment.instance_id == instance_id and attachment.lifecycle_state == "ATTACHED"]
            return [volume for volume in volumes if volume.id in volume_ids]
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def get_volume(self, volume_id, volume_type='BlockVolume') -> BootVolume | Volume | Status:
        try:
            return self.block_storage_client.get_volume(volume_id).data if volume_type != 'BlockVolume' else \
                self.block_storage_client.get_boot_volume(volume_id).data
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def wait_for_volume_status(self, volume: BootVolume | Volume,
                               attachment: BootVolumeAttachment | VolumeAttachment,
                               action, exiting) -> Status:
        wait_time = 5
        start_time = time.time()
        expected_statuses = {
            'attach': ['ATTACHED'],
            'detach': ['DETACHED'],
        }
        while not exiting.is_set() and time.time() - start_time < 300:
            try:
                result = self.get_boot_volume_attachment(attachment.id) if isinstance(volume,
                                                                                      BootVolume) \
                    else self.get_volume_attachment(attachment.id)

                if isinstance(result, Status):
                    logger.warning(f"fail to get volume: {volume.display_name} attachment, details: {result}"
                                   f", wait {wait_time}s")
                    exiting.wait(wait_time)
                    continue
                attachment = result
                lifecycle_state = attachment.lifecycle_state
                if lifecycle_state not in expected_statuses[action]:
                    logger.warning(f"waiting for volume: {volume.display_name} status, expected: "
                                   f"{expected_statuses[action]}, actual: {lifecycle_state}, "
                                   f"wait {wait_time}s")
                    exiting.wait(wait_time)
                else:
                    return Status(http.client.OK, "Success", "Success")
            except Exception as e:
                self.warning(f"fail to get volume: {volume.display_name}, details: {e}, wait {wait_time}s")
                exiting.wait(wait_time)
                continue
        return Status(http.client.REQUEST_TIMEOUT, "Timeout", "wait for volume status timeout")

    def volume_action_task(self, **kwargs):
        volume = kwargs.get("volume")
        instance = kwargs.get("instance")
        update = kwargs.get("update")
        exiting = kwargs.get("exiting")
        action = kwargs.get("action")
        task = kwargs.get("task")
        if not isinstance(volume, Volume) and not isinstance(volume, BootVolume):
            self.warning(f'fail to start task: `{action}` volume, '
                         f'details: volume is not an instance of Volume or BootVolume')
            return Status(http.client.BAD_REQUEST, "InvalidVolume",
                          "volume is not an instance of Volume or BootVolume")

        result = self.detach_volume(volume=volume, instance=instance) if action == "detach" else \
            self.attach_volume(volume=volume, instance=instance)

        direction = 'to' if action == 'attach' else 'from'

        if isinstance(result, Status):
            self.notify(message=f'fail to {action} volume '
                                f"`{escape_markdown_v2(self.name())}`\\-"
                                f'`{escape_markdown_v2(volume.display_name)}` '
                                f'{direction} instance: `{escape_markdown_v2(instance.display_name)}`, '
                                f' details: `{escape_markdown_v2(str(result))}`',
                        update=update)
            task.fail()
            return

        result = self.wait_for_volume_status(attachment=result, volume=volume, exiting=exiting, action=action)
        if is_failed(result):
            self.notify(message=f'fail to {action} volume '
                                f"`{escape_markdown_v2(self.name())}`\\-"
                                f'`{escape_markdown_v2(volume.display_name)}` '
                                f'{direction} instance: `{escape_markdown_v2(instance.display_name)}`, '
                                f' details: `{escape_markdown_v2(str(result))}`',
                        update=update)
            task.fail()
            return

        self.notify(message=f'`{action}` volume: '
                            f"`{escape_markdown_v2(self.name())}`\\-"
                            f'`{escape_markdown_v2(volume.display_name)}` '
                            f'{direction} instance: `{escape_markdown_v2(instance.display_name)}` success',
                    update=update)
        task.complete()

    def attach_volume(self, volume: Volume | BootVolume, instance: Instance) -> VolumeAttachment | Status:
        try:
            return self.oci_client.attach_volume(
                attach_volume_details=AttachParavirtualizedVolumeDetails(
                    volume_id=volume.id,
                    instance_id=instance.id,
                    is_shareable=True,
                )).data
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def detach_volume(self, volume: Volume | BootVolume, instance: Instance, ) \
            -> VolumeAttachment | BootVolumeAttachment | Status:
        attachments = self.list_volume_attachments(instance_id=instance.id, volume_id=volume.id) \
            if isinstance(volume, Volume) else self.list_boot_volume_attachments(
            instance_id=instance.id, boot_volume_id=volume.id)

        if isinstance(attachments, Status):
            return attachments

        attachments = [attachment for attachment in attachments if attachment.lifecycle_state == "ATTACHED"]

        if len(attachments) == 0:
            return Status(http.client.BAD_REQUEST, "NOTATTACHED", "volume not attached to instance")

        # should only have one attachment
        try:
            action = self.oci_client.detach_boot_volume if isinstance(volume,
                                                                      BootVolume) else self.oci_client.detach_volume
            action(attachments[0].id)
            return attachments[0]
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def get_boot_volume_attachment(self, boot_volume_attachment_id) -> BootVolumeAttachment | Status:
        try:
            return self.oci_client.get_boot_volume_attachment(boot_volume_attachment_id).data
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def get_boot_volume(self, boot_volume_id) -> BootVolume | Status:
        try:
            return self.block_storage_client.get_boot_volume(boot_volume_id).data
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def detach_boot_volume(self, boot_volume_attachment_id) -> Status:
        try:
            self.oci_client.detach_boot_volume(boot_volume_attachment_id)
            return Status(http.client.OK, "OK", "Success")
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def update_boot_volume(self, boot_volume_id, display_name=None,
                           size_in_gbs=None, vpus_per_gb=None) -> BootVolume | Status:
        try:
            self.block_storage_client.update_boot_volume(boot_volume_id,
                                                         update_boot_volume_details=UpdateBootVolumeDetails(
                                                             display_name=display_name,
                                                             size_in_gbs=size_in_gbs,
                                                             vpus_per_gb=vpus_per_gb))
            return self.get_boot_volume(boot_volume_id)
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def get_namespace(self) -> str | Status:
        try:
            return self.object_storage_client.get_namespace().data
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)

    def create_bucket(self, bucket_name,
                      public_access_type="NoPublicAccess",
                      storage_tier="Standard",
                      versioning="Disabled") -> Bucket | Status:
        try:
            return self.object_storage_client.create_bucket(
                namespace_name=self.get_namespace(),
                create_bucket_details=CreateBucketDetails(
                    name=bucket_name,
                    compartment_id=self.compartment_id,
                    public_access_type=public_access_type,
                    storage_tier=storage_tier,
                    versioning=versioning,
                )
            ).data
        except ServiceError as ex:
            return Status(ex.status, ex.code, ex.message)


def all_profiles(oci_config_file):
    _profiles = []
    if not os.path.exists(oci_config_file):
        return _profiles
    try:
        with open(oci_config_file) as ocf:
            parser = ConfigParser()
            parser.read_file(ocf)
            for section in parser.sections():
                _profiles.append(section)
    except Exception as e:
        logger.error(f"fail to read oci config file: {oci_config_file}, details: {e}")
    
    return _profiles


START_TO_ADD_PROFILE, INPUT_PROFILE_DETAILS, INPUT_PRIVATE_KEY, PASSPHRASE_REQUIRED, \
    KEY_VALIDATED = range(5)
DONE = ConversationHandler.END


class Task:
    __task_id__: str = None
    __task_name__: str = None
    __created_at__: datetime = datetime.now()
    __function__ = None
    __function_name__: str = None
    __args__: tuple = None
    __kwargs__: dict = None
    __status__: str = None
    __start_time__: datetime = None
    __end_time__: datetime = None
    __exiting__: threading.Event = threading.Event()
    __cancellable__: bool = False
    __thread_pool__: ThreadPoolExecutor = None
    __oci__profile__ = None
    __command__ = None

    def __init__(self,
                 task_name: str,
                 function_name: str,
                 function: Callable,
                 task_id: str = None,
                 command: str = None,
                 oci_profile: str = None,
                 thread_pool: ThreadPoolExecutor = None,
                 args: tuple = None,
                 kwargs: dict = None):
        self.id = str(uuid.uuid4()) if task_id is None else task_id
        self.name = task_name
        self.__function_name__ = function_name
        self.__thread_pool__ = thread_pool
        self.__function__ = function
        self.__command__ = command
        self.__oci__profile__ = oci_profile
        self.__args__ = args
        if self.__exiting__ is None:
            self.__exiting__ = threading.Event()
        self.__kwargs__ = kwargs
        self.__kwargs__['exiting'] = self.exiting
        self.__kwargs__['task'] = self

    @property
    def thread_pool(self):
        return self.__thread_pool__

    @property
    def id(self):
        return self.__task_id__

    @id.setter
    def id(self, value):
        self.__task_id__ = value

    @property
    def name(self):
        return self.__task_name__

    @name.setter
    def name(self, value):
        self.__task_name__ = value

    @property
    def function_name(self):
        return self.__function_name__

    @property
    def function(self):
        return self.__function__

    @property
    def command(self):
        return self.__command__

    @command.setter
    def command(self, value):
        self.__command__ = value

    @property
    def oci_profile(self):
        return self.__oci__profile__

    @property
    def args(self):
        return self.__args__

    @property
    def kwargs(self):
        return self.__kwargs__

    @property
    def status(self):
        return self.__status__

    @status.setter
    def status(self, value):
        self.__status__ = value

    @property
    def created_at(self):
        return self.__created_at__

    @property
    def start_time(self):
        return self.__start_time__

    @property
    def end_time(self):
        return self.__end_time__

    @end_time.setter
    def end_time(self, value):
        self.__end_time__ = value

    @property
    def exiting(self):
        return self.__exiting__

    @exiting.setter
    def exiting(self, value):
        self.__exiting__ = value

    def complete(self):
        logger.debug(f"task: {self.id}/{self.name} completed")
        self.status = "COMPLETED"
        self.end_time = datetime.now()

    def fail(self):
        self.status = "FAILED"
        self.end_time = datetime.now()

    def to_dict(self) -> dict:
        kwargs = self.kwargs
        if 'exiting' in kwargs:
            kwargs.pop('exiting')
        if 'task' in kwargs:
            kwargs.pop('task')
        for key, value in kwargs.items():
            if hasattr(value, 'to_dict') and callable(value.to_dict):
                kwargs[key] = value.to_dict()
            else:
                kwargs[key] = to_dict(value)

        return {
            'id': self.id,
            'name': self.name,
            'function_name': self.function_name,
            'command': self.command,
            'oci_profile': self.oci_profile,
            'args': self.args,
            'kwargs': kwargs,
            'status': self.status,
            'created_at': self.created_at.strftime("%Y-%m-%d %H:%M:%S"),
            'end_time': self.end_time.strftime("%Y-%m-%d %H:%M:%S") if self.end_time is not None else '',
        }

    def restart(self):
        return self.start()

    def abort(self):
        if self.status in ["ABORTED", "COMPLETED"]:
            return Status(http.client.OK, "Success", "Success")
        try:
            if not self.exiting.is_set():
                self.exiting.set()
                self.exiting.wait()
            self.status = "ABORTED"
            self.end_time = datetime.now()
            return Status(http.client.OK, "Success", "Success")
        except Exception as e:
            return Status(http.client.INTERNAL_SERVER_ERROR, "AbortTaskFailed", str(e))

    def stop(self) -> Status:
        if self.status in ["STOPPED", "FAILED", "COMPLETED", "ABORTED"]:
            return Status(http.client.OK, "Success", "Success")
        try:
            if not self.exiting.is_set():
                self.exiting.set()
                self.exiting.wait()
            self.end_time = datetime.now()
            self.status = "STOPPED"
            return Status(http.client.OK, "Success", "Success")
        except Exception as e:
            return Status(http.client.INTERNAL_SERVER_ERROR, "StopTaskFailed", str(e))

    def start(self) -> Status:
        self.__exiting__.clear()
        if self.thread_pool is None:
            self.__thread_pool__ = ThreadPoolExecutor(max_workers=1)
        try:
            self.thread_pool.submit(self.__start__)
            return Status(http.client.OK, "Success", "Success")
        except Exception as e:
            logger.error(f"fail to start task: {self.name}, details: {e}")
            self.status = "FAILED"
            self.end_time = datetime.now()
            return Status(http.client.INTERNAL_SERVER_ERROR, "StartTaskFailed", str(e))

    def __start__(self):
        self.__start_time__ = datetime.now()
        self.status = "RUNNING"
        try:
            self.function(**self.kwargs)
        except Exception as e:
            logger.error(f"fail to start task: {self.name}, details: {e}")
            self.status = "FAILED"
        finally:
            self.end_time = datetime.now()


class TelegramCommandBot:
    __thread_pool__ = None
    __oci_clients__ = None
    __telegram_bot__ = None
    __token__ = None
    __white_list_users__ = None
    __master_ssh_authorize_keys__ = None
    __users__ = {}
    __cloudflare__ = None
    __message_bot__ = None
    __config_file__: str = os.path.join(__base_dir__, "config")
    __tasks_file__: str = os.path.join(__base_dir__, "tasks.json")
    __key_dir__: str = os.path.join(__base_dir__, "keys")
    __tasks__: dict[str, Task] = {}
    __exiting__: threading.Event = threading.Event()

    @property
    def thread_pool(self):
        return self.__thread_pool__

    @thread_pool.setter
    def thread_pool(self, value):
        self.__thread_pool__ = value

    @property
    def oci_clients(self):
        return self.__oci_clients__

    @oci_clients.setter
    def oci_clients(self, value):
        self.__oci_clients__ = value

    def oci_client(self, oci_profile):
        return self.oci_clients.get(oci_profile)

    def add_oci_client(self, name, oci_client: OCIClient):
        if self.oci_clients is None:
            self.oci_clients = {}
        self.oci_clients[name] = oci_client

    @property
    def telegram_bot(self):
        return self.__telegram_bot__

    @telegram_bot.setter
    def telegram_bot(self, value):
        self.__telegram_bot__ = value

    @property
    def message_bot(self):
        return self.__message_bot__

    @message_bot.setter
    def message_bot(self, value):
        self.__message_bot__ = value

    @property
    def oci_config_file(self):
        return self.__oci_config_file__

    @oci_config_file.setter
    def oci_config_file(self, value):
        self.__oci_config_file__ = value

    @property
    def key_dir(self):
        return self.__key_dir__

    @key_dir.setter
    def key_dir(self, value):
        self.__key_dir__ = value

    @property
    def token(self):
        return self.__token__

    @token.setter
    def token(self, value):
        self.__token__ = value

    @property
    def whitelist(self):
        return self.__white_list_users__

    @whitelist.setter
    def whitelist(self, value):
        self.__white_list_users__ = value

    @property
    def users(self):
        return self.__users__

    @users.setter
    def users(self, value):
        self.__users__ = value

    @property
    def master_ssh_authorize_keys(self):
        return self.__master_ssh_authorize_keys__

    @master_ssh_authorize_keys.setter
    def master_ssh_authorize_keys(self, value):
        self.__master_ssh_authorize_keys__ = value

    @property
    def cloudflare(self):
        return self.__cloudflare__

    @cloudflare.setter
    def cloudflare(self, value):
        self.__cloudflare__ = value

    @property
    def config_file(self):
        return self.__config_file__

    @config_file.setter
    def config_file(self, value):
        self.__config_file__ = value

    @property
    def exiting(self):
        return self.__exiting__

    @property
    def tasks_file(self):
        return self.__tasks_file__

    @property
    def tasks(self):
        return self.__tasks__
    
    @property
    def semaphore(self):
        """Lazy initialization of semaphore (requires event loop)"""
        if self.__semaphore__ is None:
            try:
                # Try to get the running event loop
                loop = asyncio.get_running_loop()
                self.__semaphore__ = asyncio.Semaphore(self.__max_concurrent_oci_calls__)
                logger.debug(f"Initialized semaphore with {self.__max_concurrent_oci_calls__} max concurrent OCI calls")
            except RuntimeError:
                # No event loop running - this shouldn't happen during normal operation
                logger.warning("Attempted to create semaphore without event loop, creating new event loop")
                # Create a new event loop for this thread if needed
                try:
                    loop = asyncio.new_event_loop()
                    asyncio.set_event_loop(loop)
                    self.__semaphore__ = asyncio.Semaphore(self.__max_concurrent_oci_calls__)
                except Exception as e:
                    logger.error(f"Failed to create semaphore: {e}")
                    raise
        return self.__semaphore__
    
    def is_profile_ready(self, profile_name):
        """Check if a profile is warmed up and ready to use"""
        oci_client = self.oci_clients.get(profile_name)
        if oci_client is None:
            return False
        return oci_client.ready
    
    async def wait_for_profile_ready(self, profile_name, timeout=10.0):
        """Wait for a profile to be ready with timeout"""
        start_time = time.time()
        wait_interval = 0.1  # Check every 100ms
        
        while time.time() - start_time < timeout:
            if self.is_profile_ready(profile_name):
                return True
            await asyncio.sleep(wait_interval)
        
        # Timeout reached
        logger.warning(f"Timeout waiting for profile {profile_name} to be ready after {timeout}s")
        return False

    def _get_cached(self, key, ttl=None):
        """Get cached value if not expired"""
        if key in self.__cache__:
            timestamp, value = self.__cache__[key]
            if time.time() - timestamp < (ttl or self.__cache_ttl__):
                return value
        return None
    
    def _set_cache(self, key, value):
        """Set cache value with timestamp"""
        self.__cache__[key] = (time.time(), value)
    
    def _clear_cache(self, pattern=None):
        """Clear cache entries matching pattern, or all if pattern is None"""
        if pattern is None:
            self.__cache__.clear()
        else:
            keys_to_delete = [k for k in self.__cache__.keys() if pattern in k]
            for key in keys_to_delete:
                del self.__cache__[key]
    
    def _clear_profile_cache(self, profile_name):
        """Clear all cache entries for a specific OCI profile"""
        self._clear_cache(f"instances_{profile_name}")
        self._clear_cache(f"volumes_{profile_name}")
        self._clear_cache(f"boot_volumes_{profile_name}")
        self._clear_cache(f"live_check_{profile_name}")
        logger.debug(f"Cleared cache for profile: {profile_name}")
    
    def load_dead_profiles(self):
        """Load dead profiles from config file"""
        if not os.path.exists(self.oci_config_file):
            return
        
        try:
            config_parser = ConfigParser()
            with open(self.oci_config_file) as configfile:
                config_parser.read_file(configfile)
            
            dead_count = 0
            for section in config_parser.sections():
                dead_flag = config_parser.get(section, "dead", fallback="false").lower()
                if dead_flag == "true":
                    oci_client = self.oci_clients.get(section)
                    if oci_client:
                        # Mark as dead using the method
                        oci_client.mark_as_dead(dead=True)
                        dead_count += 1
                        logger.debug(f"Restored dead status for profile: {section}")
            
            if dead_count > 0:
                logger.info(f"Loaded {dead_count} dead profiles from config file")
        except Exception as e:
            logger.warning(f"Failed to load dead profiles from config: {e}")

    def register_and_start_tasks(self, task: Task) -> Status:
        self.__tasks__[task.id] = task
        return task.start()

    def stop_task(self, task_id: str) -> Status:
        task = self.__tasks__.get(task_id)
        if task is None:
            return Status(http.client.BAD_REQUEST, "NoTaskFound", f"Task not found: {task_id}")
        return task.stop()

    def save_tasks(self):
        to_save = [task.to_dict() for task in self.tasks.values()]
        # load and merge tasks
        if os.path.exists(self.tasks_file):
            with open(self.tasks_file, "r") as sf:
                existing_tasks = json.load(sf)
                to_save.extend(existing_tasks)
                # sort by task create_at desc
                to_save = sorted(to_save, key=lambda x: x['created_at'], reverse=True)

                seen = set()
                to_save = [x for x in to_save if x['id'] not in seen and not seen.add(x['id'])]

                # again unique by oci_profile and command
                seen = set()

                for task in to_save:
                    key = f"{task['oci_profile']}_{task['command']}"
                    if task['status'] in ['RUNNING', 'STOPPED', 'FAILED'] and key in seen:
                        logger.debug(f"found duplicated task: {task['id']} with command: {task['command']}, abort...")
                        task['status'] = 'ABORTED'  # abort duplicated task
                    else:
                        seen.add(key)

        with open(self.tasks_file, "w") as sf:
            json.dump(to_save, sf, indent=2)

    def add_whitelist(self, user_name):
        if self.whitelist is None:
            self.whitelist = []
        self.whitelist.append(user_name)

    def add_user(self, user: User):
        self.users[user.id] = User
        self.users[user.username] = User

    def get_user(self, uid: str):
        return self.users.get(uid)

    def allowed(self, update: Update) -> bool:
        user = update.effective_user
        username = user.username
        if user is None:
            return False
        # store user
        self.add_user(user)
        if self.whitelist is None:
            return False
        return username in self.whitelist

    def save_oci_config(self) -> Status:
        try:
            config_parser = ConfigParser()
            for oci_profile in sorted(self.oci_clients.keys()):
                oci_client = self.oci_clients.get(oci_profile)
                if oci_client is None:
                    continue
                c = oci_client.oci_config
                config_parser.add_section(oci_profile)
                config_parser.set(oci_profile, "user", c.user)
                config_parser.set(oci_profile, "fingerprint", c.fingerprint)
                config_parser.set(oci_profile, "key_file", c.key_file)
                config_parser.set(oci_profile, "tenancy", c.tenancy)
                config_parser.set(oci_profile, "region", c.region)
                if c.pass_phrase is not None:
                    config_parser.set(oci_profile, "pass_phrase", c.pass_phrase)
                # Save dead flag (default to false)
                if oci_client.is_dead:
                    config_parser.set(oci_profile, "dead", "true")
                else:
                    config_parser.set(oci_profile, "dead", "false")

            new_config_file = f"{self.oci_config_file}.new"
            with open(new_config_file, 'w') as configfile:  # save
                config_parser.write(configfile)
            # backup old config file
            if os.path.exists(self.oci_config_file):
                shutil.copyfile(self.oci_config_file, f"{self.oci_config_file}.bak")
            # replace config file
            shutil.move(new_config_file, self.oci_config_file)
            return Status(http.client.OK, "Success", "Success")
        except Exception as e:
            return Status(http.client.INTERNAL_SERVER_ERROR, "SaveOCIConfigFailed", str(e))
        finally:
            pass

    def submit(self, oci_profile, fn, **kwargs) -> Task | Status:
        oci_client = self.oci_client(oci_profile)
        if oci_client is None:
            return Status(http.client.BAD_REQUEST, "NoOCIProfile", f"OCI Profile not found: {oci_profile}")
        update = kwargs.get("update")
        task_id = kwargs.get("task_id")
        func = getattr(oci_client, fn)
        if func is None:
            return Status(http.client.BAD_REQUEST, "NoOCIFunction", f"OCI Function not found: {fn}")
        task_name = f"{func.__name__}"
        if update is not None:
            content = update.message.text
            message_id = update.message.message_id
            task_name = f"{update.effective_user.username}_{content.replace(' ', '_')}_{message_id}"

        task = Task(task_id=task_id,
                    task_name=task_name,
                    function=func,
                    function_name=fn,
                    command=update.message.text if update is not None else None,
                    oci_profile=oci_profile,
                    kwargs=kwargs)
        start_result = self.register_and_start_tasks(task=task)
        return task if is_success(start_result) else start_result

    def __init__(self, token,
                 thread_pool=None,
                 oci_clients=None,
                 whitelist=None,
                 master_ssh_authorize_keys=None,
                 cloudflare=None,
                 message_bot=None,
                 oci_config_file=".oci/config",
                 key_dir=None,
                 ):
        self.token = token
        self.thread_pool = thread_pool
        self.oci_clients = oci_clients
        self.whitelist = whitelist
        self.master_ssh_authorize_keys = master_ssh_authorize_keys
        self.cloudflare = cloudflare
        self.message_bot = message_bot
        self.oci_config_file = oci_config_file
        if key_dir is None:
            key_dir = os.path.join(__base_dir__, 'keys')
        self.key_dir = key_dir
        # Initialize cache for performance optimization
        self.__cache__ = {}
        self.__cache_ttl__ = 30  # Default TTL: 30 seconds
        # Semaphore will be lazily created on first use (needs event loop)
        self.__semaphore__ = None
        self.__max_concurrent_oci_calls__ = min(len(oci_clients) if oci_clients else 20, 30)

    def load_tasks(self):
        if not os.path.exists(self.tasks_file):
            logger.debug("no saved tasks found, skip loading...")
            return
        try:
            with open(self.tasks_file, "r") as sf:
                task_dicts = json.load(sf)
                for task_dict in task_dicts:
                    task_status = task_dict.get("status")
                    task_id = task_dict.get("id")
                    if task_status not in ["RUNNING", "STOPPED", "FAILED"]:
                        logger.debug(f"skip task: {task_id} with status: {task_status}")
                        continue
                    task_name = task_dict.get("name")
                    function_name = task_dict.get("function_name")
                    oci_profile = task_dict.get("oci_profile")
                    kwargs = task_dict.get("kwargs")
                    kwargs['task_id'] = task_id
                    kwargs['task_name'] = task_name
                    for k, v in kwargs.items():
                        if isinstance(v, dict):
                            class_name = snake_to_camel(k)
                            obj = globals()[class_name]
                            if hasattr(obj, 'de_json'):
                                obj = obj.de_json(v, self.telegram_bot.bot)
                                kwargs[k] = obj
                            elif hasattr(obj, 'from_dict'):
                                obj = obj.from_dict(v)
                                kwargs[k] = obj
                            elif obj is not None:
                                kwargs[k] = obj(**v)
                    result = self.submit(oci_profile, function_name, **kwargs)
                    if is_failed(result):
                        logger.warning(f"fail to load task: {task_id}, details: {result}")
                    else:
                        logger.debug(f"task: {task_id} loaded")
        except Exception as e:
            logger.warning(f"fail to load tasks, details: {e}")

    def flag(self, oci_profile):
        if oci_profile not in self.oci_clients.keys():
            return "🏴"
        return flag(self.oci_client(oci_profile).oci_config.region)

    def city(self, oci_profile):
        if oci_profile not in self.oci_clients.keys():
            return "Unknown"
        return city(self.oci_client(oci_profile).oci_config.region)

    def flagged_city(self, oci_profile):
        return f'{self.flag(oci_profile)} {self.city(oci_profile)}'

    def in_country(self, oci_profile, country_code) -> bool:
        if oci_profile not in self.oci_clients:
            return False
        oci_region = oci_regions.get(self.oci_client(oci_profile).oci_config.region)
        return in_country(oci_region, country_code)

    def warmup_connections_sync(self):
        """Pre-warm OCI connections by making a lightweight API call to each profile (synchronous version)"""
        logger.info(f"Starting background warmup for {len(self.oci_clients)} profiles...")
        
        def warmup_profile(profile_name):
            """Warm up a single profile's connection"""
            # Check if we're shutting down
            if self.exiting.is_set():
                logger.debug(f"Skipping warmup for {profile_name} - shutting down")
                return profile_name, False, "shutdown"
            
            try:
                oci_client = self.oci_clients.get(profile_name)
                if oci_client:
                    # Make a lightweight call - list_availability_domains is quick
                    oci_client.list_availability_domains()
                    
                    # Check if marked as dead during the call
                    if oci_client.is_dead:
                        logger.warning(f"💀 Profile {profile_name} marked as DEAD (auth failures: {oci_client.auth_failure_count})")
                        return profile_name, False, "dead"
                    
                    # Mark as ready first
                    oci_client.ready = True
                    # Now that we're ready, update the name (will call get_tenancy)
                    result = oci_client.name(skip_api_call=False)
                    
                    # Check again after get_tenancy call
                    if oci_client.is_dead:
                        logger.warning(f"💀 Profile {profile_name} marked as DEAD during name resolution")
                        oci_client.ready = False  # Not ready if dead
                        return profile_name, False, "dead"
                    
                    logger.debug(f"✓ Warmed up connection for {profile_name} (name: {oci_client.client_name})")
                    return profile_name, True, "success"
            except Exception as e:
                logger.warning(f"✗ Failed to warm up {profile_name}: {e}")
                # Keep ready = False (default)
                return profile_name, False, "error"
        
        # Warm up all profiles concurrently using thread pool
        try:
            futures = {self.thread_pool.submit(warmup_profile, profile): profile 
                       for profile in self.oci_clients.keys()}
            
            results = []
            for future in as_completed(futures):
                # Check if we're shutting down
                if self.exiting.is_set():
                    logger.info("Warmup interrupted - shutting down")
                    break
                
                try:
                    result = future.result()
                    results.append(result)
                except Exception as e:
                    profile = futures[future]
                    logger.warning(f"✗ Exception warming up {profile}: {e}")
                    results.append((profile, False, "exception"))
            
            # Count successes and dead profiles
            success_count = sum(1 for _, success, _ in results if success)
            dead_count = sum(1 for _, _, reason in results if reason == "dead")
            error_count = sum(1 for _, success, reason in results if not success and reason not in ["dead", "shutdown"])
            
            logger.info(f"Connection warmup complete: "
                       f"{success_count}/{len(self.oci_clients)} ready, "
                       f"{dead_count} dead (auth failures), "
                       f"{error_count} errors")
        except RuntimeError as e:
            # Handle case where interpreter is shutting down
            logger.warning(f"Warmup interrupted due to shutdown: {e}")

    async def post_init(self, application):
        """Called after the bot is initialized and event loop is running"""
        if len(self.oci_clients) > 0:
            logger.info(f"Bot initialized, starting background warmup for {len(self.oci_clients)} profiles...")
            # Start warmup as a background task
            asyncio.create_task(self._async_warmup())
    
    async def _async_warmup(self):
        """Async wrapper for warmup that runs in background without blocking"""
        try:
            # Wait a bit for bot to fully initialize
            await asyncio.sleep(0.5)
            logger.info("Starting background warmup...")
            # Get the running event loop
            loop = asyncio.get_running_loop()
            # Run warmup in executor to not block the event loop
            await loop.run_in_executor(
                None,  # Use default executor
                self.warmup_connections_sync
            )
        except Exception as e:
            logger.error(f"Error during warmup: {e}")
    
    def start(self):
        logger.info("starting telegram bot...")
        persistence = PicklePersistence(filepath=os.path.join(__base_dir__, ".bot"))
        # Build application - warmup will be handled via post_init
        try:
            builder = ApplicationBuilder().token(token=self.token).persistence(persistence=persistence)
            
            # Only add post_init if we have profiles to warm up
            if len(self.oci_clients) > 0:
                builder = builder.post_init(self.post_init)
                logger.info("post_init callback registered for warmup")
            
            self.telegram_bot = builder.build()
            logger.info("Telegram bot application built successfully")
        except Exception as e:
            import traceback
            logger.error(f"Failed to build telegram bot application: {e}")
            logger.error(f"Traceback: {traceback.format_exc()}")
            raise

        self.load_dead_profiles()
        
        self.load_tasks()
        add_profile_handler = ConversationHandler(
            entry_points=[CommandHandler("add_profile", self.start_add_profile_handler)],
            states={
                START_TO_ADD_PROFILE: [MessageHandler(filters.TEXT, self.start_add_profile_handler)],
                INPUT_PROFILE_DETAILS: [MessageHandler(filters.TEXT, self.input_profile_info_handler)],
                INPUT_PRIVATE_KEY: [MessageHandler(filters.TEXT, self.input_private_key_handler)],
                PASSPHRASE_REQUIRED: [MessageHandler(filters.TEXT, self.input_passphrase_handler)],
                DONE: [MessageHandler(filters.ALL, self.done_add_profile)],
                ConversationHandler.TIMEOUT: [MessageHandler(filters.ALL, self.done_add_profile)],
            },
            fallbacks=[CommandHandler("cancel", self.done_add_profile)],
            name="add_profile",
            persistent=True,
            conversation_timeout=180,
        )

        # on different commands - answer in Telegram
        self.telegram_bot.add_handler(TypeHandler(Update, self.permission_handler), group=-1)
        self.telegram_bot.add_handler(CommandHandler("tenancy", self.tenancy_handler))
        self.telegram_bot.add_handler(CommandHandler("instances", self.list_instances_handler))
        self.telegram_bot.add_handler(CommandHandler("profiles", self.list_profiles_handler))
        self.telegram_bot.add_handler(CommandHandler("delete_profiles", self.delete_profiles_handler))
        self.telegram_bot.add_handler(CommandHandler("mark_dead", self.mark_dead_handler))
        self.telegram_bot.add_handler(CommandHandler("volumes", self.list_volumes_handler))
        self.telegram_bot.add_handler(CommandHandler("attach_volume", self.volume_action_handler))
        self.telegram_bot.add_handler(CommandHandler("detach_volume", self.volume_action_handler))
        self.telegram_bot.add_handler(add_profile_handler)
        self.telegram_bot.add_handler(CommandHandler("change_ip", self.change_ip_handler))
        self.telegram_bot.add_handler(CommandHandler("allow_ports", self.add_security_rules_handler))
        self.telegram_bot.add_handler(CommandHandler("clear_security_lists", self.clear_security_rules_handler))
        self.telegram_bot.add_handler(CommandHandler("delete_ipv6s", self.delete_ipv6_handler))
        self.telegram_bot.add_handler(CommandHandler("dns_records", self.dns_records_handler))
        self.telegram_bot.add_handler(CommandHandler("cf_records", self.cf_records_handler))
        self.telegram_bot.add_handler(CommandHandler("add_cf_record", self.create_cf_record_handler))
        self.telegram_bot.add_handler(CommandHandler("create_cf_record", self.create_cf_record_handler))
        self.telegram_bot.add_handler(CommandHandler("update_cf_record", self.update_cf_record_handler))
        self.telegram_bot.add_handler(CommandHandler("delete_cf_records", self.delete_cf_record_handler))
        self.telegram_bot.add_handler(CommandHandler("rename_instance", self.rename_instance_handler))
        self.telegram_bot.add_handler(CommandHandler("create_instance", self.create_instance_handler))
        self.telegram_bot.add_handler(CommandHandler("resize_instance", self.resize_instance_handler))
        self.telegram_bot.add_handler(CommandHandler("create_console_connection",
                                                     self.create_console_connection_handler))
        self.telegram_bot.add_handler(CommandHandler("console_connections",
                                                     self.get_console_connection_handler))
        self.telegram_bot.add_handler(CommandHandler("console_connection",
                                                     self.get_or_create_console_connection_handler))
        self.telegram_bot.add_handler(CommandHandler("resize_boot_volume", self.resize_boot_volume_handler))
        self.telegram_bot.add_handler(CommandHandler("delete_instance", self.delete_instance_handler))
        self.telegram_bot.add_handler(CommandHandler("start_instance", self.start_instance_handler))
        self.telegram_bot.add_handler(CommandHandler("instance_action", self.instance_action_handler))
        self.telegram_bot.add_handler(CommandHandler("instance_details", self.instance_details_handler))
        self.telegram_bot.add_handler(CommandHandler("ping_instance", self.ping_instance_handler))
        self.telegram_bot.add_handler(CommandHandler("ping", self.ping_handler))
        self.telegram_bot.add_handler(CommandHandler("tasks", self.list_tasks_handler))
        self.telegram_bot.add_handler(CommandHandler("pause_task", self.pause_task_handler))
        self.telegram_bot.add_handler(CommandHandler("abort_task", self.abort_task_handler))
        self.telegram_bot.add_handler(CommandHandler("abandon_task", self.abort_task_handler))
        self.telegram_bot.add_handler(CommandHandler("start_task", self.start_task_handler))
        self.telegram_bot.add_handler(CommandHandler("sysinfo", self.sys_info_handler))
        self.telegram_bot.add_handler(CommandHandler("alive", self.alive_check_handler))
        # all other text messages and unknown commands
        self.telegram_bot.add_handler(MessageHandler(filters.TEXT & filters.COMMAND, self.help_handler))
        self.telegram_bot.add_handler(MessageHandler(filters.TEXT, self.help_handler))
        
        # Run the bot until the user presses Ctrl-C
        # Warmup will be triggered via post_init callback
        logger.info("starting polling...")
        
        try:
            # For python-telegram-bot v20+, we need to use async context
            # Create and set an event loop for the main thread
            try:
                loop = asyncio.get_running_loop()
                logger.info("Event loop already running")
            except RuntimeError:
                # No event loop in current thread, need to create one
                logger.info("Creating new event loop for main thread")
                loop = asyncio.new_event_loop()
                asyncio.set_event_loop(loop)
            
            # Now run_polling should work
            self.telegram_bot.run_polling(
                allowed_updates=Update.ALL_TYPES,
                stop_signals=[signal.SIGINT, signal.SIGTERM, signal.SIGABRT]
            )
        except Exception as e:
            import traceback
            logger.error(f"fail to start telegram bot, details: {e}")
            logger.error(f"Traceback: {traceback.format_exc()}")

        logger.info(f'Received Ctrl+C. Shutting down gracefully...')
        # stop all threads and tasks
        self.exiting.set()
        # stop all running tasks
        for task in self.tasks.values():
            result = task.stop()
            if is_failed(result):
                logger.warning(f"fail to stop task {task.name}, details: {result}")
            else:
                logger.info(f"task {task.name} stopped")
        self.save_tasks()
        self.save_oci_config()
        logger.info(f"telegram bot stopped")

    def profile_tasks(self, profile_name):
        return [task for task in self.tasks.values() if task.oci_profile == profile_name and task.status == "RUNNING"]

    def profile_instances(self, profile_name):
        oci_client = self.oci_client(profile_name)
        if oci_client is None:
            return Status(http.client.BAD_REQUEST,
                         "NoOCIProfile", f"OCI Profile not found: {profile_name}")
        # Skip dead profiles - no point making API calls
        if oci_client.is_dead:
            return Status(http.client.UNAUTHORIZED, "ProfileDead",
                         f"Profile marked as dead after {oci_client.auth_failure_count} auth failures")
        return oci_client.list_instances()

    async def list_instances(self, profile_name):
        """Run the synchronous OCI call in a thread for true async execution with caching and rate limiting"""
        # Check if profile is dead - return cached dead status
        oci_client = self.oci_client(profile_name)
        if oci_client and oci_client.is_dead:
            dead_status = Status(http.client.UNAUTHORIZED, "ProfileDead",
                                f"Profile marked as dead after {oci_client.auth_failure_count} auth failures")
            return profile_name, dead_status
        
        cache_key = f"instances_{profile_name}"
        cached = self._get_cached(cache_key, ttl=30)  # 30s cache
        if cached is not None:
            return profile_name, cached
        
        # Wait for profile to be ready if warmup is still in progress
        if not self.is_profile_ready(profile_name):
            logger.debug(f"Profile {profile_name} not ready yet, waiting...")
            ready = await self.wait_for_profile_ready(profile_name, timeout=10.0)
            if not ready:
                logger.warning(f"Profile {profile_name} still not ready after timeout, proceeding anyway")
        
        # Use semaphore to limit concurrent OCI API calls
        async with self.semaphore:
            instances = await asyncio.to_thread(self.profile_instances, profile_name)
            self._set_cache(cache_key, instances)
            return profile_name, instances

    async def list_volumes(self, profile_name, instance_id=None):
        """Run the synchronous OCI call in a thread for true async execution with caching and rate limiting"""
        # Check if profile is dead
        oci_client = self.oci_clients.get(profile_name)
        if oci_client is None:
            return profile_name, Status(http.client.BAD_REQUEST,
                                        "NoOCIProfile", f"OCI Profile not found: {profile_name}")
        if oci_client.is_dead:
            return profile_name, Status(http.client.UNAUTHORIZED, "ProfileDead",
                                       f"Profile marked as dead after {oci_client.auth_failure_count} auth failures")
        
        cache_key = f"volumes_{profile_name}_{instance_id}"
        cached = self._get_cached(cache_key, ttl=45)  # 45s cache
        if cached is not None:
            return profile_name, cached
        
        # Wait for profile to be ready if warmup is still in progress
        if not self.is_profile_ready(profile_name):
            logger.debug(f"Profile {profile_name} not ready yet, waiting...")
            ready = await self.wait_for_profile_ready(profile_name, timeout=10.0)
            if not ready:
                logger.warning(f"Profile {profile_name} still not ready after timeout, proceeding anyway")
        
        # Use semaphore to limit concurrent OCI API calls
        async with self.semaphore:
            volumes = await asyncio.to_thread(oci_client.list_volumes, instance_id=instance_id)
            self._set_cache(cache_key, volumes)
            return profile_name, volumes

    async def list_boot_volumes(self, profile_name, instance_id=None):
        """Run the synchronous OCI call in a thread for true async execution with caching and rate limiting"""
        # Check if profile is dead
        oci_client = self.oci_clients.get(profile_name)
        if oci_client is None:
            return profile_name, Status(http.client.BAD_REQUEST,
                                        "NoOCIProfile", f"OCI Profile not found: {profile_name}")
        if oci_client.is_dead:
            return profile_name, Status(http.client.UNAUTHORIZED, "ProfileDead",
                                       f"Profile marked as dead after {oci_client.auth_failure_count} auth failures")
        
        cache_key = f"boot_volumes_{profile_name}_{instance_id}"
        cached = self._get_cached(cache_key, ttl=45)  # 45s cache
        if cached is not None:
            return profile_name, cached

        # Wait for profile to be ready if warmup is still in progress
        if not self.is_profile_ready(profile_name):
            logger.debug(f"Profile {profile_name} not ready yet, waiting...")
            ready = await self.wait_for_profile_ready(profile_name, timeout=10.0)
            if not ready:
                logger.warning(f"Profile {profile_name} still not ready after timeout, proceeding anyway")

        # Use semaphore to limit concurrent OCI API calls
        async with self.semaphore:
            boot_volumes = await asyncio.to_thread(oci_client.list_boot_volumes, instance_id=instance_id)
            self._set_cache(cache_key, boot_volumes)
            return profile_name, boot_volumes

    async def volumes(self, profile_name, instance_id=None):
        result = await self.list_volumes(profile_name, instance_id)
        if isinstance(result, Status):
            return result
        _, volumes = result
        result = await self.list_boot_volumes(profile_name, instance_id)
        if isinstance(result, Status):
            return volumes

        _, boot_volumes = result
        return volumes + boot_volumes

    async def get_volumes(self, profile_name, volume_name) -> list[Volume] | Status:
        result = await self.list_volumes(profile_name)
        if isinstance(result, Status):
            return result

        _, volumes = result
        return [volume for volume in volumes if volume.display_name.upper() == volume_name.upper()]

    async def get_volume(self, profile_name, volume_name) -> Volume | Status:
        result = await self.get_volumes(profile_name, volume_name)
        if isinstance(result, Status):
            return result

        if len(result) == 0:
            return Status(http.client.BAD_REQUEST, "NoVolumeFound", f"volume {volume_name} not found")

        return result[0]

    def get_instance(self, profile_name, instance_name) -> Instance | Status:
        instances = self.profile_instances(profile_name)
        if isinstance(instances, Status):
            return instances
        for instance in instances:
            if (instance.display_name.upper() == instance_name.upper() and (
                    instance.lifecycle_state not in ["TERMINATED", "TERMINATING"])):
                return instance
        return Status(http.client.BAD_REQUEST, "NoOCIInstance",
                      f"instance {instance_name} not found in profile {profile_name}")

    async def tenancy(self, profile_name):
        """Run the synchronous OCI call in a thread for true async execution with caching and rate limiting"""
        # Check if profile is dead
        oci_client = self.oci_clients.get(profile_name)
        if oci_client is None:
            return profile_name, Status(http.client.BAD_REQUEST,
                                        "NoOCIProfile", f"OCI Profile not found: {profile_name}")
        if oci_client.is_dead:
            return profile_name, Status(http.client.UNAUTHORIZED, "ProfileDead",
                                       f"Profile marked as dead after {oci_client.auth_failure_count} auth failures")
        
        cache_key = f"tenancy_{profile_name}"
        cached = self._get_cached(cache_key, ttl=300)  # 5 min cache (tenancy rarely changes)
        if cached is not None:
            return profile_name, cached
        
        # Wait for profile to be ready if warmup is still in progress
        if not self.is_profile_ready(profile_name):
            logger.debug(f"Profile {profile_name} not ready yet, waiting...")
            ready = await self.wait_for_profile_ready(profile_name, timeout=10.0)
            if not ready:
                logger.warning(f"Profile {profile_name} still not ready after timeout, proceeding anyway")
        
        # Use semaphore to limit concurrent OCI API calls
        async with self.semaphore:
            tenancy = await asyncio.to_thread(oci_client.get_tenancy)
            self._set_cache(cache_key, tenancy)
            return profile_name, tenancy

    async def live_check(self, profile_name):
        """Run the synchronous OCI call in a thread for true async execution with caching and rate limiting"""
        cache_key = f"live_check_{profile_name}"
        cached = self._get_cached(cache_key, ttl=60)  # 60s cache for health checks
        if cached is not None:
            return cached
        
        oci_client = self.oci_clients.get(profile_name)
        if oci_client is None:
            result = (profile_name, '👻Not Found')
            self._set_cache(cache_key, result)
            return result
        
        # Check if already marked as dead
        if oci_client.is_dead:
            display_name = f'{self.flagged_city(profile_name)} - {profile_name}'
            result = (display_name, f'💀Dead ({oci_client.auth_failure_count} auth failures)')
            self._set_cache(cache_key, result)
            return result
        
        # Wait for profile to be ready if warmup is still in progress
        if not self.is_profile_ready(profile_name):
            logger.debug(f"Profile {profile_name} not ready yet, waiting...")
            ready = await self.wait_for_profile_ready(profile_name, timeout=10.0)
            if not ready:
                logger.warning(f"Profile {profile_name} still not ready after timeout, proceeding anyway")
        
        try:
            display_name = f'{self.flagged_city(profile_name)} - {profile_name}'
            # Use semaphore to limit concurrent OCI API calls and run in thread
            async with self.semaphore:
                check_result = await asyncio.to_thread(oci_client.list_instances)
            
            if isinstance(check_result, Status):
                logger.warning(f"fail to get instances for profile {display_name}, details: {check_result}")
                # Check if profile was marked dead
                if check_result.code == 'ProfileDead':
                    result = (display_name, f'💀Dead ({oci_client.auth_failure_count} auth failures)')
                elif ((check_result.status == http.client.NOT_FOUND and check_result.code == 'NotAuthorizedOrNotFound') or
                        (check_result.status == http.client.UNAUTHORIZED and check_result.code == 'NotAuthenticated')):
                    result = (display_name, '💀Dead')
                else:
                    result = (display_name, '☢️Danger')
            else:
                result = (display_name, '👍Alive')
            self._set_cache(cache_key, result)
            return result
        except Exception as ex:
            logger.warning(f"fail to get tenancy for profile {profile_name}, details: {ex}")
            result = (f'{self.flagged_city(profile_name)} - {profile_name}', '☢️Danger')
            self._set_cache(cache_key, result)
            return result

    async def alive_check(self, profiles: list[str] = None):
        if profiles is None:
            profiles = self.oci_clients.keys()
        tasks = [self.live_check(profile_name) for profile_name in profiles]
        return await asyncio.gather(*tasks)

    async def alive_check_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        profiles = context.args
        if len(profiles) == 0:
            profiles = self.oci_clients.keys()
        result = await self.alive_check(profiles=profiles)
        result = sorted(result, key=lambda x: x[0])
        
        if len(result) == 0:
            await update.message.reply_markdown_v2(
                text="No profiles found",
                reply_to_message_id=update.message.message_id)
            return
        
        # Calculate padding for alignment
        adjusted = max([len(profile_name) for profile_name, _ in result]) + 2
        
        # Paginate results (30 profiles per message to stay under Telegram's 4096 char limit)
        chunk_size = 30
        total_pages = (len(result) + chunk_size - 1) // chunk_size
        
        for page in range(total_pages):
            start_idx = page * chunk_size
            end_idx = min(start_idx + chunk_size, len(result))
            chunk = result[start_idx:end_idx]
            
            # Build message for this chunk
            message = f"*OCI Profile Status*"
            if total_pages > 1:
                message += f" \\(Page {page + 1}/{total_pages}\\)"
            message += ":\n"
            message += "```bash\n"
            for profile_name, status in chunk:
                message += f"{profile_name.ljust(adjusted)}: {status}\n"
            message += "```"
            
            # Send message (first message replies to original, others are new messages)
            if page == 0:
                await update.message.reply_markdown_v2(
                    text=message,
                    reply_to_message_id=update.message.message_id)
            else:
                await update.message.reply_markdown_v2(text=message)

    async def permission_handler(self, update: Update, _: ContextTypes.DEFAULT_TYPE) -> None:
        if update.message is None:
            return
        if update.message.chat.type == ChatType.GROUP:
            await update.message.reply_markdown_v2(text="please add me to your private chat",
                                                   reply_to_message_id=update.message.message_id)
            raise ApplicationHandlerStop(DONE)
        username = update.effective_user.username
        message = update.message.text
        logger.debug(f'received message from user: {username}, message: {redact(message)}')
        if not self.allowed(update):
            reply = (f'Hell, [{username}](tg://user?id={update.effective_user.id}), '
                     f'you are not allowed to use this bot, '
                     f'please contact @mysqto for access')
            await update.message.reply_markdown_v2(text=reply,
                                                   reply_to_message_id=update.message.message_id)
            raise ApplicationHandlerStop(DONE)

    @staticmethod
    async def sys_info_handler(update: Update, _: ContextTypes.DEFAULT_TYPE) -> None:
        cpu_count = psutil.cpu_count()
        cpu_info = cpuinfo.get_cpu_info()
        cpu_model = cpu_info.get('brand_raw')
        cpu_freq = cpu_info.get('hz_advertised_friendly')
        disks = psutil.disk_partitions(all=False)
        message = f"*System Info*:\n"
        message += f"```bash\n"
        message += f"Hostname     : {escape_markdown_v2(socket.gethostname())}\n"
        message += f"Up Time      : {uptime()}\n"
        message += f"CPU          : {escape_markdown_v2(cpu_count)} x {cpu_model} @ {cpu_freq}\n"
        message += f"Memory       : {escape_markdown_v2(readable_bytes(psutil.virtual_memory().total))}\n"
        message += f"Disk         : {escape_markdown_v2(readable_bytes(psutil.disk_usage('/').total))}\n"
        mount_point_adjust = max([len(disk.mountpoint) for disk in disks]) + 2
        dis_space_adjust = max([len(readable_bytes(psutil.disk_usage(disk.mountpoint).total)) for disk in disks]) + 2
        for disk in disks:
            if os.name == 'nt':
                if 'cdrom' in disk.opts or disk.fstype == '':
                    # skip cd-rom drives with no disk in it; they may raise
                    # ENOENT, pop-up a Windows GUI error for a non-ready
                    # partition or just hang.
                    continue

            usage = psutil.disk_usage(disk.mountpoint)
            message += (f"               {disk.mountpoint.ljust(mount_point_adjust)}"
                        f"{readable_bytes(usage.total).rjust(dis_space_adjust)}\n")
        message += f"```"
        await update.message.reply_markdown_v2(text=message,
                                               reply_to_message_id=update.message.message_id)

    async def list_tasks_handler(self, update: Update, _: ContextTypes.DEFAULT_TYPE) -> None:
        grouped_tasks = itertools.groupby(self.tasks.values(), key=lambda x: x.oci_profile)

        status_emojis = {
            "RUNNING": "🏃",
            "STOPPED": "🅿️",
            "COMPLETED": "✅",
            "FAILED": "❌",
            "UNKNOWN": "❓",
            "PAUSED": "⏸️",
        }

        message = f"*task list*:\n"
        for oci_profile, tasks in grouped_tasks:
            message += f"{self.flag(oci_profile)} `{escape_markdown_v2(oci_profile)}`:\n"
            for task in tasks:
                status = task.status
                status_emoji = status_emojis.get(status, "❓")
                task_command = task.command
                task_id = task.id
                message += (f"{status_emoji}`{escape_markdown_v2(task_id)}` : `{task_command}` \\-"
                            f" `{escape_markdown_v2(status)}`\n")

        await update.message.reply_markdown_v2(text=message,
                                               reply_to_message_id=update.message.message_id)

    async def abort_task_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if len(context.args) == 0:
            await update.message.reply_markdown_v2(text=f"task id is required",
                                                   reply_to_message_id=update.message.message_id)
            return

        task_id = context.args[0]
        task = self.tasks.get(task_id)
        if task is None:
            await update.message.reply_markdown_v2(text=f"task not found: {escape_markdown_v2(task_id)}",
                                                   reply_to_message_id=update.message.message_id)
            return

        if task.status in ["ABORTED", "COMPLETED"]:
            await update.message.reply_markdown_v2(text=f"task is already `completed` or `aborted`: "
                                                        f"`{escape_markdown_v2(task_id)}`",
                                                   reply_to_message_id=update.message.message_id)
            return

        result = task.abort()

        if is_failed(result):
            await update.message.reply_markdown_v2(text=f"fail to abort task: `{escape_markdown_v2(task_id)}`, "
                                                        f"details: {escape_markdown_v2(str(result))}",
                                                   reply_to_message_id=update.message.message_id)
            return

        await update.message.reply_markdown_v2(text=f"task aborted: `{escape_markdown_v2(task_id)}`",
                                               reply_to_message_id=update.message.message_id)

    async def pause_task_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if len(context.args) == 0:
            await update.message.reply_markdown_v2(text=f"task id is required",
                                                   reply_to_message_id=update.message.message_id)
            return

        task_id = context.args[0]
        task = self.tasks.get(task_id)
        if task is None:
            await update.message.reply_markdown_v2(text=f"task not found: {escape_markdown_v2(task_id)}",
                                                   reply_to_message_id=update.message.message_id)
            return

        if task.status != "RUNNING":
            await update.message.reply_markdown_v2(text=f"task is not running: {escape_markdown_v2(task_id)}",
                                                   reply_to_message_id=update.message.message_id)
            return

        result = task.stop()

        if is_failed(result):
            await update.message.reply_markdown_v2(text=f"fail to stop task: `{escape_markdown_v2(task_id)}`, "
                                                        f"details: {escape_markdown_v2(str(result))}",
                                                   reply_to_message_id=update.message.message_id)
            return

        await update.message.reply_markdown_v2(text=f"task paused: `{escape_markdown_v2(task_id)}`",
                                               reply_to_message_id=update.message.message_id)

    async def start_task_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if len(context.args) == 0:
            await update.message.reply_markdown_v2(text=f"task id is required",
                                                   reply_to_message_id=update.message.message_id)
            return

        task_id = context.args[0]
        task = self.tasks.get(task_id)
        if task is None:
            await update.message.reply_markdown_v2(text=f"task not found: {escape_markdown_v2(task_id)}",
                                                   reply_to_message_id=update.message.message_id)
            return

        if task.status != "STOPPED":
            await update.message.reply_markdown_v2(text=f"task is not stopped: `{escape_markdown_v2(task_id)}`",
                                                   reply_to_message_id=update.message.message_id)
            return

        result = task.start()

        if is_failed(result):
            await update.message.reply_markdown_v2(text=f"fail to stop task: `{escape_markdown_v2(task_id)}`, "
                                                        f"details: {escape_markdown_v2(str(result))}",
                                                   reply_to_message_id=update.message.message_id)
            return

        await update.message.reply_markdown_v2(text=f"task started: `{escape_markdown_v2(task_id)}`",
                                               reply_to_message_id=update.message.message_id)

    async def list_profiles_handler(self, update: Update, _: ContextTypes.DEFAULT_TYPE) -> None:
        oci_profiles = self.oci_clients.keys()

        profiles = []
        message = ""
        flagged_city_adjust = max([len(self.city(oci_profile)) for oci_profile in oci_profiles]) + 2
        tenancy_adjust = max([len(oci_profile) for oci_profile in oci_profiles]) + 2
        for oci_profile in oci_profiles:
            country_flag = self.flag(oci_profile)
            city_text = f'{self.city(oci_profile)}'
            tenancy_text = f'{escape_markdown_v2(oci_profile)}'
            spaces = " " * (flagged_city_adjust - len(city_text))
            profiles.append(f'''{country_flag}`{city_text}``{spaces}`: `{tenancy_text.rjust(tenancy_adjust)}`''')
        sorted_profiles = sorted(profiles)

        for i in range(0, len(oci_profiles), 24):
            if i == 0:
                message += f"*profile list*:\n"
            message = "\n".join(sorted_profiles[i:i + 24 if i + 24 < len(oci_profiles) else len(oci_profiles)]) + "\n"
            await update.message.reply_markdown_v2(text=message,
                                                   reply_to_message_id=update.message.message_id)

    async def delete_profiles_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if len(context.args) == 0:
            await update.message.reply_markdown_v2(
                text=f'profile(s) name is(are) required, please input the profile name(s) to delete',
                reply_to_message_id=update.message.message_id)
            return

        profiles = context.args

        for profile in profiles:
            if profile not in self.oci_clients.keys():
                await update.message.reply_markdown_v2(
                    text=f'profile `{escape_markdown_v2(profile)}` not found',
                    reply_to_message_id=update.message.message_id)
                continue
            # abort all running tasks
            tasks = self.profile_tasks(profile)
            for task in tasks:
                task.abort()
            # delete oci client
            oci_client = self.oci_clients.get(profile)
            if oci_client is not None:
                private_key_file = oci_client.oci_config.key_file
                if private_key_file is not None:
                    # delete the private key file
                    os.remove(private_key_file)
            # delete oci config
            del self.oci_clients[profile]
            self.save_oci_config()
            message = f'profile `{escape_markdown_v2(profile)}` deleted'
            if len(tasks) > 0:
                message += f', {len(tasks)} tasks aborted'
            await update.message.reply_markdown_v2(text=message,
                                                   reply_to_message_id=update.message.message_id)

    async def mark_dead_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        """Mark or unmark a profile as dead/not dead
        
        Usage: /mark_dead <profile_name> <dead|alive|true|false>
        """
        if len(context.args) < 2:
            await update.message.reply_markdown_v2(
                text=f'Usage: `/mark\\_dead` `<profile\\_name>` `<dead|alive|true|false>`\n'
                     f'Example: `/mark\\_dead` `my\\_profile` `dead`',
                reply_to_message_id=update.message.message_id)
            return
        
        profile_name = context.args[0]
        status_arg = context.args[1].lower()
        
        # Parse status argument
        if status_arg in ['dead', 'true', '1', 'yes']:
            mark_as_dead = True
        elif status_arg in ['alive', 'false', '0', 'no']:
            mark_as_dead = False
        else:
            await update.message.reply_markdown_v2(
                text=f'Invalid status: `{escape_markdown_v2(status_arg)}`\n'
                     f'Use: `dead`, `alive`, `true`, or `false`',
                reply_to_message_id=update.message.message_id)
            return
        
        # Check if profile exists
        if profile_name not in self.oci_clients.keys():
            await update.message.reply_markdown_v2(
                text=f'profile `{escape_markdown_v2(profile_name)}` not found',
                reply_to_message_id=update.message.message_id)
            return
        
        oci_client = self.oci_clients.get(profile_name)
        if oci_client is None:
            await update.message.reply_markdown_v2(
                text=f'profile `{escape_markdown_v2(profile_name)}` client not found',
                reply_to_message_id=update.message.message_id)
            return
        
        # Update dead status using the method
        oci_client.mark_as_dead(dead=mark_as_dead)
        
        if mark_as_dead:
            status_text = "☠️ DEAD"
            action_text = "marked as dead"
        else:
            status_text = "✅ ALIVE"
            action_text = "marked as alive"
        
        # Save config immediately
        save_result = self.save_oci_config()
        if is_failed(save_result):
            await update.message.reply_markdown_v2(
                text=f'profile `{escape_markdown_v2(profile_name)}` {action_text}, '
                     f'but failed to save config: `{escape_markdown_v2(str(save_result))}`',
                reply_to_message_id=update.message.message_id)
            return
        
        # Send confirmation
        await update.message.reply_markdown_v2(
            text=f'profile `{escape_markdown_v2(profile_name)}` {action_text} {status_text}\n'
                 f'Config saved successfully',
            reply_to_message_id=update.message.message_id)

    @staticmethod
    async def start_add_profile_handler(update: Update, _: ContextTypes.DEFAULT_TYPE) -> int:
        user_name = update.effective_user.username
        user_id = update.effective_user.id
        message = f'Hello, [@{user_name}](tg://user?id={user_id})\n' \
                  f'please input the profile details in the following format' \
                  f'\\(remove the `key_file=xxx` when you copy from OCI Console\\):\n' \
                  f'```bash\n' \
                  f'[profile_name]\n' \
                  f'{escape_markdown_v2("user = <user_ocid>")}\n' \
                  f'{escape_markdown_v2("fingerprint = <fingerprint>")}\n' \
                  f'{escape_markdown_v2("tenancy = <tenancy_ocid>")}\n' \
                  f'{escape_markdown_v2("region = <region>")}\n' \
                  f'```'
        await update.message.reply_markdown_v2(text=message, reply_to_message_id=update.message.message_id)
        return INPUT_PROFILE_DETAILS

    async def to_cancel(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        user_input = update.message.text.strip()
        if user_input.lower() == '/cancel':
            await self.done_add_profile(update, context)
            raise ApplicationHandlerStop(DONE)

    async def input_profile_info_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
        await self.to_cancel(update=update, context=context)
        user_input = update.message.text.strip()
        if not user_input.startswith('[') and ']' not in user_input:
            user_input = f"[{str(uuid.uuid4())}]\n{user_input}"

        # try to parse use ConfigParser
        parser = ConfigParser()
        try:
            parser.read_string(user_input)
            if len(parser.sections()) == 0:
                await update.message.reply_markdown_v2(text=f"no profile found",
                                                       reply_to_message_id=update.message.message_id)
                return INPUT_PROFILE_DETAILS

            if len(parser.sections()) > 1:
                await update.message.reply_markdown_v2(text=f"only one profile is supported",
                                                       reply_to_message_id=update.message.message_id)
                return INPUT_PROFILE_DETAILS
        except Exception as ex:
            await update.message.reply_markdown_v2(text=f"invalid profile, details: {escape_markdown_v2(str(ex))}",
                                                   reply_to_message_id=update.message.message_id)
            return INPUT_PROFILE_DETAILS

        section = parser[parser.sections()[0]]
        oci_user = section.get('user')
        oci_fingerprint = section.get('fingerprint')
        oci_tenancy = section.get('tenancy')
        region = section.get('region')
        errors = []
        if oci_user is None or not oci_user.startswith('ocid1.user'):
            errors.append(f'invalid oci user, '
                          f'should be like: `{escape_markdown_v2("user = ocid1.user.oc1..aaaaaaa...")}`')
        if oci_fingerprint is None or oci_fingerprint.count(":") != 15:
            errors.append(f'invalid oci fingerprint, '
                          f'should be like: '
                          f'`{escape_markdown_v2("fingerprint = 12:34:56:78:90:ab:cd:ef:12:34:56:78:90:ab:cd:ef")}`')
        if oci_tenancy is None or not oci_tenancy.startswith('ocid1.tenancy'):
            errors.append(f'invalid oci tenancy, '
                          f'should be like: `{escape_markdown_v2("tenancy = ocid1.tenancy.oc1..aaaaaaa...")}`')
        if region is None or region not in oci_regions:
            errors.append(f"invalid region, should be one of: {pretty(list(oci_regions.keys()))}")

        if len(errors) > 0:
            message = f'invalid profile:\n'
            for error in errors:
                message += f'  •  {error}\n'
            await update.message.reply_markdown_v2(text=message, reply_to_message_id=update.message.message_id)
            return INPUT_PROFILE_DETAILS

        context.user_data['oci_user'] = oci_user
        context.user_data['oci_fingerprint'] = oci_fingerprint
        context.user_data['oci_tenancy'] = oci_tenancy
        context.user_data['region'] = region
        context.user_data['profile_message_id'] = update.message.message_id
        context.user_data['private_key'] = None
        message = f'please input the private key file content in the following format:\n' \
                  f'```bash\n' \
                  f'-----BEGIN PRIVATE KEY-----\n' \
                  f'...\n' \
                  f'-----END PRIVATE KEY-----\n' \
                  f'```'
        await update.message.reply_markdown_v2(text=message, reply_to_message_id=update.message.message_id)

        return INPUT_PRIVATE_KEY

    @staticmethod
    async def validate_key(update: Update, context: ContextTypes.DEFAULT_TYPE, step=INPUT_PRIVATE_KEY) -> int:
        key_text = context.user_data.get('private_key')
        if step == INPUT_PRIVATE_KEY:
            key_text = update.message.text.strip()
        if key_text is None:
            await update.message.reply_markdown_v2(text=f"private key not found, please input the private key",
                                                   reply_to_message_id=update.message.message_id)
            return INPUT_PRIVATE_KEY
        pass_phrase = context.user_data.get('pass_phrase')
        if step == PASSPHRASE_REQUIRED:
            pass_phrase = update.message.text.strip()
            if pass_phrase is None:
                await update.message.reply_markdown_v2(text=f"pass phrase not found, please input the pass phrase",
                                                       reply_to_message_id=update.message.message_id)
                return PASSPHRASE_REQUIRED
        # try to parse the key
        try:
            _ = signer.load_private_key(secret=key_text, pass_phrase=pass_phrase)
            context.user_data['private_key'] = key_text
            context.user_data['pass_phrase'] = pass_phrase
            if step == INPUT_PRIVATE_KEY:
                context.user_data['private_key_message_id'] = update.message.message_id
            if step == PASSPHRASE_REQUIRED:
                context.user_data['pass_phrase_message_id'] = update.message.message_id
            await update.message.reply_markdown_v2(text=f"private key validated, please wait\\.\\.\\.",
                                                   reply_to_message_id=update.message.message_id)
            return KEY_VALIDATED
        except MissingPrivateKeyPassphrase:
            await update.message.reply_markdown_v2(text=f"private key passphrase required, "
                                                        f"please input the passphrase",
                                                   reply_to_message_id=update.message.message_id)
            context.user_data['private_key'] = key_text
            context.user_data['private_key_message_id'] = update.message.message_id
            return PASSPHRASE_REQUIRED
        except InvalidPrivateKey as ipe:
            key = 'private key' if step == INPUT_PRIVATE_KEY else 'passphrase'
            await update.message.reply_markdown_v2(
                text=f"invalid {key}, details: `{escape_markdown_v2(str(ipe))}`, "
                     f"please input the {key} again:",
                reply_to_message_id=update.message.message_id)
            return step
        except Exception as gex:
            await update.message.reply_markdown_v2(
                text=f"invalid private key, details: `{escape_markdown_v2(str(gex))}`, "
                     f"please input the private key again: ",
                reply_to_message_id=update.message.message_id)
            return INPUT_PRIVATE_KEY

    async def add_profile(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
        oci_user = context.user_data.get('oci_user')
        oci_fingerprint = context.user_data.get('oci_fingerprint')
        oci_tenancy = context.user_data.get('oci_tenancy')
        oci_region = context.user_data.get('region')
        private_key = context.user_data.get('private_key')
        pass_phrase = context.user_data.get('pass_phrase')

        key_file_path = os.path.join(self.key_dir, f"{uuid.uuid4()}.pem")
        key_dir = os.path.dirname(key_file_path)
        if not os.path.exists(key_dir):
            os.makedirs(key_dir, exist_ok=True)
        try:
            with open(key_file_path, "w") as key_file:
                key_file.write(private_key)
                os.chmod(key_file_path, 0o600)
                context.user_data['key_file_path'] = key_file_path
            await update.message.reply_markdown_v2(text=f"private key saved to `{key_file_path}`,"
                                                        f" please keep it safe",
                                                   reply_to_message_id=update.message.message_id)
        except Exception as ex:
            await update.message.reply_markdown_v2(text=f"fail to save private key to "
                                                        f"{key_file_path}, details: "
                                                        f"`{escape_markdown_v2(str(ex))}`",
                                                   reply_to_message_id=update.message.message_id)
            return await self.done_add_profile(update, context)
        finally:
            pass

        # everything should be ready
        try:
            oci_config = OciConfig(user=oci_user, fingerprint=oci_fingerprint, tenancy=oci_tenancy, region=oci_region,
                                   key_file=key_file_path, pass_phrase=pass_phrase)
        except Exception as ex:
            await update.message.reply_markdown_v2(text=f"fail to create oci config, details: "
                                                        f"`{escape_markdown_v2(str(ex))}`",
                                                   reply_to_message_id=update.message.message_id)
            return await self.done_add_profile(update, context)

        ocli = OCIClient(config=oci_config,
                         thread_pool=self.thread_pool,
                         ssh_authorized_keys=self.master_ssh_authorize_keys,
                         cloudflare=self.cloudflare,
                         telegram_bot=self.message_bot)
        tenancy = ocli.get_tenancy()
        if isinstance(tenancy, Status):
            await update.message.reply_markdown_v2(
                text=f"fail to login to OCI, details: `{escape_markdown_v2(str(tenancy))}`",
                reply_to_message_id=update.message.message_id)
            return await self.done_add_profile(update, context)
        self.oci_clients[tenancy.name] = ocli

        result = self.save_oci_config()

        if is_failed(result):
            await update.message.reply_markdown_v2(
                text=f'OCI profile `{escape_markdown_v2(tenancy.name)}` added '
                     f'successfully, but fail to save to config file, '
                     f'details: `{escape_markdown_v2(str(result))}`'
                     f'you still can operate the profile, '
                     f'but you will lose everything after bot restarts',
                reply_to_message_id=update.message.message_id)

        else:
            await update.message.reply_markdown_v2(
                text=f"OCI profile `{escape_markdown_v2(tenancy.name)}` added"
                     f" successfully, "
                     f"please use `/instances {escape_markdown_v2(tenancy.name)}` "
                     f"to list instances",
                reply_to_message_id=update.message.message_id)
        context.user_data['done'] = True
        return await self.done_add_profile(update, context)

    @staticmethod
    async def done_add_profile(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
        done = context.user_data.get('done')
        if done is None or not done:
            await update.message.reply_markdown_v2(
                text=f"profile not added",
                reply_to_message_id=update.message.message_id)
            key_file_path = context.user_data.get('key_file_path')
            if key_file_path is not None and os.path.exists(key_file_path):
                os.remove(key_file_path)

        # delete all messages
        profile_message_id = context.user_data.get('profile_message_id')
        if profile_message_id is not None:
            await context.bot.delete_message(chat_id=update.message.chat_id,
                                             message_id=profile_message_id)

        private_key_message_id = context.user_data.get('private_key_message_id')
        if private_key_message_id is not None:
            await context.bot.delete_message(chat_id=update.message.chat_id,
                                             message_id=private_key_message_id)
        pass_phrase_message_id = context.user_data.get('pass_phrase_message_id')
        if pass_phrase_message_id is not None:
            await context.bot.delete_message(chat_id=update.message.chat_id,
                                             message_id=pass_phrase_message_id)

        # clear context
        context.user_data.clear()
        return DONE

    async def input_private_key_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
        await self.to_cancel(update=update, context=context)
        key_text = update.message.text.strip()
        if (not (key_text.startswith('-----BEGIN PRIVATE KEY-----') and
                 key_text.endswith('-----END PRIVATE KEY-----')) and
                not (key_text.startswith('-----BEGIN ENCRYPTED PRIVATE KEY-----') and
                     key_text.endswith('-----END ENCRYPTED PRIVATE KEY-----'))):
            await update.message.reply_markdown_v2(
                text=f"invalid private key, private key should start with "
                     f"`{escape_markdown_v2('-----BEGIN (ENCRYPTED) PRIVATE KEY-----')}` "
                     f"and end with "
                     f"`{escape_markdown_v2('-----END (ENCRYPTED) PRIVATE KEY-----')}`",
                reply_to_message_id=update.message.message_id)
            return INPUT_PRIVATE_KEY
        result = await self.validate_key(update, context, step=INPUT_PRIVATE_KEY)
        if result in [INPUT_PRIVATE_KEY, PASSPHRASE_REQUIRED]:
            return result

        return await self.add_profile(update, context)

    async def input_passphrase_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
        await self.to_cancel(update=update, context=context)
        result = await self.validate_key(update, context, step=PASSPHRASE_REQUIRED)
        if result in [INPUT_PRIVATE_KEY, PASSPHRASE_REQUIRED]:
            return result

        return await self.add_profile(update, context)

    async def tenancy_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        profiles = context.args if len(context.args) > 0 else self.oci_clients.keys()
        tasks = [self.tenancy(profile) for profile in profiles]
        results = await asyncio.gather(*tasks, return_exceptions=True)

        message = f"*Tenancy*:\n"
        for result in results:
            profile_name, tenancy = result
            message += f"{self.flag(profile_name)} `{profile_name}`:\n"
            if isinstance(tenancy, Status):
                message += f"  •  fail to get tenancy: `{escape_markdown_v2(str(result))}`\n"
                continue
            message += f"```bash\n"
            message += f"  •  id: {tenancy.id}\n"
            message += f"  •  name: {tenancy.name}\n"
            message += f"  •  home region: {tenancy.home_region_key}\n"
            message += f"```\n"
        await update.message.reply_markdown_v2(text=message, reply_to_message_id=update.message.message_id)

    async def list_instances_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        oci_profiles = context.args
        not_found = []
        if oci_profiles is None or len(oci_profiles) == 0:
            oci_profiles = self.oci_clients.keys()
        else:
            not_found = [oci_profile for oci_profile in oci_profiles if oci_profile not
                         in self.oci_clients.keys() and not is_country_code(oci_profile)]

            countries = [oci_profile for oci_profile in oci_profiles if is_country_code(oci_profile)]

            if len(countries) > 0:
                for country in countries:
                    oci_profiles.remove(country)
                    profiles = [oci_profile for oci_profile in
                                self.oci_clients.keys() if self.in_country(oci_profile, country)]
                    if len(profiles) > 0:
                        oci_profiles.extend(profiles)
                    else:
                        not_found.append(country)

            # remove all duplicates
            oci_profiles = list(set(oci_profiles))

        if len(not_found) > 0:
            await update.message.reply_markdown_v2(
                text=f"profile not found: {markdown_list(not_found)}",
                reply_to_message_id=update.message.message_id)
        if len(not_found) == len(oci_profiles):
            return

        tasks = [self.list_instances(oci_profile) for oci_profile in oci_profiles]
        results = await asyncio.gather(*tasks, return_exceptions=True)
        # sort result by flag order
        results = sorted(results, key=lambda x: f'{self.flagged_city(x[0])}{x[0]}')
        # group results by 5
        for i in range(0, len(results), 5):
            current_results = results[i:i + 5 if i + 5 < len(results) else len(results)]
            message = f"Instances:\n"
            for result in current_results:
                oci_profile, instances = result
                oci_client = self.oci_clients.get(oci_profile)
                message += f"*`{self.flagged_city(oci_profile)} \\- {escape_markdown_v2(oci_profile)}`*\n"
                if isinstance(instances, Status):
                    message += f"  •  fail to load instances: `{escape_markdown_v2(str(instances))}`\n"
                    continue

                profile_tasks = self.profile_tasks(oci_profile)

                if len(instances) == 0:
                    message += "no instance found, use `/create_instance` to create one\n"
                    if profile_tasks is not None and len(profile_tasks) > 0:
                        message += "🤖running tasks:\n"
                        for task in profile_tasks:
                            message += f"🏃`{escape_markdown_v2(task.command)}`\n"
                    continue

                status_emojis = {
                    'RUNNING': '✅',
                    'STARTING': '⌛',
                    'STOPPING': '🛑',
                    'STOPPED': '🛑',
                    'TERMINATING': '❌',
                    'TERMINATED': '❌',
                    'PROVISIONING': '⌛️',
                    'CREATING_IMAGE': '⌛',
                }

                message += "```bash\n"
                for instance in instances:
                    status = instance.lifecycle_state
                    if status in ['TERMINATED', 'TERMINATING']:
                        continue
                    name = instance.display_name
                    icon = status_emojis[status]
                    primary_ip_v4 = oci_client.get_primary_ipv4(instance.id)
                    cpu_cores = int(instance.shape_config.ocpus)
                    memory_in_gbs = int(instance.shape_config.memory_in_gbs)
                    shap_config = f"{cpu_cores}C{memory_in_gbs}G"
                    status_text = f"{icon}{status}{icon}"
                    created_at = instance.time_created.strftime("%Y-%m-%d")
                    message += f"{name:10s} {shap_config:10s} ({primary_ip_v4:15s}) {created_at} {status_text:10s}\n"

                message += "```\n"
                if profile_tasks is not None and len(profile_tasks) > 0:
                    message += "🤖running tasks:\n"
                    for task in profile_tasks:
                        message += f"🏃`{escape_markdown_v2(task.command)}`\n"
            await update.message.reply_markdown_v2(text=message, reply_to_message_id=update.message.message_id)

    async def volume_action_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        action = update.message.text.strip().split(" ")[0].lower()
        action = action.replace("/", "").replace("_volume", "")
        if len(context.args) < 3:
            await update.message.reply_markdown_v2(
                text=f"parameter error: `/{action}_volume <profile> <instance_name> <volume_name>`",
                reply_to_message_id=update.message.message_id)
            return

        profile_name = context.args[0]
        instance_name = context.args[1]
        volume_name = context.args[2]

        instance = self.get_instance(profile_name, instance_name)
        if isinstance(instance, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get instance `{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(instance))}`',
                reply_to_message_id=update.message.message_id)
            return

        if instance.lifecycle_state not in ['RUNNING', 'STOPPED']:
            await update.message.reply_markdown_v2(
                text=f'instance `{escape_markdown_v2(instance_name)}` is not running or stopped, '
                     f'can not attach volume',
                reply_to_message_id=update.message.message_id)
            return

        volume = await self.get_volume(profile_name, volume_name)

        if isinstance(volume, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get volume `{escape_markdown_v2(volume_name)}`, '
                     f'details: `{escape_markdown_v2(str(volume))}`',
                reply_to_message_id=update.message.message_id)
            return

        result = self.submit(oci_profile=profile_name, fn='volume_action_task',
                             instance=instance, volume=volume, action=action, update=update)
        if isinstance(result, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to submit task for instance `{escape_markdown_v2(instance_name)}` '
                     f'to `{action}` volume `{escape_markdown_v2(volume_name)}`, '
                     f'details: `{escape_markdown_v2(str(result))}`',
                reply_to_message_id=update.message.message_id)
            return

        await update.message.reply_markdown_v2(
            text=f'task submitted for instance `{escape_markdown_v2(instance_name)}` '
                 f'to `{action}` volume `{escape_markdown_v2(volume_name)}`, '
                 f'task id: `{escape_markdown_v2(result.id)}`',
            reply_to_message_id=update.message.message_id)

    async def list_volumes_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        profiles = context.args
        if profiles is None or len(profiles) == 0:
            profiles = self.oci_clients.keys()

        not_found = [profile for profile in profiles if profile not in self.oci_clients.keys()]
        if not_found is not None and len(not_found) > 0:
            await update.message.reply_markdown_v2(
                text=f"profile not found: {markdown_list(not_found)}",
                reply_to_message_id=update.message.message_id)

        if len(not_found) == len(profiles):
            return

        tasks = [self.list_volumes(profile) for profile in profiles]

        results = await asyncio.gather(*tasks, return_exceptions=True)

        message = f"Volumes:\n"
        for profile, result in results:
            message += f"{self.flag(profile)} *{escape_markdown_v2(profile)}*\n"
            if isinstance(result, Status):
                message += f"  •  fail to load volumes {escape_markdown_v2(str(result))}\n"
                continue

            volumes = result
            if len(volumes) == 0:
                message += "  •  no volume found\n"
                continue
            message += "```bash\n"
            name_adjust = max([len(volume.display_name) for volume in volumes]) + 2
            size_adjust = max([len(readable_size(volume.size_in_mbs, base_unit='MB')) for volume in volumes]) + 2
            for volume in volumes:
                name = volume.display_name
                size_readable = readable_size(volume.size_in_mbs, base_unit='MB')
                message += f"{name.ljust(name_adjust)} {size_readable.rjust(size_adjust)}\n"
            message += "```\n"
            await update.message.reply_markdown_v2(text=message, reply_to_message_id=update.message.message_id)

    async def resize_boot_volume_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if context.args is None or len(context.args) < 3:
            await update.message.reply_markdown_v2(
                text=f"parameter error: `/resize_boot_volume <profile> <instance_name> <size_in_gbs>`",
                reply_to_message_id=update.message.message_id)
            return

        profile_name = context.args[0]
        instance_name = context.args[1]
        size_in_gbs = context.args[2].upper()
        size_in_gbs = size_in_gbs.replace("GB", "").replace("G", "")  # remove GB or G

        if not size_in_gbs.isdigit():
            await update.message.reply_markdown_v2(
                text=f"size_in_gbs should be a number",
                reply_to_message_id=update.message.message_id)
            return

        size_in_gbs = int(size_in_gbs)
        vpus_per_gb = None
        if len(context.args) > 3:
            vpus_per_gb = int(context.args[3])
            if vpus_per_gb < 10 or vpus_per_gb > 120 or not vpus_per_gb % 10 == 0:
                await update.message.reply_markdown_v2(
                    text=f"vpus_per_gb should be between 10 and 120 and multiple of 10",
                    reply_to_message_id=update.message.message_id)
                return

        instance = self.get_instance(profile_name, instance_name)
        if isinstance(instance, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get instance `{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(instance))}`',
                reply_to_message_id=update.message.message_id)
            return

        if instance.lifecycle_state not in ['RUNNING', 'STOPPED']:
            await update.message.reply_markdown_v2(
                text=f'instance `{escape_markdown_v2(instance_name)}` is not running or stopped, '
                     f'can not resize boot volume',
                reply_to_message_id=update.message.message_id)
            return

        oci_client = self.oci_client(profile_name)

        boot_volumes = oci_client.list_boot_volumes(instance.id)
        if isinstance(boot_volumes, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get boot volume for instance `{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(boot_volumes))}`',
                reply_to_message_id=update.message.message_id)
            return

        # should only have one boot volume
        boot_volume = boot_volumes[0]

        current_size_in_gbs = int(boot_volume.size_in_gbs)
        if current_size_in_gbs >= size_in_gbs:
            await update.message.reply_markdown_v2(
                text=f'new `size_in_gbs` should be larger than current size: '
                     f'{escape_markdown_v2(current_size_in_gbs)}GB',
                reply_to_message_id=update.message.message_id)
            return

        result = oci_client.update_boot_volume(boot_volume.id, size_in_gbs=size_in_gbs, vpus_per_gb=vpus_per_gb)
        if isinstance(result, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to update boot volume for instance `{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(result))}`',
                reply_to_message_id=update.message.message_id)
            return
        await update.message.reply_markdown_v2(
            text=f'boot volume for instance `{escape_markdown_v2(instance_name)}` is updating, '
                 f'please wait',
            reply_to_message_id=update.message.message_id)

    async def resize_instance_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:

        if context.args is None or len(context.args) < 3:
            await update.message.reply_markdown_v2(
                text=f"parameter error: `/resize_instance <profile> <instance_name> <shape_config>`",
                reply_to_message_id=update.message.message_id)
            return

        oci_profile = context.args[0]
        instance_name = context.args[1]
        shape_config = context.args[2]

        # shape_config should be like: "1C2G" or `1C` or `2G` or 2G1C, only cpu or memory is supported
        shape_config_regex = r'^(\d+C\d*G|\d*G\d+C|\d+C|\d*G)$'
        match = re.match(shape_config_regex, shape_config)
        if match is None:
            await update.message.reply_markdown_v2(
                text=f"invalidate shape config: `{escape_markdown_v2(shape_config)}`, "
                     f"should be like: `1C2G` or `1C` or `2G`",
                reply_to_message_id=update.message.message_id)
            return

        # try to extract cpu and memory_in_gbs from shape_config
        cpu_cores = None
        memory_in_gbs = None
        # 2C4G -> cpu=2, memory_in_gbs=4
        # 2G   -> cpu=,  memory_in_gbs=2
        # 2C   -> cpu=2, memory_in_gbs=
        # 2G1C -> cpu=1, memory_in_gbs=2
        if shape_config.endswith("C"):
            if 'G' not in shape_config:
                cpu_cores = int(shape_config[:-1])
            else:
                # 2G2C
                cpu_cores = int(shape_config.split("G")[1][:-1])
                memory_in_gbs = int(shape_config.split("G")[0])
        elif shape_config.endswith("G"):
            if 'C' not in shape_config:
                memory_in_gbs = int(shape_config[:-1])
            else:
                # 1C6G
                cpu_cores = int(shape_config.split("C")[0])
                memory_in_gbs = int(shape_config.split("C")[1][:-1])

        if cpu_cores is None and memory_in_gbs is None:
            await update.message.reply_markdown_v2(
                text=f'fail to extract cpu and memory_in_gbs from `{shape_config}`',
                reply_to_message_id=update.message.message_id)
            return

        instance = self.get_instance(oci_profile, instance_name)

        if isinstance(instance, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get instance `{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(instance))}`',
                reply_to_message_id=update.message.message_id)
            return

        current_cpus = int(instance.shape_config.ocpus)
        current_memory_in_gbs = int(instance.shape_config.memory_in_gbs)

        if (cpu_cores is not None and cpu_cores == current_cpus and
                memory_in_gbs is not None and memory_in_gbs == current_memory_in_gbs):
            await update.message.reply_markdown_v2(
                text=f'instance `{escape_markdown_v2(instance_name)}` is already '
                     f'`{escape_markdown_v2(shape_config)}`, no need to resize',
                reply_to_message_id=update.message.message_id)
            return

        result = self.submit(oci_profile, fn="resize_instance", instance=instance, cpu_cores=cpu_cores,
                             memory_in_gbs=memory_in_gbs, update=update)

        if is_failed(result):
            await update.message.reply_markdown_v2(
                text=f'fail to submit resize task task for instance '
                     f'`{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(result))}`',
                reply_to_message_id=update.message.message_id)
        else:
            await update.message.reply_markdown_v2(
                text=f'task submitted for instance '
                     f'`{escape_markdown_v2(instance_name)}`'
                     f' to resize to `{escape_markdown_v2(shape_config)}`, '
                     f'task\\_id: `{escape_markdown_v2(result.id)}`',
                reply_to_message_id=update.message.message_id)

    async def rename_instance_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:

        if context.args is None or len(context.args) < 3:
            await update.message.reply_markdown_v2(
                f"parameter error: `/rename_instance <profile> <old_name> <new_name>`",
                reply_to_message_id=update.message.message_id)
            return

        oci_profile = context.args[0]
        old_name = context.args[1]
        new_name = context.args[2]

        if old_name == new_name:
            await update.message.reply_markdown_v2(
                text=f"new name should not be the same as old name",
                reply_to_message_id=update.message.message_id)
            return

        _, instances = await self.list_instances(oci_profile)

        if isinstance(instances, Status):
            await update.message.reply_markdown_v2(
                text=f"fail to list instances `{escape_markdown_v2(old_name)}`, "
                     f"errors::`{escape_markdown_v2(str(instances))}`",
                reply_to_message_id=update.message.message_id)
            return

        new_name_exists = (len(list(cytoolz.filter(
            lambda i: i.display_name == new_name and i.lifecycle_state not in ["TERMINATED", "TERMINATING"],
            instances))) > 0)

        if new_name_exists:
            await update.message.reply_markdown_v2(
                text=f"instance `{escape_markdown_v2(new_name)}` already exists",
                reply_to_message_id=update.message.message_id)
            return

        old_instances = list(cytoolz.filter(lambda i: i.display_name == old_name, instances))

        if len(old_instances) == 0:
            await update.message.reply_markdown_v2(
                text=f"instance `{escape_markdown_v2(old_name)}` not found",
                reply_to_message_id=update.message.message_id)
            return

        if len(old_instances) > 1:
            await update.message.reply_markdown_v2(
                text=f"instance `{escape_markdown_v2(old_name)}` found more than one",
                reply_to_message_id=update.message.message_id)
            # return

        instance = old_instances[0]

        # should not be None
        oci_client = self.oci_clients.get(oci_profile)

        result = oci_client.rename_instance(instance.id, new_name)
        if isinstance(result, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to rename instance `{escape_markdown_v2(old_name)}` to `{escape_markdown_v2(new_name)}`, '
                     f'errors::`{escape_markdown_v2(str(result))}`',
                reply_to_message_id=update.message.message_id)
            return

        await update.message.reply_markdown_v2(
            text=f'rename instance `{escape_markdown_v2(old_name)}` to '
                 f'`{escape_markdown_v2(new_name)}` success',
            reply_to_message_id=update.message.message_id)

    async def instance_console_connection(self, oci_client: OCIClient, instance: Instance):
        """Run the synchronous OCI call in a thread for true async execution with rate limiting"""
        # Use semaphore to limit concurrent OCI API calls
        async with self.semaphore:
            console_conn = await asyncio.to_thread(oci_client.instance_console_connection, instance)
        return instance, console_conn

    async def get_console_connection_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if context.args is None or len(context.args) < 1:
            await update.message.reply_markdown_v2(
                text=f"parameter error: `/console_connections <profile> [instance_name]`",
                reply_to_message_id=update.message.message_id)
            return

        oci_profile = context.args[0]
        instance_names = context.args[1:]

        oci_client = self.oci_client(oci_profile)
        if oci_client is None:
            await update.message.reply_markdown_v2(
                text=f"OCI profile `{escape_markdown_v2(oci_profile)}` not found",
                reply_to_message_id=update.message.message_id)
            return
        instances = oci_client.list_instances()
        if isinstance(instances, Status):
            await update.message.reply_markdown_v2(
                text=f"fail to list instances, details: `{escape_markdown_v2(str(instances))}`",
                reply_to_message_id=update.message.message_id)
            return

        if len(instances) == 0:
            await update.message.reply_markdown_v2(
                text=f"no instance found",
                reply_to_message_id=update.message.message_id)
            return

        if len(instance_names) > 0:
            instances = list(cytoolz.filter(lambda i: i.display_name in instance_names, instances))

        if len(instances) == 0:
            await update.message.reply_markdown_v2(
                text=f"no instance found",
                reply_to_message_id=update.message.message_id)
            return

        tasks = [self.instance_console_connection(oci_client, instance) for instance in instances]
        results = await asyncio.gather(*tasks, return_exceptions=True)

        message = f"Console Connections:\n"
        for result in results:
            instance, console_connection = result
            if isinstance(console_connection, Status):
                message += (f"❌ `{escape_markdown_v2(instance.display_name)}`: "
                            f"`{escape_markdown_v2(str(console_connection.message))}`\n")
            else:
                message += f"✅ `{escape_markdown_v2(instance.display_name)}`\n"
                message += f"    🔗SSH for `macOS/Linux`\n"
                message += f"```bash\n"
                message += f"{escape_markdown_v2(console_connection.connection_string)}\n"
                message += "```\n"
                message += f"    🔗VNC connection for `macOS/Linux`\n"
                message += f"```bash\n"
                message += f"{escape_markdown_v2(console_connection.vnc_connection_string)}\n"
                message += "```\n"

        await update.message.reply_markdown_v2(text=message, reply_to_message_id=update.message.message_id)

    async def create_console_connection_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if context.args is None or len(context.args) < 2:
            await update.message.reply_markdown_v2(
                text=f"parameter error: `/create_console_connection <profile> <instance_name>`",
                reply_to_message_id=update.message.message_id)
            return

        use_master_ssh_key = False
        if len(context.args) > 2:
            use_master_ssh_key = context.args[2].lower() in ["use_master_ssh_key", "true"]

        oci_profile = context.args[0]
        instance_name = context.args[1]

        instance = self.get_instance(oci_profile, instance_name)
        if isinstance(instance, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get instance `{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(instance))}`',
                reply_to_message_id=update.message.message_id)
            return

        if instance.lifecycle_state in ["TERMINATED", "TERMINATING"]:
            await update.message.reply_markdown_v2(
                text=f'instance `{escape_markdown_v2(instance_name)}` is terminated or terminating',
                reply_to_message_id=update.message.message_id)

        ssh_key = None
        public_key = self.master_ssh_authorize_keys
        if not use_master_ssh_key or public_key is None:
            ssh_key = generate_ssh_key()
            public_key = ssh_key.public_key

        oci_client = self.oci_client(oci_profile)
        # try to delete the console connection and create a new one
        result = oci_client.delete_instance_console_connections(instance=instance)
        if is_failed(result):
            await update.message.reply_markdown_v2(
                text=f'fail to delete console connection for instance `{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(result))}`',
                reply_to_message_id=update.message.message_id)
            return
        if len(result) > 0:
            await update.message.reply_markdown_v2(
                text=f'console connection for instance `{escape_markdown_v2(instance_name)}` is deleting, '
                     f'please wait for a while',
                reply_to_message_id=update.message.message_id)

            async def wait_task(conn: ConsoleConnection):
                r = oci_client.wait_for_console_connection(instance=instance,
                                                           console_connection=conn,
                                                           exiting=self.exiting,
                                                           expected_lifecycle_state="DELETED")
                if isinstance(r, Status):
                    await update.message.reply_markdown_v2(
                        text=f'fail to wait for console connection to be deleted, '
                             f'details: `{escape_markdown_v2(str(r))}`',
                        reply_to_message_id=update.message.message_id)
                    return False
                return True

            tasks = [wait_task(conn) for conn in result]

            wait_result = await asyncio.gather(*tasks)
            if not all(wait_result):
                await update.message.reply_markdown_v2(
                    text=f'fail to wait for console connections to be deleted',
                    reply_to_message_id=update.message.message_id)
                return
        result = oci_client.create_console_connection(instance_id=instance.id, public_key=public_key)
        if isinstance(result, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to create console connection for instance `{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(result))}`',
                reply_to_message_id=update.message.message_id)
            return

        connection = result
        text = (f"console connection for instance `{escape_markdown_v2(instance_name)}` "
                f"created, please wait for a while\n")
        message = await update.message.reply_markdown_v2(text=text, reply_to_message_id=update.message.message_id)

        # wait for console connection to be ready
        result = oci_client.wait_for_console_connection(instance=instance,
                                                        console_connection=connection,
                                                        exiting=self.exiting)
        if isinstance(result, Status):
            await message.edit_text("fail to wait for console connection to be ready, "
                                    f"details: `{escape_markdown_v2(str(result))}`", parse_mode=ParseMode.MARKDOWN_V2)
            return

        console_connection = result
        text = (f"console connection for instance `{escape_markdown_v2(instance_name)}` "
                f"created, connection is ready, use the following commands to connect:\n"
                f"    🔗SSH for `macOS/Linux`\n"
                f"```bash\n"
                f"{escape_markdown_v2(console_connection.connection_string)}\n"
                "```\n"
                f"    🔗VNC connection for `macOS/Linux`\n"
                f"```bash\n"
                f"{escape_markdown_v2(console_connection.vnc_connection_string)}\n"
                "```\n")
        await message.edit_text(text=text, parse_mode=ParseMode.MARKDOWN_V2)
        if ssh_key is not None:
            private_key_path = ssh_key.save()
            if private_key_path is not None:
                await message.reply_document(document=open(private_key_path, 'rb'),
                                             filename=f"{instance_name}.pem",
                                             parse_mode=ParseMode.MARKDOWN_V2,
                                             caption=f"private key for console connection of instance `{instance_name}`"
                                                     f", passphrase is `{escape_markdown_v2(ssh_key.passphrase)}`")
                os.remove(private_key_path)

    async def get_or_create_console_connection_handler(self, update: Update,
                                                       context: ContextTypes.DEFAULT_TYPE) -> None:
        """Get console connection for an instance, create one with master SSH key if not exists."""
        if context.args is None or len(context.args) < 2:
            await update.message.reply_markdown_v2(
                text=f"parameter error: `/console_connection <profile> <instance_name>`",
                reply_to_message_id=update.message.message_id)
            return

        oci_profile = context.args[0]
        instance_name = context.args[1]

        instance = self.get_instance(oci_profile, instance_name)
        if isinstance(instance, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get instance `{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(instance))}`',
                reply_to_message_id=update.message.message_id)
            return

        if instance.lifecycle_state in ["TERMINATED", "TERMINATING"]:
            await update.message.reply_markdown_v2(
                text=f'instance `{escape_markdown_v2(instance_name)}` is terminated or terminating',
                reply_to_message_id=update.message.message_id)
            return

        oci_client = self.oci_client(oci_profile)

        # Try to get existing console connection first
        console_connection = oci_client.instance_console_connection(instance)
        if not isinstance(console_connection, Status):
            # Found existing active console connection
            text = (f"✅ Console connection for `{escape_markdown_v2(instance_name)}` found:\n"
                    f"    🔗SSH for `macOS/Linux`\n"
                    f"```bash\n"
                    f"{escape_markdown_v2(console_connection.connection_string)}\n"
                    "```\n"
                    f"    🔗VNC connection for `macOS/Linux`\n"
                    f"```bash\n"
                    f"{escape_markdown_v2(console_connection.vnc_connection_string)}\n"
                    "```\n")
            await update.message.reply_markdown_v2(text=text, reply_to_message_id=update.message.message_id)
            return

        # No existing console connection, create a new one with master SSH key
        public_key = self.master_ssh_authorize_keys
        ssh_key = None
        if public_key is None:
            ssh_key = generate_ssh_key()
            public_key = ssh_key.public_key
            await update.message.reply_markdown_v2(
                text=f"`master_ssh_authorize_keys` is not set, generating a new SSH key",
                reply_to_message_id=update.message.message_id)

        await update.message.reply_markdown_v2(
            text=f"No active console connection found for `{escape_markdown_v2(instance_name)}`, creating one\\.\\.\\.",
            reply_to_message_id=update.message.message_id)

        result = oci_client.create_console_connection(instance_id=instance.id, public_key=public_key)
        if isinstance(result, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to create console connection for instance `{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(result))}`',
                reply_to_message_id=update.message.message_id)
            return

        connection = result
        message = await update.message.reply_markdown_v2(
            text=f"Console connection for instance `{escape_markdown_v2(instance_name)}` created, please wait\\.\\.\\.",
            reply_to_message_id=update.message.message_id)

        # Wait for console connection to be ready
        result = oci_client.wait_for_console_connection(instance=instance,
                                                        console_connection=connection,
                                                        exiting=self.exiting)
        if isinstance(result, Status):
            await message.edit_text(f"fail to wait for console connection to be ready, "
                                    f"details: `{escape_markdown_v2(str(result))}`", parse_mode=ParseMode.MARKDOWN_V2)
            return

        console_connection = result
        text = (f"✅ Console connection for `{escape_markdown_v2(instance_name)}` is ready:\n"
                f"    🔗SSH for `macOS/Linux`\n"
                f"```bash\n"
                f"{escape_markdown_v2(console_connection.connection_string)}\n"
                "```\n"
                f"    🔗VNC connection for `macOS/Linux`\n"
                f"```bash\n"
                f"{escape_markdown_v2(console_connection.vnc_connection_string)}\n"
                "```\n")
        await message.edit_text(text=text, parse_mode=ParseMode.MARKDOWN_V2)

        # Send private key if generated
        if ssh_key is not None:
            private_key_path = ssh_key.save()
            if private_key_path is not None:
                await message.reply_document(document=open(private_key_path, 'rb'),
                                             filename=f"{instance_name}.pem",
                                             parse_mode=ParseMode.MARKDOWN_V2,
                                             caption=f"private key for console connection of instance `{instance_name}`"
                                                     f", passphrase is `{escape_markdown_v2(ssh_key.passphrase)}`")
                os.remove(private_key_path)

    @staticmethod
    async def ping_handler(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if context.args is None or len(context.args) < 1:
            await update.message.reply_markdown_v2(
                text=f"parameter error: `/ping <host> <host>`",
                reply_to_message_id=update.message.message_id)
            return

        hosts = context.args
        # run ping in parallel and combine the results
        tasks = []
        for host in hosts:
            if validate_ip_address(host):
                tasks.append(ping(host=host, count=8))
            else:
                tasks.extend([ping(host=host, ipv6=False, count=8), ping(host=host, ipv6=True, count=8)])
        results = await asyncio.gather(*tasks, return_exceptions=True)
        await update.message.reply_markdown_v2(text='\n'.join(results),
                                               reply_to_message_id=update.message.message_id)

    async def ping_instance_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if context.args is None or len(context.args) < 2:
            await update.message.reply_markdown_v2(
                text=f"parameter error: `/ping_instance <profile> <instance_name>`",
                reply_to_message_id=update.message.message_id)
            return

        oci_profile = context.args[0]
        instance_name = context.args[1]
        instance = self.get_instance(oci_profile, instance_name)
        if isinstance(instance, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get instance `{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(instance))}`',
                reply_to_message_id=update.message.message_id)
            return

        ips = self.oci_client(oci_profile).get_public_ips(instance.id)

        ipv4s = [ip.v4 for ip in ips]
        ipv6s = itertools.chain.from_iterable([ip.v6s for ip in ips])
        ips = itertools.chain(ipv4s, ipv6s)

        # run ping in parallel and combine the results
        tasks = [ping(host=ip, ipv6=True if validate_ipv6_address(ip) else False, count=8) for ip in ips]
        results = await asyncio.gather(*tasks, return_exceptions=True)

        message = f"ping results for instance `{escape_markdown_v2(instance_name)}`:\n"
        message += '\n'.join(results)

        await update.message.reply_markdown_v2(text=message, reply_to_message_id=update.message.message_id)

    async def instance_details_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:

        if context.args is None or len(context.args) < 2:
            await update.message.reply_markdown_v2(
                text=f"parameter error: `/instance_details <profile> <instance_name>`",
                reply_to_message_id=update.message.message_id)
            return

        oci_profile = context.args[0]
        instance_name = context.args[1]

        instance = self.get_instance(oci_profile, instance_name)

        if isinstance(instance, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get instance `{escape_markdown_v2(instance_name)}`, '
                     f'errors::`{escape_markdown_v2(str(instance))}`',
                reply_to_message_id=update.message.message_id)
            return

        message = f"Instance Details:\n"
        message += f"```bash\n"
        message += f"Name:            {escape_markdown_v2(instance.display_name)}\n"
        message += f"Region:          {escape_markdown_v2(instance.region)}\n"
        message += f"Shape:           {escape_markdown_v2(instance.shape)}\n"
        message += (f"CPU:             {escape_markdown_v2(int(instance.shape_config.ocpus))} x "
                    f"{escape_markdown_v2(instance.shape_config.processor_description)}\n")
        message += f"Memory:          {escape_markdown_v2(instance.shape_config.memory_in_gbs)} GB\n"
        message += f"Network:         {escape_markdown_v2(instance.shape_config.networking_bandwidth_in_gbps)}Gbps\n"
        message += f"Fault Domain:    {escape_markdown_v2(instance.fault_domain)}\n"
        message += f"Lifecycle State: {escape_markdown_v2(instance.lifecycle_state)}\n"
        message += f"Time Created:    {escape_markdown_v2(instance.time_created)}\n"

        oci_client = self.oci_client(oci_profile)
        ips = oci_client.get_public_ips(instance.id)

        if isinstance(ips, list):
            message += f"Public IPs:      "
            index = 0
            for ip in ips:
                if index == 0:
                    message += f"{escape_markdown_v2(ip.v4)}\n"
                else:
                    message += f"                 {escape_markdown_v2(ip.v4)}\n"
                for v6 in ip.v6s:
                    message += f"                 {escape_markdown_v2(v6)}\n"
                index += 1

        volumes = await self.volumes(oci_profile, instance_id=instance.id)

        dns_records = oci_client.get_instance_records(instance=instance)
        if isinstance(dns_records, list) and len(dns_records) > 0:
            domains = [r['name'] for r in list(cytoolz.unique(dns_records, key=lambda r: r['name']))]
            message += f"DNS Records:     "
            index = 0
            for domain in domains:
                if index == 0:
                    message += f"{escape_markdown_v2(domain)}\n"
                else:
                    message += f"                 {escape_markdown_v2(domain)}\n"
                index += 1

        if isinstance(volumes, list) and len(volumes) > 0:
            message += f"Boot Volumes:    "
            index = 0
            name_adjust = max([len(volume.display_name) for volume in volumes]) + 2
            size_adjust = max([len(readable_size(volume.size_in_gbs, base_unit='GB')) for volume in volumes]) + 2
            for volume in volumes:
                volume_size = readable_size(volume.size_in_gbs, base_unit='GB')
                volume_name = volume.display_name
                if index == 0:
                    message += f"{volume_name.ljust(name_adjust)} {volume_size.rjust(size_adjust)}\n"
                else:
                    message += (f"                 {volume_name.ljust(name_adjust)} "
                                f"{volume_size.rjust(size_adjust)}\n")
                index += 1

        allowed_ports = oci_client.get_allowed_ports(instance_id=instance.id)
        prefix = "Allowed Ports:   "
        allowed_ports_str = markdown_dict(allowed_ports, level=int(len(prefix) / 2) + 1)
        if allowed_ports_str is not None:
            message += f"Allowed Ports:   \n{allowed_ports_str}\n"

        message += f"```\n"

        await update.message.reply_markdown_v2(text=message, reply_to_message_id=update.message.message_id)

    async def instance_action_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:

        if context.args is None or len(context.args) < 3:
            await update.message.reply_markdown_v2(
                text=f"parameter error: `/instance_action <profile> <instance_name> <action>`",
                reply_to_message_id=update.message.message_id)
            return

        oci_profile = context.args[0]
        instance_name = context.args[1]
        action = context.args[2].upper()

        supported_actions = ["START", "RESET", "SOFTRESET", "DIAGNOSTICREBOOT", "STOP", "SOFTSTOP", "TERMINATE"]
        if action not in supported_actions:
            await update.message.reply_markdown_v2(
                text=f"action not supported: `{escape_markdown_v2(action)}`, "
                     f"should be one of {pretty(supported_actions)}",
                reply_to_message_id=update.message.message_id)
            return

        instance = self.get_instance(oci_profile, instance_name)

        if isinstance(instance, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get instance `{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(instance))}`',
                reply_to_message_id=update.message.message_id)
            return

        if instance.lifecycle_state in ["TERMINATED", "TERMINATING"]:
            await update.message.reply_markdown_v2(
                text=f"instance `{escape_markdown_v2(instance_name)}` is been "
                     f"`{escape_markdown_v2(instance.lifecycle_state)}`, can not "
                     f"do `{escape_markdown_v2(action)}`",
                reply_to_message_id=update.message.message_id)

        result = self.submit(oci_profile, "instance_action_task", instance=instance, action=action, update=update)

        if is_failed(result):
            await update.message.reply_markdown_v2(
                text=f'fail to submit task for instance '
                     f'`{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(result))}`',
                reply_to_message_id=update.message.message_id)
        else:
            await update.message.reply_markdown_v2(
                text=f'task submitted: `{escape_markdown_v2(action)}` instance for '
                     f'`{escape_markdown_v2(instance_name)}`, task\\_id: `{escape_markdown_v2(result.id)}`',
                reply_to_message_id=update.message.message_id)

    async def start_instance_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:

        if context.args is None or len(context.args) < 2:
            await update.message.reply_markdown_v2(
                text=f"parameter error: `/start_instance <profile> <instance_name>`",
                reply_to_message_id=update.message.message_id)

        oci_profile = context.args[0]
        instance_name = context.args[1]

        instance = self.get_instance(oci_profile, instance_name)

        if isinstance(instance, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get instance `{escape_markdown_v2(instance_name)}`, '
                     f'errors::`{escape_markdown_v2(str(instance))}`',
                reply_to_message_id=update.message.message_id)
            return

        # should not be None
        status = instance.lifecycle_state
        if status == "RUNNING" or status == "PROVISIONING":
            await update.message.reply_markdown_v2(
                text=f"instance `{escape_markdown_v2(instance_name)}` is already running",
                reply_to_message_id=update.message.message_id)
            return
        elif status != "STOPPED":
            await update.message.reply_markdown_v2(
                text=f"inappropriate instance status: `{escape_markdown_v2(status)}`",
                reply_to_message_id=update.message.message_id)
            return

        result = self.submit(oci_profile, "instance_action_task", instance=instance, action="START", update=update)

        if is_failed(result):
            await update.message.reply_markdown_v2(
                text=f'fail to submit task for instance '
                     f'`{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(result))}`',
                reply_to_message_id=update.message.message_id)
        else:
            await update.message.reply_markdown_v2(
                text=f'task submitted: start instance for '
                     f'`{escape_markdown_v2(instance_name)}`, task\\_id: `{result.id}`',
                reply_to_message_id=update.message.message_id)

    async def delete_instance_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:

        if context.args is None or len(context.args) < 2:
            await update.message.reply_markdown_v2(
                text=f"parameter error: `/delete_instance <profile> <instance_name>`",
                reply_to_message_id=update.message.message_id)
            return

        oci_profile = context.args[0]
        instance_name = context.args[1]

        instance = self.get_instance(oci_profile, instance_name)
        if isinstance(instance, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get instance `{escape_markdown_v2(instance_name)}`, '
                     f'errors::`{escape_markdown_v2(str(instance))}`',
                reply_to_message_id=update.message.message_id)
            return

        # should not be None
        status = instance.lifecycle_state
        if status == "TERMINATED" or status == "TERMINATING":
            await update.message.reply_markdown_v2(
                text=f"instance `{escape_markdown_v2(instance_name)}` "
                     f"is already terminated",
                reply_to_message_id=update.message.message_id)
            return

        result = self.submit(oci_profile, "delete_instance_task", instance=instance, update=update)
        if is_failed(result):
            await update.message.reply_markdown_v2(
                text=f'fail to submit delete instance task for instance '
                     f'`{escape_markdown_v2(instance_name)}`, '
                     f'details: `{escape_markdown_v2(str(result))}`',
                reply_to_message_id=update.message.message_id)
        else:
            await update.message.reply_markdown_v2(
                text=f'task submitted: delete instance for '
                     f'`{escape_markdown_v2(instance_name)}`, '
                     f'task\\_id: `{result.id}`',
                reply_to_message_id=update.message.message_id)

    async def create_instance_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:

        if context.args is None or len(context.args) < 3:
            await update.message.reply_markdown_v2(
                text=f"parameter error: `/create_instance <profile> <shape> "
                     f"<instance_config> [use_master_ssh_key]`",
                reply_to_message_id=update.message.message_id)
            return

        oci_profile = context.args[0]
        shape = context.args[1]
        instance_config = context.args[2]
        use_master_ssh_key = False
        display_name = None
        if len(context.args) > 3:
            use_master_ssh_key = context.args[3].lower() == "use_master_ssh_key"

        if len(context.args) > 4:
            display_name = context.args[4].strip().upper()

        shape = shape.upper()
        if shape not in available_shapes:
            await update.message.reply_markdown_v2(
                text=f"shape not supported: `{escape_markdown_v2(shape)}`, "
                     f"should be one of:\n{markdown_dict(value_map(available_shapes))}",
                reply_to_message_id=update.message.message_id)
            return

        # should not be None
        shape = available_shapes[shape]

        # check instance_config should be like 1C2G100G C is cpu, G is memory, G is disk
        regex = r"(\d+)C(\d+)G(\d+)G"
        # 1C2G100G -> 1, 2, 100
        if not re.match(regex, instance_config):
            await update.message.reply_markdown_v2(
                text=f"parameter error: invalid `instance_config`, "
                     f"should be like `1C2G100G` or `1G1C100G`",
                reply_to_message_id=update.message.message_id)
            return

        re.findall(regex, instance_config)
        cpu, memory, disk_size = re.findall(regex, instance_config)[0]
        logger.debug(f'start to create instance, shape: {shape}, cpu: {cpu}, memory: {memory}, disk_size: {disk_size}')

        instance_ssh_authorize_keys = None
        key_message = "SSH private key file:"
        if use_master_ssh_key:
            instance_ssh_authorize_keys = self.master_ssh_authorize_keys
            if self.master_ssh_authorize_keys is None:
                await update.message.reply_markdown_v2(
                    text=f"`master_ssh_authorize_keys` is not set, will try to generate one",
                    reply_to_message_id=update.message.message_id)
            else:
                key_message = "use your own SSH private key, please replace it with the new one if you changed it"

        oci_client = self.oci_client(oci_profile)
        if oci_client is None:
            await update.message.reply_markdown_v2(
                text=f"profile not found: `{escape_markdown_v2(oci_profile)}`",
                reply_to_message_id=update.message.message_id)
            return

        create_instance_details = (
            oci_client.build_create_instance_details(shape=shape,
                                                     ocpus=int(cpu),
                                                     memory_in_gbs=int(memory),
                                                     boot_volume_size_in_gbs=int(disk_size),
                                                     display_name=display_name,
                                                     ssh_authorized_keys=instance_ssh_authorize_keys))

        if isinstance(create_instance_details, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to build instance details, '
                     f'errors: {create_instance_details.message}',
                reply_to_message_id=update.message.message_id)
            return

        instance_name = create_instance_details.display_name

        result = self.submit(oci_profile, fn='create_instance_task', create_instance_details=create_instance_details,
                             update=update)

        if is_failed(result):
            await update.message.reply_markdown_v2(
                text=f'fail to submit create instance task with shape '
                     f'`{escape_markdown_v2(shape)}`: '
                     f'`{escape_markdown_v2(instance_config)}`, '
                     f'details: `{escape_markdown_v2(str(result))}`',
                reply_to_message_id=update.message.message_id)
            return

        submit_message = await update.message.reply_markdown_v2(
            text=f'submit create instance task success, '
                 f'instance name: '
                 f'`{escape_markdown_v2(instance_name)}`'
                 f', {key_message}, task\\_id: `{result.id}`',
            reply_to_message_id=update.message.message_id)

        private_key_file = oci_client.save_ssh_key(create_instance_details)
        if private_key_file is not None:
            pass_phrase = create_instance_details.ssh_passphrase()
            await update.message.reply_document(open(private_key_file, "rb"),
                                                caption=f"SSH private key file for "
                                                        f"`{escape_markdown_v2(instance_name)}`, "
                                                        f"passphrase: `{escape_markdown_v2(pass_phrase)}`",
                                                parse_mode=ParseMode.MARKDOWN_V2,
                                                reply_to_message_id=submit_message.message_id)

    async def create_cf_record_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:

        if self.cloudflare is None:
            await update.message.reply_markdown_v2(
                text=f"cloudflare not configured",
                reply_to_message_id=update.message.message_id)
            return

        if context.args is None or len(context.args) < 2:
            await update.message.reply_markdown_v2(
                text=f'''parameter error: `{escape_markdown_v2('/create_cf_record <domain> <ip>')}`''',
                reply_to_message_id=update.message.message_id)
            return

        domain = context.args[0]
        ip = context.args[1]

        result = self.cloudflare.create_dns_record(domain, ip)

        if is_failed(result):
            await update.message.reply_markdown_v2(
                text=f"fail to create record `{escape_markdown_v2(domain)}`: "
                     f"`{escape_markdown_v2(ip)}`, details: {result}",
                reply_to_message_id=update.message.message_id)
        else:
            domain = result["name"]
            await update.message.reply_markdown_v2(
                text=f"create record `{escape_markdown_v2(domain)}`: "
                     f"`{escape_markdown_v2(ip)}` success",
                reply_to_message_id=update.message.message_id)

    async def update_cf_record_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:

        if self.cloudflare is None:
            await update.message.reply_markdown_v2(
                text=f"cloudflare not configured",
                reply_to_message_id=update.message.message_id)
            return
        if context.args is None or len(context.args) < 2:
            await update.message.reply_markdown_v2(
                text=f'''parameter error: `{escape_markdown_v2('/update_cf_record <domain> <ip>')}`''',
                reply_to_message_id=update.message.message_id)
            return

        domain = context.args[0]
        ip = context.args[1]

        records = self.cloudflare.dns_records(name=domain)

        if len(records) == 0:
            await update.message.reply_markdown_v2(
                text=f"record `{escape_markdown_v2(domain)}` not found, "
                     f"create it? `/create_cf_record "
                     f"{escape_markdown_v2(domain)} {escape_markdown_v2(ip)}`",
                reply_to_message_id=update.message.message_id)

        else:
            for record in records:
                record_name = record["name"]
                record_ip = record["content"]
                result = self.cloudflare.update_dns_record(record, ip)
                if is_failed(result):
                    await update.message.reply_markdown_v2(
                        text=f"fail to update record `{escape_markdown_v2(record_name)}`: "
                             f"`{escape_markdown_v2(record_ip)}` to "
                             f"`{escape_markdown_v2(ip)}`, details: {result}",
                        reply_to_message_id=update.message.message_id)
                else:
                    await update.message.reply_markdown_v2(
                        text=f"update record `{escape_markdown_v2(record_name)}`: "
                             f"`{escape_markdown_v2(record_ip)}` to "
                             f"`{escape_markdown_v2(ip)}` success",
                        reply_to_message_id=update.message.message_id)

    async def delete_cf_record_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:

        if self.cloudflare is None:
            await update.message.reply_markdown_v2(
                text=f"cloudflare not configured",
                reply_to_message_id=update.message.message_id)
            return

        if context.args is None or len(context.args) == 0:
            await update.message.reply_markdown_v2(
                text=f'''parameter error: `{escape_markdown_v2('/delete_cf_record <ip|domain>')}`''',
                reply_to_message_id=update.message.message_id)
            return

        record_filters = context.args

        records = self.cloudflare.dns_records()

        for record_filter in record_filters:
            to_delete = list(
                cytoolz.filter(lambda r: record_filter in r["content"] or record_filter in r["name"], records))
            if len(to_delete) == 0:
                await update.message.reply_markdown_v2(
                    text=f"record `{escape_markdown_v2(record_filter)}` not found",
                    reply_to_message_id=update.message.message_id)
                continue
            failed_records = []
            success_records = []
            for record in to_delete:
                record_name = record["name"]
                record_id = record["id"]
                result = self.cloudflare.delete_dns_record(record_id)
                if is_failed(result):
                    logger.warning(f"fail to delete record `{record_name}`, details: {result}")
                    failed_records.append(record)
                else:
                    logger.info(f"delete record `{record_name}` success")
                    success_records.append(record)
            message = f"success records:\n"
            for record in success_records:
                record_name = record["name"]
                record_ip = record["content"]
                message += f'`✅  {escape_markdown_v2(record_name)}`: `{escape_markdown_v2(record_ip)}`\n'
            message += "failed records:\n"
            for record in failed_records:
                record_name = record["name"]
                record_ip = record["content"]
                message += f'`❎  {escape_markdown_v2(record_name)}`: `{escape_markdown_v2(record_ip)}`\n'
            message += f"{pretty(failed_records)}\n"
            await update.message.reply_markdown_v2(text=message, reply_to_message_id=update.message.message_id)

    async def cf_records_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:

        if self.cloudflare is None:
            await update.message.reply_markdown_v2(
                text=f"cloudflare not configured",
                reply_to_message_id=update.message.message_id)
            return

        record_filters = context.args
        records = self.cloudflare.dns_records()
        # sort by name

        if len(records) == 0:
            await update.message.reply_markdown_v2(
                text=f"No records", reply_to_message_id=update.message.message_id)
        else:
            records = filter_cf_records(records, record_filters)
            if len(records) == 0:
                await update.message.reply_markdown_v2(
                    text=f"No records", reply_to_message_id=update.message.message_id)
                return
            records = sorted(records, key=lambda r: r["name"])
            # send by 100 records each time
            for i in range(0, len(records), 50):
                message = ""
                current = records[i:i + 50 if i + 50 < len(records) else len(records)]
                for record in current:
                    record_name = record["name"]
                    record_ip = record["content"]
                    created_at = record["created_on"]
                    message += (f'`✅ {escape_markdown_v2(record_name)}`: `{escape_markdown_v2(record_ip)}`, '
                                f'{escape_markdown_v2(created_at)}\n')
                await update.message.reply_markdown_v2(text=message, reply_to_message_id=update.message.message_id)

    async def dns_records_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:

        if self.cloudflare is None:
            await update.message.reply_markdown_v2(
                text=f"cloudflare not configured",
                reply_to_message_id=update.message.message_id)
            return

        if context.args is None or len(context.args) < 2:
            await update.message.reply_markdown_v2(
                text=f"parameter error: `/dns_records <profile> <instance_name>`",
                reply_to_message_id=update.message.message_id)
            return

        oci_profile = context.args[0]
        instance_name = context.args[1]

        instance = self.get_instance(oci_profile, instance_name)

        if isinstance(instance, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get instance `{escape_markdown_v2(instance_name)}`, '
                     f'errors::`{escape_markdown_v2(str(instance))}`',
                reply_to_message_id=update.message.message_id)
            return

        # should not be None
        oci_client = self.oci_client(oci_profile)

        records = oci_client.get_instance_records(instance)
        message = f"DNS records for `{escape_markdown_v2(instance_name)}`:\n"
        if len(records) == 0:
            message += f"No records"
        else:
            message += "\n".join([f'`{record["name"]:32s}`:  `{record["content"]}`' for record in records])

        await update.message.reply_markdown_v2(text=message, reply_to_message_id=update.message.message_id)

    async def delete_ipv6_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:

        if context.args is None or len(context.args) < 2:
            await update.message.reply_markdown_v2(
                text=f'''parameter error: `{escape_markdown_v2(
                    '/delete_ipv6 <profile> <instance_name> [ipv6_address]')}`''',
                reply_to_message_id=update.message.message_id)
            return

        oci_profile = context.args[0]
        instance_name = context.args[1]
        ipv6_address = None
        if len(context.args) > 2:
            ipv6_address = context.args[2]
            # validate ipv6_address
            if not validate_ipv6_address(ipv6_address):
                await update.message.reply_markdown_v2(
                    text=f"parameter error: invalid ipv6 address: "
                         f"`{escape_markdown_v2(ipv6_address)}`",
                    reply_to_message_id=update.message.message_id)
                return

        instance = self.get_instance(oci_profile, instance_name)
        if isinstance(instance, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get instance `{escape_markdown_v2(instance_name)}`, '
                     f'errors::`{escape_markdown_v2(str(instance))}`',
                reply_to_message_id=update.message.message_id)
            return

        oci_client = self.oci_client(oci_profile)

        ipv6_addresses = oci_client.get_instance_ipv6s(instance)

        to_delete = list(
            cytoolz.filter(lambda ipv6: ipv6_address is None or ipv6.ip_address == ipv6_address, ipv6_addresses))

        if len(to_delete) == 0:
            await update.message.reply_markdown_v2(
                text=f"ipv6 address `{escape_markdown_v2(ipv6_address)}` not found",
                reply_to_message_id=update.message.message_id)
            return

        failed = []
        success = []
        for ip in to_delete:
            result = oci_client.delete_ipv6(ip.id)
            if is_failed(result):
                failed.append(ip)
                logger.warning(f"fail to delete ipv6 `{ip.ip_address}`, details: {result}")
            else:
                logger.info(f"delete ipv6 `{ip.ip_address}` success")
                success.append(ip)

        dns_records = self.cloudflare.list_dns_records(ips=[ip.ip_address for ip in success])
        failed_records = self.cloudflare.delete_dns_records(dns_records)
        success_records = [record for record in dns_records if record['id'] not in [r['id'] for r in failed_records]]

        message = f"success ipv6 addresses:\n"
        for ip in success:
            message += f'`✅  {escape_markdown_v2(ip.ip_address)}`\n'

        if len(failed) > 0:
            message += f"failed ipv6 addresses:\n"
            for ip in failed:
                message += f'`❎  {escape_markdown_v2(ip.ip_address)}`\n'

        if len(success_records) > 0:
            message += f"success dns records:\n"
            for record in success_records:
                message += f'`✅  {escape_markdown_v2(record["name"])}: {escape_markdown_v2(record["content"])}`\n'

        if len(failed_records) > 0:
            message += f"failed dns records:\n"
            for record in failed_records:
                message += f'`❎  {escape_markdown_v2(record["name"])}: {escape_markdown_v2(record["content"])}`\n'

        await update.message.reply_markdown_v2(text=message, reply_to_message_id=update.message.message_id)

    async def change_ip_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:

        if context.args is None or len(context.args) < 3:
            await update.message.reply_markdown_v2(
                text=f'''parameter error: `{escape_markdown_v2(
                    '/change_ip <profile> <instance_name> [EPHEMERAL|RESERVED|V6]')}`''',
                reply_to_message_id=update.message.message_id)
            return

        oci_profile = context.args[0]
        instance_name = context.args[1]
        ip_type = context.args[2].upper()

        if ip_type not in ["EPHEMERAL", "RESERVED", "V6"]:
            await update.message.reply_markdown_v2(
                text=f'''type error: `{escape_markdown_v2(
                    '/change_ip <profile> <instance_name> [EPHEMERAL|RESERVED|V6]')}`''',
                reply_to_message_id=update.message.message_id)
            return

        instance = self.get_instance(oci_profile, instance_name)
        if isinstance(instance, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get instance `{instance_name}`,'
                     f' errors::`{escape_markdown_v2(str(instance))}`',
                reply_to_message_id=update.message.message_id)
            return

        # should not be None
        oci_client = self.oci_clients.get(oci_profile)
        changes = oci_client.change_ip(instance, ip_type=ip_type)
        changes = oci_client.update_dns_records(instance=instance, changes=changes)
        message = f"IP address changed for `{instance_name}`:\n"
        if len(changes) == 0:
            message += f"*no changes*"
        else:
            for change in changes:
                message += f'{change.markdown()}\n'
        await update.message.reply_markdown(
            message,
            reply_to_message_id=update.message.message_id)

    async def add_security_rules_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if context.args is None or len(context.args) < 3:
            await update.message.reply_markdown_v2(
                text=f'''parameter error: `{escape_markdown_v2(
                    '/add_security_rules <profile> <type> <ports>')}`''',
                reply_to_message_id=update.message.message_id)
            return

        oci_profile = context.args[0]
        direction = context.args[1].upper()
        ports = context.args[2]
        protocols = []
        if len(context.args) > 3:
            protocol = context.args[3].upper()
            if protocol not in ["TCP", "UDP"]:
                await update.message.reply_markdown_v2(
                    text=f'''type error: `{escape_markdown_v2(
                        '/add_security_rules <profile> [INGRESS|EGRESS] <ports> [TCP|UDP]')}`''',
                    reply_to_message_id=update.message.message_id)
                return
            protocols.append(protocol)
        if len(protocols) == 0:
            protocols = ["TCP", "UDP"]

        accepted_directions = {
            "INGRESS": "INGRESS",
            "IN": "INGRESS",
            "EGRESS": "EGRESS",
            "OUT": "EGRESS"
        }

        if direction not in ["INGRESS", "EGRESS", "IN", "OUT"]:
            await update.message.reply_markdown_v2(
                text=f'''type error: `{escape_markdown_v2(
                    '/add_security_rules <profile> [INGRESS|EGRESS] <ports>')}`''',
                reply_to_message_id=update.message.message_id)
            return

        direction = accepted_directions[direction]
        if ports.upper() == "ALL":
            protocols = ["ALL"]
        # ports should be like 80,443,8080-8090
        else:
            ports = ports.split(',')
            ports = [port.strip() for port in ports if port is not None and len(port.strip()) > 0]
            invalid_ports = []
            for port in ports:
                # remove the invalid port
                if not re.match(r"(\d+)-(\d+)", port) and not re.match(r"\d+", port):
                    invalid_ports.append(port)
                    ports.remove(port)
            if len(invalid_ports) > 0:
                await update.message.reply_markdown_v2(
                    text=f'''invalid ports: `{markdown_list(invalid_ports)}`''',
                    reply_to_message_id=update.message.message_id)

            if len(ports) == 0:
                await update.message.reply_markdown_v2(
                    text=f'''invalid ports, should be like: `{escape_markdown_v2('80,443,8080-8090')}`''',
                    reply_to_message_id=update.message.message_id)
                return

        oci_client = self.oci_client(oci_profile)
        if oci_client is None:
            await update.message.reply_markdown_v2(
                text=f"profile not found: `{escape_markdown_v2(oci_profile)}`",
                reply_to_message_id=update.message.message_id)
            return

        vcns = oci_client.list_vcns()
        if isinstance(vcns, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to list vcns, errors: `{escape_markdown_v2(str(vcns))}`',
                reply_to_message_id=update.message.message_id)
            return

        if len(vcns) == 0:
            await update.message.reply_markdown_v2(
                text=f'no vcns found for profile `{escape_markdown_v2(oci_profile)}`',
                reply_to_message_id=update.message.message_id)
            return

        tasks = []
        for vcn in vcns:
            for protocol in protocols:
                for is_ipv6 in [True, False]:
                    if protocol == "ALL":
                        ports = [None]
                    for port in ports:
                        tasks.append(self.allow_port_on_vcn(oci_client,
                                                            vcn=vcn,
                                                            port=port,
                                                            is_ipv6=is_ipv6,
                                                            direction=direction,
                                                            protocol=protocol))

        results = await asyncio.gather(*tasks)
        message = f"add security rules for `{escape_markdown_v2(oci_profile)}`:\n"
        for proto, is_ipv6, port, direction, result in results:
            port_str = f'`{escape_markdown_v2(port)}`' if port is not None else ""
            ip_str = 'IPv6' if is_ipv6 else 'IPv4'
            if is_failed(result):
                message += f'fail to add security rules for `{proto}` `{ip_str}` ports {port_str}: `{direction}`, ' \
                           f'errors: `{escape_markdown_v2(str(result))}`\n'
            else:
                message += f'add security rules for `{proto}` `{ip_str}` ports {port_str}: `{direction}` success\n'

        await update.message.reply_markdown_v2(text=message, reply_to_message_id=update.message.message_id)

    async def allow_port_on_vcn(self, oci_client: OCIClient, vcn: Vcn,
                                direction: str, port: str = None, is_ipv6: bool = False, protocol="TCP"):
        """Run the synchronous OCI call in a thread for true async execution with rate limiting"""
        min_port, max_port = None, None
        if protocol not in ['ALL']:
            if '-' in port:
                min_port, max_port = port.split('-')
                min_port, max_port = int(min_port), int(max_port)
            else:
                min_port, max_port = int(port), int(port)
        
        # Use semaphore to limit concurrent OCI API calls
        async with self.semaphore:
            result = await asyncio.to_thread(
                oci_client.allow_vcn_ports,
                vcn,
                min_port=min_port,
                max_port=max_port,
                is_ipv6=is_ipv6,
                direction=direction,
                protocol=protocol
            )
        return protocol, is_ipv6, port, direction, result

    async def clear_security_rules_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
        if context.args is None or len(context.args) < 1:
            await update.message.reply_markdown_v2(
                text=f'''parameter error: `{escape_markdown_v2(
                    '/clear_security_rules <profile>')}`''',
                reply_to_message_id=update.message.message_id)
            return
        oci_profile = context.args[0]
        oci_client = self.oci_client(oci_profile)
        if isinstance(oci_client, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to get oci client for profile `{escape_markdown_v2(oci_profile)}`, '
                     f'errors: `{escape_markdown_v2(str(oci_client))}`',
                reply_to_message_id=update.message.message_id)
            return

        vcns = oci_client.list_vcns()
        if isinstance(vcns, Status):
            await update.message.reply_markdown_v2(
                text=f'fail to list vcns, errors: `{escape_markdown_v2(str(vcns))}`',
                reply_to_message_id=update.message.message_id)
            return

        tasks = [oci_client.clear_vcn_security_lists(vcn=vcn) for vcn in vcns]
        await asyncio.gather(*tasks)
        await update.message.reply_markdown_v2(
            f"clear security rules for `{escape_markdown_v2(oci_profile)}` success",
            reply_to_message_id=update.message.message_id)

    @staticmethod
    async def help_handler(update: Update, _: ContextTypes.DEFAULT_TYPE) -> None:

        prefix = (f"Hello [@{escape_markdown_v2(update.effective_user.username)}]"
                  f"(tg://user?id={update.effective_user.id}), ")
        if update.message.text.startswith("/"):
            # get the command
            command = update.message.text.split(" ")[0][1:]
            prefix += f"command `{escape_markdown_v2(command)}` not found, "
        else:
            f"welcome to use oracle bot, "
        prefix += f"here are the available commands:\n"
        await update.message.reply_markdown_v2(
            text=prefix + f"```\n"
                          # Profile Management
                          f"# Profile Management\n"
                          f"/profiles                              \\- list profiles\n"
                          f"/add\\_profile                           \\- add new profile\n"
                          f"/cancel                                \\- cancel add\\_profile\n"
                          f"/delete\\_profiles <profiles>            \\- delete profiles\n"
                          f"/mark\\_dead <profile> <dead|alive>      \\- mark dead/alive\n"
                          f"/tenancy [profiles]                    \\- show tenancy info\n"
                          f"\n"
                          # Instance Management
                          f"# Instance Management\n"
                          f"/instances [profiles]                  \\- list instances\n"
                          f"/instance\\_details <profile> <name>     \\- details\n"
                          f"/create\\_instance <profile> <shape> \\.\\.\\.  \\- create\n"
                          f"/rename\\_instance <profile> <old> <new> \\- rename\n"
                          f"/resize\\_instance <profile> <name> \\.\\.\\.   \\- resize\n"
                          f"/delete\\_instance <profile> <name>      \\- delete\n"
                          f"/start\\_instance <profile> <name>       \\- start\n"
                          f"/instance\\_action <profile> <name> \\.\\.\\.  \\- action\n"
                          f"/ping\\_instance <profile> <name>        \\- ping instance\n"
                          f"/ping <hosts>                          \\- ping hosts\n"
                          f"\n"
                          # Volume Management
                          f"# Volume Management\n"
                          f"/volumes [profiles]                    \\- list volumes\n"
                          f"/attach\\_volume <profile> <inst> <vol>  \\- attach\n"
                          f"/detach\\_volume <profile> <inst> <vol>  \\- detach\n"
                          f"/resize\\_boot\\_volume <profile> \\.\\.\\.      \\- resize\n"
                          f"\n"
                          # Console Connection
                          f"# Console Connection\n"
                          f"/console\\_connection <profile> <name>    \\- get/create\n"
                          f"/console\\_connections <profile> [names] \\- list all\n"
                          f"/create\\_console\\_connection <profile>   \\- force create\n"
                          f"\n"
                          # Network Management
                          f"# Network Management\n"
                          f"/change\\_ip <profile> <name> [type]     \\- change IP\n"
                          f"/delete\\_ipv6s <profile> <name> [ipv6]  \\- delete IPv6\n"
                          f"/allow\\_ports <profile> <dir> <ports>   \\- add rules\n"
                          f"/clear\\_security\\_lists <profile>        \\- clear rules\n"
                          f"\n"
                          # DNS/Cloudflare
                          f"# DNS/Cloudflare\n"
                          f"/dns\\_records <profile> <name>          \\- list DNS records\n"
                          f"/cf\\_records [filters]                  \\- list CF records\n"
                          f"/add\\_cf\\_record <domain> <ip>           \\- add CF record\n"
                          f"/create\\_cf\\_record <domain> <ip>        \\- alias add\\_cf\n"
                          f"/update\\_cf\\_record <domain> <ip>        \\- update CF\n"
                          f"/delete\\_cf\\_records <ip|domain>         \\- delete CF\n"
                          f"\n"
                          # Task Management
                          f"# Task Management\n"
                          f"/tasks                                 \\- list tasks\n"
                          f"/pause\\_task <task\\_id>                  \\- pause task\n"
                          f"/start\\_task <task\\_id>                  \\- start/resume\n"
                          f"/abort\\_task <task\\_id>                  \\- abort task\n"
                          f"/abandon\\_task <task\\_id>                \\- alias abort\n"
                          f"\n"
                          # System
                          f"# System\n"
                          f"/sysinfo                               \\- system info\n"
                          f"/alive [profiles]                      \\- alive check\n"
                          f"/help                                  \\- show this help\n"
                          f"```",
            reply_to_message_id=update.message.message_id)


def parse_arguments():
    parser = argparse.ArgumentParser(description='Oracle CLI helper')
    parser.add_argument('--telegram-bot-token', '-tt', dest='telegram_bot_token', help='Telegram bot token')
    parser.add_argument('--telegram-users', '-tus', nargs='+', dest='telegram_users', help='Telegram users')
    parser.add_argument('--telegram-api-host', '-th', dest='telegram_api_host', help='Telegram api host')
    parser.add_argument('--ssh-authorized-keys', '-k', dest='ssh_authorized_keys', help='SSH authorized keys')
    parser.add_argument('--cloudflare-email', '-ce', dest='cloudflare_email', help='Cloudflare email')
    parser.add_argument('--cloudflare-api-key', '-ck', dest='cloudflare_api_key', help='Cloudflare api key')
    parser.add_argument('--cloudflare-zone-id', '-cz', dest='cloudflare_zone_id', help='Cloudflare zone id')
    cli_args = parser.parse_args()
    return cli_args


def main():
    log_file = os.path.join(__base_dir__, "logs", "oci_bot.log")
    logger.add(log_file, rotation="1day", retention="7 days", level="DEBUG", compression="gz")

    cmd_args = parse_arguments()
    ssh_authorize_keys = cmd_args.ssh_authorized_keys
    cloudflare_email = cmd_args.cloudflare_email
    cloudflare_api_key = cmd_args.cloudflare_api_key
    cloudflare_zone_id = cmd_args.cloudflare_zone_id
    telegram_bot_token = cmd_args.telegram_bot_token
    telegram_users = cmd_args.telegram_users

    ssh_authorize_keys = ssh_authorize_keys.strip() if ssh_authorize_keys is not None \
        else os.environ.get("SSH_AUTHORIZED_KEYS", None)
    cloudflare_email = cloudflare_email.strip() if cloudflare_email is not None \
        else os.environ.get("CLOUDFLARE_EMAIL", None)

    cloudflare_api_key = cloudflare_api_key.strip() if cloudflare_api_key is not None \
        else os.environ.get("CLOUDFLARE_API_KEY", None)

    cloudflare_zone_id = cloudflare_zone_id.strip() if cloudflare_zone_id is not None \
        else os.environ.get("CLOUDFLARE_ZONE_ID", None)

    telegram_bot_token = telegram_bot_token.strip() if telegram_bot_token is not None \
        else os.environ.get("TELEGRAM_BOT_TOKEN", None)

    telegram_users = telegram_users if telegram_users is not None and len(telegram_users) > 0 \
        else os.environ.get("TELEGRAM_USERS", None)

    if telegram_users is not None and isinstance(telegram_users, str):
        telegram_users = telegram_users.split(" ")
        telegram_users = [user.strip() for user in telegram_users if user is not None and len(user.strip()) > 0]

    if ssh_authorize_keys is not None and os.path.exists(ssh_authorize_keys):
        with open(ssh_authorize_keys) as f:
            ssh_authorize_keys = f.read().strip()

    if ssh_authorize_keys is not None and not ssh_authorize_keys.startswith("ssh-rsa"):
        logger.warning(f"ssh-authorized-keys is not valid, should be like: ssh-rsa xxxxx")
        ssh_authorize_keys = None

    # cloudflare should have all the parameters
    cf = None
    if (cloudflare_email is not None
            and cloudflare_api_key is not None
            and cloudflare_zone_id is not None):
        cf = CloudFlareClient(email=cloudflare_email, api_key=cloudflare_api_key,
                              zone_id=cloudflare_zone_id)

    elif (
            cloudflare_email is not None or
            cloudflare_api_key is not None or
            cloudflare_zone_id is not None):
        logger.warning(
            f"cloudflare config is not valid, should have all the parameters: `email`, `api_key`, `zone_id`")
        cf = None

    # Accessing the parsed arguments
    config_file = os.path.join(__base_dir__, "config")
    if not os.path.exists(config_file):
        logger.warning(f"config file not found: {config_file}, create one")

    bot = None
    if telegram_bot_token is not None:
        bot = TelegramBot(token=telegram_bot_token)

    clients = {}
    profiles = all_profiles(oci_config_file=os.path.abspath(config_file))

    # if profiles is empty, try to load from backup one
    if len(profiles) == 0:
        backup_file = os.path.join(__base_dir__, "oci_config.bak")
        if os.path.exists(backup_file):
            all_profiles(oci_config_file=os.path.abspath(backup_file))

    # Optimize thread pool size based on CPU count and profile count
    # For I/O-bound operations (OCI API calls), we can use more threads than CPU cores
    # But we need to balance between too few (slow) and too many (context switching overhead)
    cpu_count = os.cpu_count() or 4
    profile_count = len(profiles) if profiles else 0
    
    # Base calculation: CPU cores * 2 for I/O-bound work
    base_workers = cpu_count * 2
    
    # Add workers for profiles, but with diminishing returns
    # Each profile can benefit from 1-2 threads, but not unlimited
    if profile_count > 0:
        # Add 1 worker per profile up to a reasonable limit
        profile_workers = min(profile_count, cpu_count * 4)
        max_workers = base_workers + profile_workers
    else:
        max_workers = base_workers
    
    # Cap at a reasonable maximum to avoid excessive thread creation
    # Even with many profiles, we don't want 1000+ threads
    max_workers = min(max_workers, 100)  # Hard cap at 100 threads
    max_workers = max(max_workers, 4)    # Minimum 4 threads
    
    logger.info(f"Initializing thread pool with {max_workers} workers "
                f"(CPU: {cpu_count}, Profiles: {profile_count})")
    tp = ThreadPoolExecutor(max_workers=max_workers, thread_name_prefix="oci_worker")

    # Pre-load all configs at once (faster than loading 81 times)
    logger.info(f"Loading configurations for {len(profiles)} profiles...")
    config_load_start = time.time()
    configs = {}
    for profile in profiles:
        oci_cfg = config_from_file(os.path.abspath(config_file), profile)
        if oci_cfg is not None:
            configs[profile] = oci_cfg
        else:
            logger.warning(f"fail to load profile `{profile}`")
    config_load_time = time.time() - config_load_start
    logger.info(f"Loaded {len(configs)} configs in {config_load_time:.2f}s")
    
    # Parallelize OCI client creation for faster initialization
    def create_oci_client(profile):
        """Create an OCI client for a profile"""
        try:
            oci_cfg = configs.get(profile)
            if oci_cfg is None:
                return profile, None
            
            client = OCIClient(config=oci_cfg,
                              cloudflare=cf,
                              ssh_authorized_keys=ssh_authorize_keys,
                              telegram_bot=bot,
                              thread_pool=tp)
            # Set profile name for fallback naming (avoids API call during init)
            client.profile_name = profile
            return profile, client
        except Exception as e:
            logger.warning(f"fail to create client for profile `{profile}`: {e}")
            return profile, None
    
    start_time = time.time()
    logger.info(f"Creating {len(configs)} OCI clients in parallel...")
    # Use thread pool to create clients in parallel
    with ThreadPoolExecutor(max_workers=min(len(configs), cpu_count * 2)) as init_executor:
        results = list(init_executor.map(create_oci_client, configs.keys()))
    
    # Build clients dictionary from results
    for profile, client in results:
        if client is not None:
            clients[profile] = client
    
    elapsed = time.time() - start_time
    logger.info(f"Created {len(clients)} OCI clients successfully in {elapsed:.2f}s "
                f"({elapsed/len(clients):.3f}s per client)")

    logger.info("Initializing Telegram command bot...")
    bot_start_time = time.time()
    bot = TelegramCommandBot(token=telegram_bot_token,
                             thread_pool=tp,
                             oci_clients=clients,
                             master_ssh_authorize_keys=ssh_authorize_keys,
                             whitelist=telegram_users,
                             cloudflare=cf,
                             oci_config_file=os.path.abspath(config_file),
                             message_bot=bot
                             )
    bot_elapsed = time.time() - bot_start_time
    logger.info(f"Telegram command bot initialized in {bot_elapsed:.2f}s")
    
    bot.start()


if __name__ == "__main__":
    main()

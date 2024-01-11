FROM python:alpine as base

WORKDIR /app

RUN apk add --no-cache --update \
    gcc \
    python3-dev \
    musl-dev \
    libffi-dev \
    bash \
    && rm -rf /var/cache/apk/*

COPY requirements.txt .

RUN pip install -r requirements.txt -U

COPY . .

VOLUME /app/.oci

FROM base as prod
ADD docker-entrypoint.sh /docker-entrypoint.sh
RUN chmod +x /docker-entrypoint.sh
ENTRYPOINT ["/docker-entrypoint.sh"]
CMD ["python", "oci_bot.py"]

ARG VERIFIER_IMAGE=autoformbench-verifier:lean4.32.2-mathlib-905b9581

FROM ${VERIFIER_IMAGE}

USER root

COPY test.sh /tests/test.sh

RUN chmod 0755 /tests/test.sh \
    && mkdir -p /app /logs/verifier \
    && chown -R verifier:verifier /app /logs/verifier

USER verifier
ENV HOME=/home/verifier
WORKDIR /app

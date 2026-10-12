# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the CC BY-NC 4.0 license found in the
# LICENSE file in the root directory of this source tree.

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

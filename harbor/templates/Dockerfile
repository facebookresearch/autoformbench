# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the CC BY-NC 4.0 license found in the
# LICENSE file in the root directory of this source tree.

ARG AGENT_IMAGE=autoformbench-agent:lean4.32.2-mathlib-905b9581

FROM ${AGENT_IMAGE}

USER root
WORKDIR /app

COPY --chown=agent:agent workspace/ /app/

RUN mkdir -p /app/.lake \
    && ln -s /opt/autoformbench/packages /app/.lake/packages \
    && chown -R --no-dereference agent:agent /app \
    && chmod -R u+rwX,go+rX /app

USER agent
ENV HOME=/home/agent

RUN lake build

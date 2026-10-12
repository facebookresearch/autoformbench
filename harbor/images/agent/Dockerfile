# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the CC BY-NC 4.0 license found in the
# LICENSE file in the root directory of this source tree.

FROM ubuntu:24.04

RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
        ca-certificates \
        curl \
        git \
        python3 \
        python3-venv \
        ripgrep \
        zstd \
    && rm -rf /var/lib/apt/lists/*

ARG ELAN_VERSION=4.2.1
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.32.2

ENV ELAN_HOME=/opt/elan
ENV PATH="/opt/elan/bin:${PATH}"

RUN curl -sSfL \
        "https://raw.githubusercontent.com/leanprover/elan/v${ELAN_VERSION}/elan-init.sh" \
        | sh -s -- -y --no-modify-path --default-toolchain none \
    && elan toolchain install "${LEAN_TOOLCHAIN}" \
    && elan default "${LEAN_TOOLCHAIN}" \
    && lean --version \
    && lake --version

COPY --from=ghcr.io/astral-sh/uv:0.9.27 /uv /uvx /usr/local/bin/

RUN uv --version

WORKDIR /opt/autoformbench

COPY harbor/runtime/pyproject.toml harbor/runtime/uv.lock ./

RUN uv sync --frozen --no-dev

COPY harbor/runtime/tools/lean_repl_mcp/ tools/lean_repl_mcp/
COPY harbor/runtime/tools/loogle_mcp/ tools/loogle_mcp/
COPY harbor/runtime/tools/run-repl.sh harbor/runtime/tools/run-loogle.sh tools/

RUN chmod 0755 tools/run-repl.sh tools/run-loogle.sh

COPY harbor/runtime/tools/lean-project/lean-toolchain \
     harbor/runtime/tools/lean-project/lakefile.toml \
     harbor/runtime/tools/lean-project/lake-manifest.json \
     tools/lean-project/

WORKDIR /opt/autoformbench/tools/lean-project

RUN lake exe cache get \
    && lake build Mathlib \
    && lake build repl loogle \
    && ln -s /opt/autoformbench/tools/lean-project/.lake/packages \
        /opt/autoformbench/packages

RUN printf 'Nat.add_comm\n' | lake exe loogle -i -j >/tmp/loogle-index-build.out \
    && test -s .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.loogle-index

RUN cd /opt/autoformbench/tools/lean-project/.lake/packages/proofwidgets \
    && lake build widgetPackageLock

RUN find /opt/autoformbench/tools/lean-project/.lake/packages \
        -mindepth 1 -maxdepth 1 -type d \
        -exec git config --system --add safe.directory '{}' \;

ENV PATH="/opt/autoformbench/.venv/bin:${PATH}"

RUN ln -s /opt/autoformbench/tools/run-repl.sh /usr/local/bin/autoform-repl \
    && ln -s /opt/autoformbench/tools/run-loogle.sh /usr/local/bin/autoform-loogle

RUN useradd --create-home --shell /bin/bash agent \
    && useradd --create-home --shell /bin/bash verifier \
    && mkdir -p /logs/agent /logs/artifacts \
    && chown -R agent:agent /logs/agent /logs/artifacts \
    && chmod -R a+rX /opt/autoformbench /opt/elan \
    && chmod -R go-w /opt/autoformbench /opt/elan

USER agent
ENV HOME=/home/agent
WORKDIR /app

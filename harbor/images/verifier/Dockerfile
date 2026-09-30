# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the CC BY-NC 4.0 license found in the
# LICENSE file in the root directory of this source tree.

ARG AGENT_IMAGE=autoformbench-agent:lean4.32.2-mathlib-905b9581

FROM ${AGENT_IMAGE} AS verifier-builder

USER root
ENV HOME=/root

RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
        build-essential \
        golang-go \
    && rm -rf /var/lib/apt/lists/* \
    && go version

ENV RUSTUP_HOME=/opt/rustup
ENV CARGO_HOME=/opt/cargo
ENV PATH="/opt/cargo/bin:${PATH}"

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
        | sh -s -- -y --no-modify-path \
    && rustc --version \
    && cargo --version

ARG LEAN4EXPORT_URL=https://github.com/leanprover/lean4export.git
ARG LEAN4EXPORT_REV=4e7915201d3f9f04470d9eae002fa695f7cdc589
ARG CORPUS_TOOLCHAIN=leanprover/lean4:v4.32.2
ARG NANODA_URL=https://github.com/robsimmons/nanoda_lib.git
ARG NANODA_REV=68d5ca9db226849b41a6fff59d796ff19d0a8840
ARG LANDRUN_REV=5ed4a3db3a4ad930d577215c6b9abaa19df7f99f
ARG COMPARATOR_URL=https://github.com/leanprover/comparator.git
ARG COMPARATOR_REV=789279735fe44c1c05dc54bb9f46ba4d9b8c7611

WORKDIR /opt/autoformbench-benchmark

RUN mkdir -p /out

RUN mkdir -p .ci \
    && git clone "${LEAN4EXPORT_URL}" .ci/lean4export \
    && git -C .ci/lean4export checkout --detach "${LEAN4EXPORT_REV}" \
    && test "$(git -C .ci/lean4export rev-parse HEAD)" = "${LEAN4EXPORT_REV}" \
    && cd .ci/lean4export \
    && elan override set "${CORPUS_TOOLCHAIN}" \
    && lake build lean4export \
    && install -m 0755 .lake/build/bin/lean4export /out/lean4export

RUN git clone "${NANODA_URL}" .ci/nanoda \
    && git -C .ci/nanoda checkout --detach "${NANODA_REV}" \
    && test "$(git -C .ci/nanoda rev-parse HEAD)" = "${NANODA_REV}" \
    && cd .ci/nanoda \
    && cargo build --locked --release \
    && install -m 0755 target/release/nanoda_bin /out/nanoda_bin

RUN GO111MODULE=on go install \
        "github.com/zouuup/landrun/cmd/landrun@${LANDRUN_REV}" \
    && install -m 0755 /root/go/bin/landrun /out/landrun

RUN git clone "${COMPARATOR_URL}" comparator \
    && git -C comparator checkout --detach "${COMPARATOR_REV}" \
    && test "$(git -C comparator rev-parse HEAD)" = "${COMPARATOR_REV}" \
    && cd comparator \
    && lake build lean4export comparator \
    && install -m 0755 .lake/build/bin/comparator /out/comparator

FROM ${AGENT_IMAGE}

USER root
ENV HOME=/root

WORKDIR /opt/autoformbench-benchmark

COPY --from=verifier-builder /out/lean4export /usr/local/bin/lean4export
COPY --from=verifier-builder /out/nanoda_bin /usr/local/bin/nanoda_bin
COPY --from=verifier-builder /out/landrun /usr/local/bin/landrun
COPY --from=verifier-builder /out/comparator /usr/local/bin/comparator

# These are the source-free, canonical grading inputs. They contain challenge
# statements and Comparator adapters, but no accepted submissions or gold
# proofs.
COPY workspaces/ workspaces/
COPY harbor/images/verifier/verify.py /usr/local/bin/autoform-verify

RUN chmod 0755 /usr/local/bin/autoform-verify \
    && mkdir -p /app /logs/verifier /tmp/autoform-grade \
    && chmod -R a+rX /opt/autoformbench-benchmark \
    && chmod -R go-w /opt/autoformbench-benchmark \
    && chown -R verifier:verifier /app /logs/verifier /tmp/autoform-grade

USER verifier
ENV HOME=/home/verifier
WORKDIR /app

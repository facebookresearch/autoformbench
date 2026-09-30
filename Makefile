# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the CC BY-NC 4.0 license found in the
# LICENSE file in the root directory of this source tree.

SHELL := /bin/bash
.DEFAULT_GOAL := help

# Forward caller-provided proxy variables without recording their values in the
# release. Explicit build args also override stale per-user Docker proxy config.
DOCKER_PROXY_ARGS := --build-arg http_proxy --build-arg https_proxy \
	--build-arg HTTP_PROXY --build-arg HTTPS_PROXY \
	--build-arg no_proxy --build-arg NO_PROXY

.PHONY: help harbor-tasks check harbor-images

help:
	@printf '%s\n' \
	  'make harbor-tasks  Generate all source-free Harbor task directories.' \
	  'make check         Verify Harbor task parity.' \
	  'make harbor-images Build the local agent and verifier OCI images.'

harbor-tasks:
	PYTHONDONTWRITEBYTECODE=1 python3 harbor/export.py --all

check: harbor-tasks
	PYTHONDONTWRITEBYTECODE=1 python3 harbor/export.py --check

harbor-images:
	docker build $(DOCKER_PROXY_ARGS) -f harbor/images/agent/Dockerfile \
	  -t autoformbench-agent:lean4.32.2-mathlib-905b9581 .
	docker build $(DOCKER_PROXY_ARGS) \
	  --build-arg AGENT_IMAGE=autoformbench-agent:lean4.32.2-mathlib-905b9581 \
	  -f harbor/images/verifier/Dockerfile \
	  -t autoformbench-verifier:lean4.32.2-mathlib-905b9581 .

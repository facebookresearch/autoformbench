#!/usr/bin/env bash
# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the CC BY-NC 4.0 license found in the
# LICENSE file in the root directory of this source tree.

set -u

autoform-verify {{ problem_id }}
status=$?

# Accepted and rejected submissions are both completed evaluations. Only a
# verifier infrastructure error makes the Harbor trial itself fail.
case "$status" in
  0|1) exit 0 ;;
  *)   exit "$status" ;;
esac

#!/usr/bin/env bash
set -u

autoform-verify {{ problem_id }}
status=$?

# Accepted and rejected submissions are both completed evaluations. Only a
# verifier infrastructure error makes the Harbor trial itself fail.
case "$status" in
  0|1) exit 0 ;;
  *)   exit "$status" ;;
esac

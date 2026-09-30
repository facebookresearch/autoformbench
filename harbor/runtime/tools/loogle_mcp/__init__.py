# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the CC BY-NC 4.0 license found in the
# LICENSE file in the root directory of this source tree.

"""Loogle MCP server — AutoformBench's own copy.

Self-contained: drives a warm `lake exe loogle -i -j` process (Loogle in
interactive JSON mode) inside a built Lean project, exposing Mathlib search
by name / type / subterm to coding agents (Claude/Codex) as `loogle_search`.

Loogle loads the project's own Mathlib oleans at runtime, so results are
version-matched to whatever Lean project the launcher points at.
"""

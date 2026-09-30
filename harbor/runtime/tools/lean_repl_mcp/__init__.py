"""Lean REPL MCP server — AutoformBench's own copy.

Self-contained: exposes a built Lean project's `lake exe repl` to coding agents
(Claude/Codex) as the `run_lean_code` MCP tool. Lives here so the evaluations
work from a plain clone with no external-repo dependency.

Originally derived from autoform-bot's servers/repl; maintained independently
in this repo from here on.
"""

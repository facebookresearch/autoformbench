#!/usr/bin/env bash
# autoform REPL MCP launcher — used by both Claude and Codex.
#
# Self-contained: derives its own location, runs the vendored lean_repl_mcp
# server, and points the REPL at a built Lean project. No hardcoded user paths.
#
# Overridable via environment:
#   LEAN_PROJECT_DIR         built Lean project to attach to   (default: ./lean-project)
#   LEAN_NUM_REPLS           pool size                          (default: 1)
#   LEAN_ALLOW_LOCAL_IMPORTS allow importing the project's own modules (default: 0)
#   ELAN_HOME                elan install dir                   (default: ~/.elan)
set -euo pipefail

SCRIPT_PATH="$(readlink -f "${BASH_SOURCE[0]}")"
SCRIPT_DIR="$(cd "$(dirname "$SCRIPT_PATH")" && pwd)"

# Put elan-managed lean/lake on PATH for the `lake exe repl` subprocess.
export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"

export LEAN_PROJECT_DIR="${LEAN_PROJECT_DIR:-$SCRIPT_DIR/lean-project}"
# Default capacity is RAM-derived (can be dozens of Mathlib-loaded REPLs);
# one REPL is enough for an interactive eval session.
export LEAN_NUM_REPLS="${LEAN_NUM_REPLS:-1}"
# Allow snippets to import the project's own modules (datapoints), not just Mathlib.
# Off by default; set to 1 to enable.
export LEAN_ALLOW_LOCAL_IMPORTS="${LEAN_ALLOW_LOCAL_IMPORTS:-0}"

PYTHON="$SCRIPT_DIR/../.venv/bin/python"
if [ ! -x "$PYTHON" ]; then
    echo "ERROR: Python environment is missing: $PYTHON" >&2
    echo "Rebuild the AutoformBench agent image from the release root." >&2
    exit 1
fi

cd "$SCRIPT_DIR"
exec "$PYTHON" -m lean_repl_mcp.server

#!/usr/bin/env bash
# autoform Loogle MCP launcher — used by both Claude and Codex.
#
# Self-contained: derives its own location, runs the vendored loogle_mcp server,
# which drives `lake exe loogle -i -j` inside a built Lean project. Loogle loads
# that project's Mathlib oleans at runtime → results are version-matched.
#
# Overridable via environment:
#   LEAN_PROJECT_DIR  built Lean project (with loogle built)  (default: ./lean-project)
#   ELAN_HOME         elan install dir                          (default: ~/.elan)
set -euo pipefail
SCRIPT_PATH="$(readlink -f "${BASH_SOURCE[0]}")"
SCRIPT_DIR="$(cd "$(dirname "$SCRIPT_PATH")" && pwd)"
export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
export LEAN_PROJECT_DIR="${LEAN_PROJECT_DIR:-$SCRIPT_DIR/lean-project}"

PYTHON="$SCRIPT_DIR/../.venv/bin/python"
if [ ! -x "$PYTHON" ]; then
    echo "ERROR: Python environment is missing: $PYTHON" >&2
    echo "Rebuild the AutoformBench agent image from the release root." >&2
    exit 1
fi

cd "$SCRIPT_DIR"
exec "$PYTHON" -m loogle_mcp.server

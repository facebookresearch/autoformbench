"""Lean REPL MCP server — run Lean code and check compilation."""

from __future__ import annotations

import json
import math
import os

from fastmcp.server import FastMCP

from .core import DEFAULT_STARTUP_TIMEOUT, format_repl_response
from .pool import LeanReplPool, LeanReplPoolConfig


def config_from_environment() -> LeanReplPoolConfig:
    """Build a validated REPL configuration from the server environment."""
    cwd = os.environ.get("LEAN_PROJECT_DIR", ".")
    repl_cmd = os.environ.get("LEAN_REPL_CMD", "lake exe repl").split()
    num_repls = int(os.environ.get("LEAN_NUM_REPLS", "0")) or None
    raw_startup_timeout = os.environ.get(
        "LEAN_REPL_STARTUP_TIMEOUT_SECONDS",
        str(DEFAULT_STARTUP_TIMEOUT),
    )
    try:
        startup_timeout = float(raw_startup_timeout)
    except ValueError as error:
        raise ValueError(
            "LEAN_REPL_STARTUP_TIMEOUT_SECONDS must be a positive finite number"
        ) from error
    if not math.isfinite(startup_timeout) or startup_timeout <= 0:
        raise ValueError(
            "LEAN_REPL_STARTUP_TIMEOUT_SECONDS must be a positive finite number"
        )
    allow_local = os.environ.get("LEAN_ALLOW_LOCAL_IMPORTS", "").lower() in (
        "1",
        "true",
        "yes",
    )
    return LeanReplPoolConfig(
        cwd=cwd,
        repl_command=repl_cmd,
        num_repls=num_repls,
        startup_timeout=startup_timeout,
        allow_local_imports=allow_local,
    )


def create_repl_server(pool: LeanReplPool) -> FastMCP:
    """Create a FastMCP server wrapping a LeanReplPool.

    Exposes two tools:
    - run_lean_code: Send Lean code to the REPL pool
    - get_repl_status: Check pool health and memory usage
    """
    server = FastMCP(name="autoform-repl")

    @server.tool
    def run_lean_code(code: str, timeout: float | None = None) -> str:
        """Send Lean code to the REPL and return formatted diagnostics.

        Imports are cached automatically — repeated calls with the same
        imports reuse the cached environment for speed. When the server is
        started with LEAN_ALLOW_LOCAL_IMPORTS=1, snippets may also import the
        project's own modules (e.g. `import Number_Theory_I.Proposition20_3`),
        loaded alongside Mathlib; otherwise only Mathlib/Aesop/Batteries are allowed.

        Args:
            code: Lean code to execute (imports + body).
            timeout: Optional timeout in seconds (overrides the default).

        Returns:
            Formatted diagnostic output: compilation status, errors,
            sorries with goals, and warnings.
        """
        kwargs = {}
        if timeout is not None:
            kwargs["timeout"] = timeout
        result = pool.run(code, **kwargs)
        return format_repl_response(result)

    @server.tool
    def get_repl_status() -> str:
        """Check the REPL pool's health and memory usage.

        Returns:
            JSON string with capacity, memory_usage_gb, and shutdown status.
        """
        return json.dumps(
            {
                "capacity": pool.capacity,
                "memory_usage_gb": round(pool.get_memory_usage(), 2),
                "shutdown": pool._shutdown,
            }
        )

    return server


if __name__ == "__main__":
    config = config_from_environment()
    pool = LeanReplPool(config)

    try:
        server = create_repl_server(pool)
        server.run(transport="stdio")
    finally:
        pool.shutdown()

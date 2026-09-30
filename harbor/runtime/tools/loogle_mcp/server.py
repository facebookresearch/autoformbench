# Copyright (c) Meta Platforms, Inc. and affiliates.
#
# This source code is licensed under the CC BY-NC 4.0 license found in the
# LICENSE file in the root directory of this source tree.

"""Loogle MCP server — search Mathlib by name, type, or subterm."""

from __future__ import annotations

import json
import os

from fastmcp.server import FastMCP

from .core import DEFAULT_MAX_RESULTS, LoogleConfig, LoogleSearcher, format_loogle_response


def create_loogle_server(searcher: LoogleSearcher) -> FastMCP:
    """Create a FastMCP server wrapping a LoogleSearcher.

    Exposes:
    - loogle_search: search Mathlib via Loogle
    - get_loogle_status: check whether the Loogle process is up
    """
    server = FastMCP(name="autoform-loogle")

    @server.tool
    def loogle_search(query: str, num_results: int = DEFAULT_MAX_RESULTS) -> str:
        """Search Mathlib for declarations via Loogle (version-matched to the project).

        Query syntax (combine terms, separated by commas — all must match):
        - By name substring:        "differ"            (declarations whose name contains "differ")
        - By constant present:       Real.sin            (lemmas mentioning Real.sin)
        - By type / subterm:         _ * (_ ^ _)         (a subterm of this shape appears)
        - By conclusion shape:       |- tsum _ = _       (the goal/conclusion matches)
        - By exact type:             (?a -> ?b) -> List ?a -> List ?b
        Example: `Real.sin, _ ^ 2`  → lemmas mentioning Real.sin with a square subterm.

        Args:
            query: A Loogle query string.
            num_results: Max hits to display (default 20).

        Returns:
            A readable list of matching declarations with their types and modules.
        """
        result = searcher.search(query)
        return format_loogle_response(result, num_results)

    @server.tool
    def get_loogle_status() -> str:
        """Report whether the Loogle process is running and warmed up."""
        return json.dumps(
            {
                "alive": searcher.is_alive(),
                "mathlib_loaded": searcher._loaded,
            }
        )

    return server


if __name__ == "__main__":
    cwd = os.environ.get("LEAN_PROJECT_DIR", ".")
    searcher = LoogleSearcher(LoogleConfig(cwd=cwd))
    try:
        server = create_loogle_server(searcher)
        server.run(transport="stdio")
    finally:
        searcher.close()

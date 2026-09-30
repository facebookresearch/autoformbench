"""Loogle searcher — single warm ``lake exe loogle -i -j`` subprocess.

Loogle runs in interactive mode (reads one query per line from stdin) with
JSON output (one result object per line). The Mathlib environment + search
index are loaded once at process startup and kept warm, so the first query
is slow (imports Mathlib) and subsequent queries are fast.
"""

from __future__ import annotations

import json
import os
import select
import subprocess
import threading
import time
from dataclasses import dataclass, field
from logging import getLogger
from typing import Any

logger = getLogger(__name__)

DEFAULT_MAX_RESULTS = 20


def _inherit_clean_env() -> dict[str, str]:
    """Return a copy of the current environment without PYTHONPATH noise."""
    env = os.environ.copy()
    env.pop("PYTHONPATH", None)
    return env


def _kill_subprocesses(process: subprocess.Popen) -> None:
    """Kill a process and all its children."""
    try:
        import psutil

        parent = psutil.Process(process.pid)
        for child in parent.children(recursive=True):
            try:
                child.kill()
            except psutil.NoSuchProcess:
                pass
        parent.kill()
        parent.wait(timeout=5)
    except Exception:
        try:
            process.kill()
            process.wait(timeout=5)
        except Exception:
            pass


@dataclass
class LoogleConfig:
    """Configuration for a Loogle searcher."""

    cwd: str = "."
    env: dict[str, str] = field(default_factory=dict)

    # First query loads Mathlib (+ builds the index if not cached); be generous.
    startup_timeout: float = 600.0
    query_timeout: float = 60.0
    chunk_size: int = 65536
    max_buffer_bytes: int = 32 * 1024 * 1024

    loogle_command: list[str] = field(
        default_factory=lambda: ["lake", "exe", "loogle", "-i", "-j"]
    )


class LoogleProcessExited(RuntimeError):
    """Raised when the Loogle process dies unexpectedly."""


class LoogleSearcher:
    """Manages a single warm ``lake exe loogle -i -j`` subprocess."""

    def __init__(self, config: LoogleConfig) -> None:
        self.config = config
        self.cwd = config.cwd
        self.process: subprocess.Popen | None = None
        self._loaded = False
        self._lock = threading.Lock()

    # -- lifecycle ----------------------------------------------------------

    def start(self) -> None:
        """Spawn the Loogle process (non-blocking; Mathlib loads lazily)."""
        env = _inherit_clean_env()
        env.update(self.config.env)
        self.process = subprocess.Popen(
            self.config.loogle_command,
            cwd=self.cwd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
        )
        self._loaded = False

    def close(self) -> None:
        """Terminate the Loogle process."""
        try:
            if not self.process or self.process.poll() is not None:
                return
            _kill_subprocesses(self.process)
        finally:
            self.process = None
            self._loaded = False

    def restart(self) -> None:
        self.close()
        self.start()

    def is_alive(self) -> bool:
        return self.process is not None and self.process.poll() is None

    # -- query --------------------------------------------------------------

    def search(self, query: str, timeout: float | None = None) -> dict[str, Any]:
        """Run one Loogle query, returning the parsed JSON result.

        Retries once with a fresh process if the subprocess has died.
        """
        with self._lock:
            for attempt in range(2):
                try:
                    if not self.is_alive():
                        self.start()
                    return self._query(query, timeout)
                except (LoogleProcessExited, TimeoutError, json.JSONDecodeError) as e:
                    logger.error("Loogle query failed (attempt %d/2): %s", attempt + 1, e)
                    self.restart()
                    if attempt == 1:
                        return {"error": f"Loogle unavailable: {e}"}
            return {"error": "Loogle unavailable"}

    def _query(self, query: str, timeout: float | None) -> dict[str, Any]:
        if self.process is None or self.process.poll() is not None:
            raise LoogleProcessExited("Loogle process is not running.")

        # First query pays the Mathlib-load cost.
        effective_timeout = timeout or (
            self.config.query_timeout if self._loaded else self.config.startup_timeout
        )

        line = query.replace("\n", " ").strip() + "\n"
        self.process.stdin.write(line.encode("utf-8"))
        self.process.stdin.flush()

        result = json.loads(self._read_line(effective_timeout))
        self._loaded = True
        return result

    def _read_line(self, timeout: float) -> str:
        """Read the next JSON line from stdout (draining stderr).

        Interactive Loogle emits non-JSON status lines too (e.g. the startup
        banner "Loogle is ready." and "...rebuilding." notices), so we skip any
        stdout line that is not a JSON object and return the first one that is.
        """
        stdout_fd = self.process.stdout.fileno()
        stderr_fd = self.process.stderr.fileno()

        buffer = ""
        stderr_buffer = ""
        end_time = time.monotonic() + timeout

        while True:
            # Consume any complete lines already buffered; return the first JSON one.
            while "\n" in buffer:
                line, buffer = buffer.split("\n", 1)
                line = line.strip()
                if line.startswith("{"):
                    return line
                if line:
                    logger.debug("Loogle non-JSON stdout: %s", line)

            remaining = end_time - time.monotonic()
            if remaining <= 0:
                raise TimeoutError(f"Loogle query timed out after {timeout}s")

            ready, _, _ = select.select([stdout_fd, stderr_fd], [], [], remaining)
            if not ready:
                raise TimeoutError(f"Loogle query timed out after {timeout}s")

            if stdout_fd in ready:
                chunk = os.read(stdout_fd, self.config.chunk_size)
                if not chunk:
                    raise LoogleProcessExited(
                        f"Loogle process exited. stderr tail: {stderr_buffer[-500:]}"
                    )
                buffer += chunk.decode("utf-8", errors="replace")
                if len(buffer) > self.config.max_buffer_bytes:
                    raise RuntimeError("Loogle response exceeded buffer limit")

            if stderr_fd in ready:
                err = os.read(stderr_fd, self.config.chunk_size)
                if err:
                    stderr_buffer += err.decode("utf-8", errors="replace")
                    logger.debug("Loogle stderr: %s", err.decode("utf-8", "replace").rstrip())


def format_loogle_response(result: dict[str, Any], max_results: int = DEFAULT_MAX_RESULTS) -> str:
    """Format a Loogle JSON result as a readable list of hits."""
    if result.get("error"):
        return f"Loogle error: {result['error']}"

    hits = result.get("hits") or []
    count = result.get("count", len(hits))
    if not hits:
        header = (result.get("header") or "").strip()
        return header or "No results."

    parts: list[str] = [f"Found {count} declaration(s):"]
    for hit in hits[:max_results]:
        name = hit.get("name", "?")
        typ = (hit.get("type") or "").strip()
        module = hit.get("module", "")
        line = f"  - {name} : {typ}" if typ else f"  - {name}"
        if module:
            line += f"    [{module}]"
        parts.append(line)
    if count > max_results:
        parts.append(f"  ... and {count - max_results} more (raise num_results to see them)")
    return "\n".join(parts)

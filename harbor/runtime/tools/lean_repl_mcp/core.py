"""Lean REPL — single session managing a ``lake exe repl`` subprocess.

Provides LeanRepl with non-blocking I/O, a preloaded import environment,
memory monitoring, automatic restart, and multi-snippet chaining.
"""

from __future__ import annotations

import json
import os
import random
import select
import subprocess
import threading
import time
from dataclasses import dataclass, field
from logging import getLogger
from typing import Any

logger = getLogger(__name__)

DEFAULT_MAX_DIAGNOSTICS = 10
DEFAULT_SMOKE_TEST_TIMEOUT = 10
DEFAULT_STARTUP_TIMEOUT = 600.0

ALLOWED_IMPORTS = frozenset({"Mathlib", "Aesop", "Batteries", "LeanSearchClient"})
WARMUP_IMPORTS = frozenset({"Mathlib"})


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def _get_process_memory_gb(process: subprocess.Popen | None) -> float:
    """Return memory usage of a process and its children in GB."""
    if process is None or process.poll() is not None:
        return 0.0
    try:
        import psutil

        parent = psutil.Process(process.pid)
        total = parent.memory_info().rss
        for child in parent.children(recursive=True):
            try:
                total += child.memory_info().rss
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                pass
        return total / (1024**3)
    except Exception:
        return 0.0


def _kill_subprocesses(process: subprocess.Popen) -> None:
    """Kill a process and all its children."""
    try:
        import psutil

        parent = psutil.Process(process.pid)
        children = parent.children(recursive=True)
        for child in children:
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


def _inherit_clean_env() -> dict[str, str]:
    """Return a copy of the current environment without PYTHONPATH noise."""
    env = os.environ.copy()
    env.pop("PYTHONPATH", None)
    return env


def _split_imports_and_body(code: str) -> tuple[list[str], str, int]:
    """Split Lean code into import statements and body.

    Returns (import_names, body, header_line_count).
    """
    lines = code.split("\n")
    imports: list[str] = []
    body_start = 0

    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("import "):
            imports.append(stripped[7:].strip())
            body_start = i + 1
        elif stripped == "" or stripped.startswith("--"):
            if imports:
                body_start = i + 1
        else:
            break

    body = "\n".join(lines[body_start:])
    return imports, body, body_start


# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------


@dataclass
class LeanReplConfig:
    """Configuration for a Lean REPL instance."""

    cwd: str = "."
    env: dict[str, str] = field(default_factory=dict)

    request_timeout: float = 30.0
    startup_timeout: float = DEFAULT_STARTUP_TIMEOUT
    chunk_size: int = 4096

    instance_mem_limit_gb: int = 16
    mem_interval_check: float = 1.0
    max_retries: int = 1

    allowed_imports: frozenset[str] = ALLOWED_IMPORTS
    warmup_imports: frozenset[str] = WARMUP_IMPORTS

    repl_command: list[str] = field(default_factory=lambda: ["lake", "exe", "repl"])

    max_buffer_bytes: int = 10 * 1024 * 1024
    mem_restart_ratio: float = 0.9
    validate_imports: bool = True

    # When True, snippets may import the project's own modules (datapoints), not
    # just Mathlib/Aesop/Batteries. Such imports are actually loaded into a
    # cached environment instead of being validated-then-dropped.
    allow_local_imports: bool = False


# ---------------------------------------------------------------------------
# Response formatting
# ---------------------------------------------------------------------------


def _adjust_line_numbers(resp: dict, offset: int) -> None:
    """Offset all pos.line values so they map back to original source."""
    if offset == 0:
        return
    for msg in resp.get("messages", []):
        pos = msg.get("pos")
        if pos and isinstance(pos, dict) and "line" in pos:
            pos["line"] = pos["line"] + offset
        end_pos = msg.get("endPos")
        if end_pos and isinstance(end_pos, dict) and "line" in end_pos:
            end_pos["line"] = end_pos["line"] + offset
    for sorry in resp.get("sorries", []):
        pos = sorry.get("pos")
        if pos and isinstance(pos, dict) and "line" in pos:
            pos["line"] = pos["line"] + offset
        end_pos = sorry.get("endPos")
        if end_pos and isinstance(end_pos, dict) and "line" in end_pos:
            end_pos["line"] = end_pos["line"] + offset


def format_message(msg: dict) -> str:
    """Format one REPL message: ``"3:5: error: unknown identifier"``."""
    severity = msg.get("severity", "info")
    data = msg.get("data", "")
    pos = msg.get("pos")

    if pos and isinstance(pos, dict):
        line = pos.get("line")
        column = pos.get("column")
        if line is not None:
            if column is not None:
                return f"{line}:{column}: {severity}: {data}"
            return f"{line}: {severity}: {data}"

    return f"{severity}: {data}"


def format_repl_response(response: dict[str, Any]) -> str:
    """Parse a raw REPL response and format it as readable diagnostics."""
    if response.get("repl_error") is not None:
        return f"REPL error: {response['repl_error']}"

    messages = response.get("messages", [])
    sorries_raw = response.get("sorries", [])

    errors: list[str] = []
    warnings: list[str] = []
    infos: list[str] = []
    for msg in messages:
        if not isinstance(msg, dict):
            continue
        sev = msg.get("severity", "")
        if sev == "error":
            errors.append(format_message(msg))
        elif sev == "warning":
            warnings.append(format_message(msg))
        elif sev == "info":
            infos.append(format_message(msg))

    sorries: list[dict[str, Any]] = []
    for s in sorries_raw:
        if not isinstance(s, dict):
            continue
        pos = s.get("pos", {})
        sorries.append(
            {
                "line": pos.get("line", 0) if isinstance(pos, dict) else 0,
                "goal": s.get("goal", ""),
            }
        )

    parts: list[str] = []

    if errors:
        parts.append(f"Compilation Errors ({len(errors)})")
        for e in errors:
            parts.append(f"  - {e}")
    elif warnings:
        parts.append("Compiles successfully")
        parts.append(f"\nWarnings ({len(warnings)})")
        for w in warnings[:DEFAULT_MAX_DIAGNOSTICS]:
            parts.append(f"  - {w}")
        if len(warnings) > DEFAULT_MAX_DIAGNOSTICS:
            parts.append(f"  ... and {len(warnings) - DEFAULT_MAX_DIAGNOSTICS} more")
    elif infos:
        parts.append("Compiles successfully")
        parts.append(f"\nOutput ({len(infos)})")
        for i in infos[:DEFAULT_MAX_DIAGNOSTICS]:
            parts.append(f"  - {i}")
        if len(infos) > DEFAULT_MAX_DIAGNOSTICS:
            parts.append(f"  ... and {len(infos) - DEFAULT_MAX_DIAGNOSTICS} more")
    else:
        parts.append("Compiles successfully")

    if sorries:
        parts.append(f"\nSorries ({len(sorries)})")
        for s in sorries:
            parts.append(f"  - Line {s['line']}: {s['goal']}")

    return "\n".join(parts)


# ---------------------------------------------------------------------------
# LeanRepl
# ---------------------------------------------------------------------------


class ReplProcessExited(RuntimeError):
    """Raised when the REPL process dies unexpectedly."""


class ReplProcessRestarted(RuntimeError):
    """Raised when the REPL restarts and env_id state is lost."""


class ImportEnvError(RuntimeError):
    """Raised when submitted imports fail to load (the process stays healthy)."""


class LeanRepl:
    """Lean REPL process manager.

    Manages a ``lake exe repl`` subprocess with non-blocking I/O,
    a preloaded import environment, and automatic restart on failure.
    """

    def __init__(self, config: LeanReplConfig) -> None:
        self.config = config
        self.cwd = config.cwd
        self.process: subprocess.Popen | None = None

        self.request_timeout = config.request_timeout
        self.max_retries = config.max_retries

        self._base_env_id: int | None = None
        self.chunk_size: int = config.chunk_size

        self.mem_limit_gb: int = config.instance_mem_limit_gb

        self._process_lock = threading.Lock()

        # env ids for non-warmup import sets, keyed by the frozenset of imports.
        self._import_env_cache: dict[frozenset[str], int] = {}

        self._allowed_import_roots: frozenset[str] | None = None
        if config.validate_imports and config.allowed_imports:
            self._allowed_import_roots = config.allowed_imports

    def start(self) -> None:
        """Start the Lean REPL process."""
        env = _inherit_clean_env()
        env.update(self.config.env)

        self.process = subprocess.Popen(
            self.config.repl_command,
            cwd=self.cwd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
        )

        try:
            if self.config.warmup_imports:
                header = "\n".join(f"import {root}" for root in self.config.warmup_imports)
                logger.info("Loading imports at startup: %s", self.config.warmup_imports)
                resp = self._run(code=header, env_id=None, timeout=self.config.startup_timeout)
                if "env" not in resp:
                    raise RuntimeError(f"Failed to preload imports: {resp}")

                errors = [m for m in resp.get("messages", []) if isinstance(m, dict) and m.get("severity") == "error"]
                if errors:
                    error_details = "\n".join(m.get("data", str(m)) for m in errors)
                    raise RuntimeError(f"Import preloading failed:\n{error_details}")

                self._base_env_id = resp["env"]

                smoke = self._run(code="#check Nat", env_id=self._base_env_id, timeout=DEFAULT_SMOKE_TEST_TIMEOUT)
                smoke_errors = [
                    m for m in smoke.get("messages", []) if isinstance(m, dict) and m.get("severity") == "error"
                ]
                if smoke_errors:
                    error_details = "; ".join(m.get("data", str(m)) for m in smoke_errors)
                    raise RuntimeError(
                        f"REPL smoke test failed — LEAN_PATH may be misconfigured. Errors: {error_details}"
                    )
        except Exception:
            self.close()
            raise

    def close(self) -> None:
        """Close the Lean REPL process."""
        try:
            if not self.process or self.process.poll() is not None:
                return
            _kill_subprocesses(self.process)
        finally:
            self.process = None
            self._base_env_id = None
            self._import_env_cache.clear()

    def restart(self) -> None:
        """Restart the Lean REPL process."""
        self.close()
        self.start()

    def is_alive(self) -> bool:
        """Check if the REPL process is alive."""
        return self.process is not None and self.process.poll() is None

    def get_memory_usage(self) -> float:
        """Return memory usage in GB."""
        return _get_process_memory_gb(self.process)

    def run(self, code: str, env_id: int | None = None, timeout: float | None = None) -> dict[str, Any]:
        """Send code to the REPL and get the response."""
        timeout = timeout or self.request_timeout
        run_from_env = env_id is not None
        max_retries = 0 if run_from_env else self.max_retries

        header_line_count = 0
        import_set: frozenset[str] = frozenset()
        needs_custom_env = False
        if not run_from_env:
            imports, code, header_line_count = _split_imports_and_body(code)

            if self.config.validate_imports and self._allowed_import_roots is not None:
                submitted_roots = {stmt.split(".")[0] for stmt in imports}
                disallowed = submitted_roots - self._allowed_import_roots
                if disallowed and not self.config.allow_local_imports:
                    return {
                        "repl_error": (
                            f"Disallowed imports: {', '.join(sorted(disallowed))}. "
                            f"Allowed roots: {', '.join(sorted(self._allowed_import_roots))}. "
                            f"Set LEAN_ALLOW_LOCAL_IMPORTS=1 to import the project's own modules."
                        )
                    }

            import_set = frozenset(imports)
            # When local imports are enabled and the snippet imports anything
            # beyond the warmed-up set, build (and cache) a dedicated env that
            # actually loads those modules — alongside Mathlib.
            needs_custom_env = (
                self.config.allow_local_imports
                and bool(import_set)
                and not (import_set <= self.config.warmup_imports)
            )
            env_id = self._base_env_id

        last_exception: Exception | None = None
        with self._process_lock:
            self._check_memory_and_maybe_restart()
            for i in range(max_retries + 1):
                try:
                    target_env = env_id
                    if needs_custom_env:
                        target_env = self._ensure_import_env(
                            self.config.warmup_imports | import_set, timeout
                        )
                    resp = self._run(code=code, env_id=target_env, timeout=timeout)
                    _adjust_line_numbers(resp, header_line_count)
                    return resp
                except ImportEnvError as e:
                    # The imports themselves failed to load; the process is fine,
                    # so surface the error without restarting.
                    return {"repl_error": str(e)}
                except ReplProcessExited as e:
                    last_exception = e
                    logger.error("REPL process exited: %s. Attempt %d/%d.", e, i + 1, max_retries + 1)
                    if not run_from_env and i < max_retries:
                        backoff = min(2**i, 30) + random.uniform(0, 1)
                        time.sleep(backoff)
                    self.restart()
                    if run_from_env:
                        raise ReplProcessRestarted(str(e)) from e
                except (TimeoutError, RuntimeError, json.JSONDecodeError) as e:
                    last_exception = e
                    logger.error("Error running command: %s. Attempt %d/%d.", e, i + 1, max_retries + 1)
                    if not run_from_env and i < max_retries:
                        backoff = min(2**i, 30) + random.uniform(0, 1)
                        time.sleep(backoff)
                    self.restart()
                    if run_from_env:
                        raise ReplProcessRestarted(str(e)) from e
            logger.error("Exceeded maximum retries for Lean REPL command")
            return {"repl_error": str(last_exception)}

    def _ensure_import_env(self, import_set: frozenset[str], timeout: float) -> int:
        """Return a cached env id that imports ``import_set``, creating it if needed.

        Building an env imports the modules from scratch (slow on first use, like
        the Mathlib warmup), so results are cached per import-set. Raises
        ImportEnvError if the imports fail to load — the process stays healthy.
        Must be called with ``self._process_lock`` held.
        """
        cached = self._import_env_cache.get(import_set)
        if cached is not None:
            return cached

        header = "\n".join(f"import {imp}" for imp in sorted(import_set))
        resp = self._run(code=header, env_id=None, timeout=max(timeout, self.config.startup_timeout))

        if "env" not in resp:
            raise ImportEnvError(f"Failed to import {', '.join(sorted(import_set))}: {resp}")
        errors = [m for m in resp.get("messages", []) if isinstance(m, dict) and m.get("severity") == "error"]
        if errors:
            details = "; ".join(m.get("data", str(m)) for m in errors)
            raise ImportEnvError(f"Import failed for {', '.join(sorted(import_set))}: {details}")

        env = resp["env"]
        self._import_env_cache[import_set] = env
        return env

    def _check_memory_and_maybe_restart(self) -> None:
        """Proactively restart if memory usage is near the limit."""
        if self.mem_limit_gb <= 0 or self.config.mem_restart_ratio <= 0:
            return
        try:
            usage_gb = self.get_memory_usage()
            threshold_gb = self.mem_limit_gb * self.config.mem_restart_ratio
            if usage_gb >= threshold_gb:
                logger.info("REPL memory %.2fGB >= threshold %.2fGB, restarting...", usage_gb, threshold_gb)
                self.restart()
        except Exception:
            logger.warning("Memory check failed, continuing", exc_info=True)

    def _run(self, code: str, env_id: int | None, timeout: float) -> dict[str, Any]:
        """Send code to the REPL via stdin JSON-RPC, read response via non-blocking I/O."""
        cmd_obj: dict[str, Any] = {"cmd": code}
        if env_id is not None:
            cmd_obj["env"] = env_id
        command = json.dumps(cmd_obj) + "\n\n"

        if self.process is None or self.process.poll() is not None:
            raise ReplProcessExited("REPL process is not running.")

        self.process.stdin.write(command.encode("utf-8"))
        self.process.stdin.flush()

        stdout_fd = self.process.stdout.fileno()
        stderr_fd = self.process.stderr.fileno()

        response_buffer = ""
        stderr_buffer = ""
        end_time = time.monotonic() + timeout
        max_buffer = self.config.max_buffer_bytes

        while True:
            remaining = end_time - time.monotonic()
            if remaining <= 0:
                raise TimeoutError(f"REPL command timed out after {timeout} seconds")

            ready, _, _ = select.select([stdout_fd, stderr_fd], [], [], remaining)
            if not ready:
                raise TimeoutError(f"REPL command timed out after {timeout} seconds")

            if stdout_fd in ready:
                chunk_bytes = os.read(stdout_fd, self.chunk_size)
                if not chunk_bytes:
                    raise ReplProcessExited(f"REPL process exited. stderr: {stderr_buffer}")
                chunk = chunk_bytes.decode("utf-8", errors="replace")
                response_buffer += chunk

                if len(response_buffer) > max_buffer:
                    raise RuntimeError(
                        f"REPL response exceeded {max_buffer} bytes. Tail: {response_buffer[-200:]!r}"
                    )

                if "\n\n" in response_buffer:
                    response_str, _ = response_buffer.split("\n\n", 1)
                    response_str = response_str.strip()
                    break

            if stderr_fd in ready:
                err_chunk_bytes = os.read(stderr_fd, self.chunk_size)
                if err_chunk_bytes:
                    err_chunk = err_chunk_bytes.decode("utf-8", errors="replace")
                    stderr_buffer += err_chunk
                    logger.debug("Lean REPL stderr: %s", err_chunk.rstrip())

        return json.loads(response_str)

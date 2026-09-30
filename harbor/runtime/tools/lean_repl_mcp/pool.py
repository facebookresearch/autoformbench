"""Lean REPL pool — thread pool of REPL instances with queue-based load balancing."""

from __future__ import annotations

import queue
import threading
from dataclasses import dataclass
from logging import getLogger
from typing import Any

from .core import LeanRepl, LeanReplConfig, ReplProcessRestarted

logger = getLogger(__name__)

DEFAULT_PORT = 8990
DEFAULT_RAM_FRACTION = 0.5
DEFAULT_STARTUP_STAGGER_SECONDS = 2.0


@dataclass
class LeanReplPoolConfig(LeanReplConfig):
    """Configuration for a pool of Lean REPL instances."""

    num_repls: int | None = None
    startup_stagger: float = DEFAULT_STARTUP_STAGGER_SECONDS

    def __post_init__(self) -> None:
        if self.num_repls is None:
            try:
                import psutil

                total_gb = psutil.virtual_memory().total / (1024**3)
                self.num_repls = max(1, int(total_gb * DEFAULT_RAM_FRACTION / self.instance_mem_limit_gb))
            except ImportError:
                self.num_repls = 1


class LeanReplPool:
    """Pool of Lean REPL instances with queue-based load balancing.

    Each worker thread owns its own LeanRepl subprocess. Tasks are
    distributed to idle workers via a FIFO queue.
    """

    def __init__(self, config: LeanReplPoolConfig) -> None:
        self.config = config
        self.capacity = config.num_repls or 1
        self._shutdown = False

        self._workers: list[LeanRepl] = []
        self._idle: queue.Queue[LeanRepl] = queue.Queue()
        self._lock = threading.Lock()

        for i in range(self.capacity):
            if i > 0:
                import time

                time.sleep(config.startup_stagger)
            repl = LeanRepl(config)
            repl.start()
            self._workers.append(repl)
            self._idle.put(repl)

    def run(self, code: str, **kwargs: Any) -> dict[str, Any]:
        """Run code on an idle REPL, retrying once on restart."""
        repl = self._idle.get()
        try:
            try:
                return repl.run(code, **kwargs)
            except ReplProcessRestarted:
                logger.info("REPL was restarted, retrying command...")
                return repl.run(code, **kwargs)
        finally:
            self._idle.put(repl)

    def get_memory_usage(self) -> float:
        """Total memory usage across all REPL instances in GB."""
        return sum(w.get_memory_usage() for w in self._workers)

    def shutdown(self) -> None:
        """Shut down all REPL instances."""
        self._shutdown = True
        for worker in self._workers:
            worker.close()
        self._workers.clear()

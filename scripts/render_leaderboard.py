#!/usr/bin/env python3
"""Render the public leaderboard as a Markdown table."""

from __future__ import annotations

import csv
import json
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FULL_TOTAL = 341
PUBLIC_TOTAL = 241
PRIVATE_TOTAL = 100

DISPLAY_NAMES = {
    "deepseek-v4.1-flash": "DeepSeek V4.1 Flash",
    "fable-5": "Fable 5",
    "fable-5.1": "Fable 5.1",
    "gemini-3.7-flash": "Gemini 3.7 Flash",
    "gemini-3.8-flash": "Gemini 3.8 Flash",
    "gpt-5.6-sol": "GPT-5.6 Sol",
    "gpt-6-astra": "GPT-6 Astra",
    "kimi-k3": "Kimi K3",
    "muse-spark-1.3": "Muse Spark 1.3",
    "opus-4.8": "Opus 4.8",
    "opus-5": "Opus 5",
    "sonnet-5": "Sonnet 5",
}


@dataclass(frozen=True)
class Result:
    slug: str
    full_solved: int
    public_solved: int
    private_solved: int


def load_results() -> list[Result]:
    summary = json.loads(
        (ROOT / "audit/public_private_split_summary.json").read_text()
    )
    aggregate = {
        row["model"]: row
        for row in (
            summary["primary_model_performance"]
            + summary["secondary_model_performance"]
        )
    }
    results = []
    for path in sorted((ROOT / "leaderboard_data").glob("*.csv")):
        with path.open(newline="", encoding="utf-8") as handle:
            rows = list(csv.DictReader(handle))
        if len(rows) != PUBLIC_TOTAL:
            raise ValueError(
                f"{path.name}: expected {PUBLIC_TOTAL} rows, found {len(rows)}"
            )
        public_solved = sum(
            row["passed"].strip().lower() == "true" for row in rows
        )
        row = aggregate[path.stem]
        if public_solved != row["public_solved"]:
            raise ValueError(f"{path.name}: public aggregate does not match CSV")
        results.append(
            Result(
                slug=path.stem,
                full_solved=row["full_solved"],
                public_solved=public_solved,
                private_solved=row["private_solved"],
            )
        )
    if set(aggregate) != {result.slug for result in results}:
        raise ValueError("aggregate leaderboard and public CSV model sets differ")
    return sorted(results, key=lambda result: (-result.full_solved, result.slug))


def render() -> str:
    lines = [
        "| Rank | Model | Full benchmark | Public | Private | Public results |",
        "| ---: | --- | ---: | ---: | ---: | --- |",
    ]
    previous_solved = None
    rank = 0
    for index, result in enumerate(load_results(), start=1):
        if result.full_solved != previous_solved:
            rank = index
        previous_solved = result.full_solved
        name = DISPLAY_NAMES.get(result.slug, result.slug)
        lines.append(
            f"| {rank} | {name} | "
            f"{result.full_solved} / {FULL_TOTAL} "
            f"({100 * result.full_solved / FULL_TOTAL:.1f}%) | "
            f"{result.public_solved} / {PUBLIC_TOTAL} "
            f"({100 * result.public_solved / PUBLIC_TOTAL:.1f}%) | "
            f"{result.private_solved} / {PRIVATE_TOTAL} "
            f"({100 * result.private_solved / PRIVATE_TOTAL:.1f}%) | "
            f"[CSV](leaderboard_data/{result.slug}.csv) |"
        )
    return "\n".join(lines)


if __name__ == "__main__":
    print(render())

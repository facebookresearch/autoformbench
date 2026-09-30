#!/usr/bin/env python3
"""Deterministically export the final AutoformBench corpus as Harbor tasks.

The canonical inputs are ``MANIFEST.csv``, ``SOURCES.csv``, and
``workspaces/`` in the enclosing release bundle. Generated tasks are source-free: source citations are
recorded as metadata, but textbook files are never copied into an agent image.

Usage::

    python harbor/export.py --all
    python harbor/export.py --problem <problem-id>
    python harbor/export.py --check
    python harbor/export.py --check --problem <problem-id>

``--check`` is read-only.  It validates target parity, workspace hashes, task
structure, and byte-for-byte deterministic regeneration.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import tomllib
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path

FINAL_BENCHMARK_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_TASKS_ROOT = Path(__file__).resolve().parent / "tasks"
TEMPLATES_ROOT = Path(__file__).resolve().parent / "templates"

SCHEMA_VERSION = "1.4"
GENERATOR_VERSION = "1"
MARKER = ".autoformbench-harbor-generated"
PROBLEM_ID_RE = re.compile(r"^[A-Za-z0-9_-]+$")
HEX_REV_RE = re.compile(r"^[0-9a-f]{40}$")

MANIFEST_FIELDS = (
    "problem_id",
    "book",
    "target_count",
    "target_declarations",
)
SOURCE_FIELDS = ("book", "title", "authors", "url")

# These are the only canonical files exposed to the solver.  In particular,
# config.json, holes.json, WorkspaceTest.lean, and README.md stay inside the
# trusted verifier image.
AGENT_FILES = (
    "Challenge.lean",
    "Solution.lean",
    "Submission.lean",
    "Submission/Helpers.lean",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
)
OPTIONAL_AGENT_FILES = ("ChallengeDeps.lean",)

CANONICAL_FILES = frozenset(
    {
        *AGENT_FILES,
        *OPTIONAL_AGENT_FILES,
        "README.md",
        "WorkspaceTest.lean",
        "config.json",
        "holes.json",
    }
)
REQUIRED_CANONICAL_FILES = frozenset(CANONICAL_FILES - set(OPTIONAL_AGENT_FILES))


class ExportError(RuntimeError):
    """The canonical release or generated Harbor export is inconsistent."""


@dataclass(frozen=True)
class Source:
    book: str
    title: str
    authors: str
    url: str


@dataclass(frozen=True)
class Problem:
    problem_id: str
    book: str
    targets: tuple[str, ...]
    workspace: Path
    source: Source
    workspace_sha256: str
    agent_payload_sha256: str
    targets_sha256: str
    manifest_row_sha256: str
    source_row_sha256: str
    lean_toolchain: str
    mathlib_revision: str

    @property
    def agent_files(self) -> tuple[str, ...]:
        files = list(AGENT_FILES)
        files.extend(
            relative
            for relative in OPTIONAL_AGENT_FILES
            if (self.workspace / relative).is_file()
        )
        return tuple(sorted(files))

    @property
    def image_suffix(self) -> str:
        lean = self.lean_toolchain.rsplit(":", 1)[-1].removeprefix("v")
        return f"lean{lean}-mathlib-{self.mathlib_revision[:8]}"

    @property
    def agent_image(self) -> str:
        return f"autoformbench-agent:{self.image_suffix}"

    @property
    def verifier_image(self) -> str:
        return f"autoformbench-verifier:{self.image_suffix}"


@dataclass(frozen=True)
class Benchmark:
    root: Path
    problems: Mapping[str, Problem]
    sources: Mapping[str, Source]


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _canonical_json(value: object) -> bytes:
    return json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")


def _row_hash(row: Mapping[str, str], fields: Sequence[str]) -> str:
    return _sha256(_canonical_json({field: row[field] for field in fields}))


def _tree_entries(root: Path) -> list[tuple[str, bytes]]:
    """Return a sorted regular-file snapshot, rejecting unsafe entries."""

    if not root.is_dir() or root.is_symlink():
        raise ExportError(f"Expected a real directory: {root}")

    entries: list[tuple[str, bytes]] = []
    for path in sorted(root.rglob("*"), key=lambda item: item.relative_to(root).as_posix()):
        relative = path.relative_to(root).as_posix()
        mode = path.lstat().st_mode
        if stat.S_ISLNK(mode):
            raise ExportError(f"Symbolic links are not allowed: {path}")
        if stat.S_ISDIR(mode):
            continue
        if not stat.S_ISREG(mode):
            raise ExportError(f"Special filesystem entry is not allowed: {path}")
        entries.append((relative, path.read_bytes()))
    return entries


def tree_hash(root: Path, relative_files: Iterable[str] | None = None) -> str:
    selected = None if relative_files is None else frozenset(relative_files)
    digest = hashlib.sha256()
    seen: set[str] = set()
    for relative, contents in _tree_entries(root):
        if selected is not None and relative not in selected:
            continue
        seen.add(relative)
        encoded = relative.encode("utf-8")
        digest.update(len(encoded).to_bytes(4, "big"))
        digest.update(encoded)
        digest.update(len(contents).to_bytes(8, "big"))
        digest.update(contents)
    if selected is not None and seen != selected:
        raise ExportError(
            f"Cannot hash missing files under {root}: {sorted(selected - seen)}"
        )
    return digest.hexdigest()


def file_manifest(root: Path) -> dict[str, tuple[str, int]]:
    """Hash generated files and record normalized modes for drift checks."""

    if not root.exists():
        return {}
    manifest: dict[str, tuple[str, int]] = {}
    for path in sorted(root.rglob("*"), key=lambda item: item.relative_to(root).as_posix()):
        mode = path.lstat().st_mode
        if stat.S_ISDIR(mode):
            continue
        relative = path.relative_to(root).as_posix()
        if not stat.S_ISREG(mode):
            raise ExportError(f"Generated task contains an unsafe entry: {path}")
        manifest[relative] = (_sha256(path.read_bytes()), stat.S_IMODE(mode))
    return manifest


def _read_csv(path: Path, expected_fields: Sequence[str]) -> list[dict[str, str]]:
    try:
        with path.open(newline="", encoding="utf-8") as handle:
            reader = csv.DictReader(handle)
            if tuple(reader.fieldnames or ()) != tuple(expected_fields):
                raise ExportError(
                    f"Unexpected columns in {path}: {reader.fieldnames!r}; "
                    f"expected {tuple(expected_fields)!r}"
                )
            rows = []
            for line_number, row in enumerate(reader, start=2):
                if None in row or any(
                    not isinstance(row.get(field), str) for field in expected_fields
                ):
                    raise ExportError(f"Malformed CSV row in {path}:{line_number}")
                rows.append({field: row[field] for field in expected_fields})
    except OSError as error:
        raise ExportError(f"Cannot read {path}: {error}") from error
    if not rows:
        raise ExportError(f"CSV file is empty: {path}")
    return rows


def _load_sources(root: Path) -> dict[str, tuple[Source, str]]:
    path = root / "SOURCES.csv"
    result: dict[str, tuple[Source, str]] = {}
    for row in _read_csv(path, SOURCE_FIELDS):
        book = row["book"]
        if not isinstance(book, str) or not PROBLEM_ID_RE.fullmatch(book):
            raise ExportError(f"Invalid book slug in {path}: {book!r}")
        if book in result:
            raise ExportError(f"Duplicate book in {path}: {book}")
        if not row["title"] or not row["authors"]:
            raise ExportError(f"Incomplete source metadata for book {book}")
        if not re.match(r"^https?://", row["url"]):
            raise ExportError(f"Source URL must be HTTP(S) for book {book}")
        source = Source(book, row["title"], row["authors"], row["url"])
        result[book] = (source, _row_hash(row, SOURCE_FIELDS))
    return result


def _load_json(path: Path) -> object:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ExportError(f"Invalid JSON file {path}: {error}") from error


def _validate_workspace_files(workspace: Path, problem_id: str) -> set[str]:
    actual = {relative for relative, _ in _tree_entries(workspace)}
    directories = {
        path.relative_to(workspace).as_posix()
        for path in workspace.rglob("*")
        if path.is_dir() and not path.is_symlink()
    }
    missing = REQUIRED_CANONICAL_FILES - actual
    unexpected = actual - CANONICAL_FILES
    unexpected_directories = directories - {"Submission"}
    if missing or unexpected or unexpected_directories:
        raise ExportError(
            f"{problem_id}: canonical workspace file set mismatch; "
            f"missing={sorted(missing)}, unexpected={sorted(unexpected)}, "
            f"unexpected_directories={sorted(unexpected_directories)}"
        )
    return actual


def _load_toolchain(workspace: Path, problem_id: str) -> tuple[str, str]:
    lean = (workspace / "lean-toolchain").read_text(encoding="utf-8").strip()
    if not lean.startswith("leanprover/lean4:v"):
        raise ExportError(f"{problem_id}: unexpected Lean toolchain {lean!r}")
    manifest = _load_json(workspace / "lake-manifest.json")
    if not isinstance(manifest, dict) or not isinstance(manifest.get("packages"), list):
        raise ExportError(f"{problem_id}: malformed lake-manifest.json")
    mathlib = [
        package
        for package in manifest["packages"]
        if isinstance(package, dict) and package.get("name") == "mathlib"
    ]
    if len(mathlib) != 1 or not isinstance(mathlib[0].get("rev"), str):
        raise ExportError(f"{problem_id}: Mathlib revision is missing or ambiguous")
    revision = mathlib[0]["rev"]
    if not HEX_REV_RE.fullmatch(revision):
        raise ExportError(f"{problem_id}: invalid Mathlib revision {revision!r}")
    return lean, revision


def _validate_targets(
    workspace: Path,
    problem_id: str,
    targets: tuple[str, ...],
) -> None:
    config = _load_json(workspace / "config.json")
    holes_data = _load_json(workspace / "holes.json")
    if not isinstance(config, dict):
        raise ExportError(f"{problem_id}: config.json must contain an object")
    configured = config.get("theorem_names")
    if configured != list(targets):
        raise ExportError(
            f"{problem_id}: MANIFEST targets do not exactly match config.json; "
            f"manifest={list(targets)!r}, config={configured!r}"
        )
    if not isinstance(holes_data, dict) or holes_data.get("id") != problem_id:
        raise ExportError(f"{problem_id}: holes.json has the wrong problem ID")
    holes = holes_data.get("holes")
    if not isinstance(holes, list) or len(holes) != len(targets):
        raise ExportError(
            f"{problem_id}: hole count does not match MANIFEST target count"
        )
    for index, (target, hole) in enumerate(zip(targets, holes)):
        if not isinstance(hole, dict):
            raise ExportError(f"{problem_id}: hole {index} is not an object")
        if target not in {hole.get("name"), hole.get("basename")}:
            raise ExportError(
                f"{problem_id}: target {target!r} does not match hole {index} "
                f"({hole.get('name')!r}, {hole.get('basename')!r})"
            )


def load_benchmark(root: Path = FINAL_BENCHMARK_ROOT) -> Benchmark:
    root = root.resolve()
    workspaces_root = root / "workspaces"
    if not workspaces_root.is_dir() or workspaces_root.is_symlink():
        raise ExportError(f"Missing canonical workspace directory: {workspaces_root}")

    sources_with_hashes = _load_sources(root)
    manifest_path = root / "MANIFEST.csv"
    problems: dict[str, Problem] = {}
    for row in _read_csv(manifest_path, MANIFEST_FIELDS):
        problem_id = row["problem_id"]
        if not isinstance(problem_id, str) or not PROBLEM_ID_RE.fullmatch(problem_id):
            raise ExportError(f"Invalid problem ID in {manifest_path}: {problem_id!r}")
        if problem_id in problems:
            raise ExportError(f"Duplicate problem ID in {manifest_path}: {problem_id}")
        book = row["book"]
        if book not in sources_with_hashes:
            raise ExportError(f"{problem_id}: book {book!r} is absent from SOURCES.csv")
        try:
            target_count = int(row["target_count"])
        except (TypeError, ValueError) as error:
            raise ExportError(f"{problem_id}: invalid target_count") from error
        declarations = row["target_declarations"]
        if not isinstance(declarations, str):
            raise ExportError(f"{problem_id}: missing target declarations")
        targets = tuple(declarations.split(";"))
        if (
            target_count <= 0
            or len(targets) != target_count
            or any(not target or target.strip() != target for target in targets)
            or len(set(targets)) != len(targets)
        ):
            raise ExportError(f"{problem_id}: malformed target declaration list")

        workspace = workspaces_root / problem_id
        actual_files = _validate_workspace_files(workspace, problem_id)
        _validate_targets(workspace, problem_id, targets)
        lean, mathlib = _load_toolchain(workspace, problem_id)
        agent_files = tuple(
            sorted(
                {
                    *AGENT_FILES,
                    *(
                        relative
                        for relative in OPTIONAL_AGENT_FILES
                        if relative in actual_files
                    ),
                }
            )
        )
        source, source_hash = sources_with_hashes[book]
        problems[problem_id] = Problem(
            problem_id=problem_id,
            book=book,
            targets=targets,
            workspace=workspace,
            source=source,
            workspace_sha256=tree_hash(workspace),
            agent_payload_sha256=tree_hash(workspace, agent_files),
            targets_sha256=_sha256(_canonical_json(list(targets))),
            manifest_row_sha256=_row_hash(row, MANIFEST_FIELDS),
            source_row_sha256=source_hash,
            lean_toolchain=lean,
            mathlib_revision=mathlib,
        )

    actual_workspace_ids: set[str] = set()
    for path in workspaces_root.iterdir():
        if path.is_symlink() or not path.is_dir():
            raise ExportError(f"Unexpected entry in workspaces/: {path}")
        actual_workspace_ids.add(path.name)
    if actual_workspace_ids != set(problems):
        raise ExportError(
            "MANIFEST/workspace set mismatch; "
            f"missing={sorted(set(problems) - actual_workspace_ids)}, "
            f"extra={sorted(actual_workspace_ids - set(problems))}"
        )

    used_books = {problem.book for problem in problems.values()}
    if used_books != set(sources_with_hashes):
        raise ExportError(
            "MANIFEST/SOURCES book set mismatch; "
            f"missing={sorted(used_books - set(sources_with_hashes))}, "
            f"extra={sorted(set(sources_with_hashes) - used_books)}"
        )
    sources = {book: value[0] for book, value in sources_with_hashes.items()}
    return Benchmark(root=root, problems=problems, sources=sources)


def _toml_string(value: str) -> str:
    # JSON strings use the TOML basic-string escapes needed by these values.
    return json.dumps(value, ensure_ascii=False)


def _toml_list(values: Iterable[str]) -> str:
    return "[" + ", ".join(_toml_string(value) for value in values) + "]"


def _description(problem: Problem) -> str:
    return (
        f"Prove {len(problem.targets)} Lean target"
        f"{'s' if len(problem.targets) != 1 else ''} from {problem.source.title}"
    )


def _render_template(relative: str, replacements: Mapping[str, str]) -> str:
    path = TEMPLATES_ROOT / relative
    try:
        rendered = path.read_text(encoding="utf-8")
    except OSError as error:
        raise ExportError(f"Cannot read Harbor template {path}: {error}") from error
    for name, value in replacements.items():
        rendered = rendered.replace("{{ " + name + " }}", value)
    unresolved = sorted(set(re.findall(r"{{\s*([^{}]+?)\s*}}", rendered)))
    if unresolved:
        raise ExportError(f"Unresolved placeholders in {path}: {unresolved}")
    if not rendered.endswith("\n"):
        rendered += "\n"
    return rendered


def _instruction(problem: Problem) -> str:
    noun = "declaration" if len(problem.targets) == 1 else "declarations"
    return _render_template(
        "instruction.md",
        {
            "problem_id": problem.problem_id,
            "title": _description(problem),
            "hole_summary": f"{len(problem.targets)} incomplete {noun}",
        },
    )


def _task_toml(problem: Problem) -> str:
    rendered = _render_template(
        "task.toml",
        {
            "task_name_toml": _toml_string(f"autoformbench/{problem.problem_id}"),
            "description_toml": _toml_string(_description(problem)),
            "book_toml": _toml_string(problem.book),
        },
    )
    integrity = f"""
[metadata.integrity]
problem_id = {_toml_string(problem.problem_id)}
source_included = false
target_count = {len(problem.targets)}
target_declarations = {_toml_list(problem.targets)}
workspace_sha256 = {_toml_string(problem.workspace_sha256)}
agent_payload_sha256 = {_toml_string(problem.agent_payload_sha256)}
targets_sha256 = {_toml_string(problem.targets_sha256)}
manifest_row_sha256 = {_toml_string(problem.manifest_row_sha256)}
source_row_sha256 = {_toml_string(problem.source_row_sha256)}

[metadata.source]
title = {_toml_string(problem.source.title)}
authors = {_toml_string(problem.source.authors)}
url = {_toml_string(problem.source.url)}

[metadata.toolchain]
lean = {_toml_string(problem.lean_toolchain)}
mathlib = {_toml_string(problem.mathlib_revision)}
agent_image = {_toml_string(problem.agent_image)}
verifier_image = {_toml_string(problem.verifier_image)}
harbor_schema = {_toml_string(SCHEMA_VERSION)}
"""
    return rendered + integrity


def _agent_dockerfile(problem: Problem) -> str:
    rendered = _render_template("Dockerfile", {})
    expected = f"ARG AGENT_IMAGE={problem.agent_image}"
    if expected not in rendered.splitlines():
        raise ExportError(
            f"Agent image template does not match {problem.problem_id}'s toolchain: "
            f"expected {expected!r}"
        )
    return rendered


def _test_dockerfile(problem: Problem) -> str:
    rendered = _render_template("tests/Dockerfile", {})
    expected = f"ARG VERIFIER_IMAGE={problem.verifier_image}"
    if expected not in rendered.splitlines():
        raise ExportError(
            f"Verifier image template does not match {problem.problem_id}'s toolchain: "
            f"expected {expected!r}"
        )
    return rendered


def _test_script(problem: Problem) -> str:
    return _render_template("tests/test.sh", {"problem_id": problem.problem_id})


def _marker(kind: str) -> str:
    return (
        "Generated by harbor/export.py; do not edit.\n"
        f"generator_version={GENERATOR_VERSION}\n"
        f"kind={kind}\n"
    )


def _make_directory(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)
    path.chmod(0o755)


def _write(path: Path, data: str | bytes, *, executable: bool = False) -> None:
    _make_directory(path.parent)
    payload = data.encode("utf-8") if isinstance(data, str) else data
    path.write_bytes(payload)
    path.chmod(0o755 if executable else 0o644)


def build_task(destination: Path, problem: Problem) -> None:
    if destination.exists():
        raise ExportError(f"Refusing to generate over existing task: {destination}")
    _make_directory(destination)
    _write(destination / MARKER, _marker("task"))
    _write(destination / "instruction.md", _instruction(problem))
    _write(destination / "task.toml", _task_toml(problem))
    _write(destination / "environment/Dockerfile", _agent_dockerfile(problem))
    for relative in problem.agent_files:
        _write(
            destination / "environment/workspace" / relative,
            (problem.workspace / relative).read_bytes(),
        )
    _write(destination / "tests/Dockerfile", _test_dockerfile(problem))
    _write(destination / "tests/test.sh", _test_script(problem), executable=True)
    validate_task(destination, problem)


def _validate_task_metadata(task: Path, problem: Problem) -> None:
    try:
        data = tomllib.loads((task / "task.toml").read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
        raise ExportError(f"{problem.problem_id}: invalid generated task.toml: {error}") from error
    if data.get("schema_version") != SCHEMA_VERSION:
        raise ExportError(f"{problem.problem_id}: wrong Harbor schema version")
    if data.get("task", {}).get("name") != f"autoformbench/{problem.problem_id}":
        raise ExportError(f"{problem.problem_id}: wrong Harbor task identity")
    metadata = data.get("metadata", {})
    integrity = metadata.get("integrity", {})
    expected = {
        "problem_id": problem.problem_id,
        "source_included": False,
        "target_count": len(problem.targets),
        "target_declarations": list(problem.targets),
        "workspace_sha256": problem.workspace_sha256,
        "agent_payload_sha256": problem.agent_payload_sha256,
        "targets_sha256": problem.targets_sha256,
        "manifest_row_sha256": problem.manifest_row_sha256,
        "source_row_sha256": problem.source_row_sha256,
    }
    mismatches = {
        key: (integrity.get(key), value)
        for key, value in expected.items()
        if integrity.get(key) != value
    }
    if mismatches:
        raise ExportError(
            f"{problem.problem_id}: generated metadata is stale: {mismatches}"
        )
    artifacts = [entry.get("source") for entry in data.get("artifacts", [])]
    if artifacts != ["/app/Submission.lean", "/app/Submission"]:
        raise ExportError(f"{problem.problem_id}: unexpected artifact boundary")
    if metadata.get("source_condition") != "source-free":
        raise ExportError(f"{problem.problem_id}: task is not source-free")
    if data.get("verifier", {}).get("environment_mode") != "separate":
        raise ExportError(f"{problem.problem_id}: verifier is not isolated")


def _validate_agent_payload(task: Path, problem: Problem) -> None:
    generated = task / "environment/workspace"
    generated_entries = _tree_entries(generated)
    generated_files = {relative for relative, _ in generated_entries}
    if generated_files != set(problem.agent_files):
        raise ExportError(
            f"{problem.problem_id}: agent file set mismatch; "
            f"missing={sorted(set(problem.agent_files) - generated_files)}, "
            f"extra={sorted(generated_files - set(problem.agent_files))}"
        )
    for relative, contents in generated_entries:
        canonical = (problem.workspace / relative).read_bytes()
        if contents != canonical:
            raise ExportError(
                f"{problem.problem_id}: copied agent file changed: {relative}"
            )
    if tree_hash(generated) != problem.agent_payload_sha256:
        raise ExportError(f"{problem.problem_id}: agent payload hash mismatch")


def validate_task(task: Path, problem: Problem) -> None:
    required = {
        MARKER,
        "instruction.md",
        "task.toml",
        "environment/Dockerfile",
        "tests/Dockerfile",
        "tests/test.sh",
        *(f"environment/workspace/{relative}" for relative in problem.agent_files),
    }
    actual = {relative for relative, _ in _tree_entries(task)}
    if actual != required:
        raise ExportError(
            f"{problem.problem_id}: generated task file set mismatch; "
            f"missing={sorted(required - actual)}, extra={sorted(actual - required)}"
        )
    if (task / MARKER).read_text(encoding="utf-8") != _marker("task"):
        raise ExportError(f"{problem.problem_id}: invalid generated-task marker")
    _validate_task_metadata(task, problem)
    _validate_agent_payload(task, problem)
    shell = subprocess.run(
        ["bash", "-n", str(task / "tests/test.sh")],
        capture_output=True,
        text=True,
        check=False,
    )
    if shell.returncode:
        raise ExportError(
            f"{problem.problem_id}: invalid verifier shell script: {shell.stderr}"
        )


def _require_marker(path: Path, kind: str) -> None:
    if path.is_symlink() or not path.is_dir():
        raise ExportError(f"Refusing to replace non-directory output: {path}")
    marker = path / MARKER
    if (
        marker.is_symlink()
        or not marker.is_file()
        or marker.read_text(encoding="utf-8") != _marker(kind)
    ):
        raise ExportError(f"Refusing to replace unmanaged output: {path}")


def _atomic_replace(source: Path, destination: Path, kind: str) -> None:
    backup = destination.parent / f".{destination.name}.autoformbench-backup"
    if backup.exists() or backup.is_symlink():
        raise ExportError(f"Stale export backup requires inspection: {backup}")
    moved_old = False
    if destination.exists() or destination.is_symlink():
        _require_marker(destination, kind)
        destination.rename(backup)
        moved_old = True
    try:
        source.rename(destination)
    except Exception:
        if moved_old and backup.exists():
            backup.rename(destination)
        raise
    else:
        if moved_old:
            shutil.rmtree(backup)


def _build_all_tree(destination: Path, benchmark: Benchmark) -> None:
    _make_directory(destination)
    _write(destination / MARKER, _marker("task-set"))
    for problem_id in sorted(benchmark.problems):
        build_task(destination / problem_id, benchmark.problems[problem_id])


def export_all(benchmark: Benchmark, tasks_root: Path = DEFAULT_TASKS_ROOT) -> None:
    tasks_root = tasks_root.resolve()
    _make_directory(tasks_root.parent)
    with tempfile.TemporaryDirectory(
        prefix=".autoformbench-harbor-export-", dir=tasks_root.parent
    ) as temporary:
        staged = Path(temporary) / "tasks"
        _build_all_tree(staged, benchmark)
        _atomic_replace(staged, tasks_root, "task-set")
    print(f"Exported {len(benchmark.problems)} Harbor tasks to {tasks_root}.")


def export_problem(
    benchmark: Benchmark,
    problem_id: str,
    tasks_root: Path = DEFAULT_TASKS_ROOT,
) -> None:
    if problem_id not in benchmark.problems:
        raise ExportError(f"Problem is not in the release manifest: {problem_id}")
    tasks_root = tasks_root.resolve()
    if tasks_root.exists() or tasks_root.is_symlink():
        _require_marker(tasks_root, "task-set")
    else:
        _make_directory(tasks_root)
        _write(tasks_root / MARKER, _marker("task-set"))

    destination = tasks_root / problem_id
    if destination.exists() or destination.is_symlink():
        _require_marker(destination, "task")
    with tempfile.TemporaryDirectory(
        prefix=f".{problem_id}.autoformbench-export-", dir=tasks_root.parent
    ) as temporary:
        staged = Path(temporary) / problem_id
        build_task(staged, benchmark.problems[problem_id])
        _atomic_replace(staged, destination, "task")
    print(f"Exported {problem_id} to {destination}.")


def _describe_manifest_difference(
    expected: Mapping[str, tuple[str, int]],
    actual: Mapping[str, tuple[str, int]],
) -> str:
    missing = sorted(set(expected) - set(actual))[:10]
    extra = sorted(set(actual) - set(expected))[:10]
    changed = sorted(
        path
        for path in set(expected) & set(actual)
        if expected[path] != actual[path]
    )[:10]
    return f"missing={missing}, extra={extra}, changed={changed}"


def check_export(
    benchmark: Benchmark,
    tasks_root: Path = DEFAULT_TASKS_ROOT,
    problem_id: str | None = None,
) -> None:
    tasks_root = tasks_root.resolve()
    _require_marker(tasks_root, "task-set")
    if problem_id is not None:
        if problem_id not in benchmark.problems:
            raise ExportError(f"Problem is not in the release manifest: {problem_id}")
        actual_root = tasks_root / problem_id
        validate_task(actual_root, benchmark.problems[problem_id])
        with tempfile.TemporaryDirectory(prefix="autoformbench-harbor-check-") as temp:
            expected_root = Path(temp) / problem_id
            build_task(expected_root, benchmark.problems[problem_id])
            expected = file_manifest(expected_root)
        actual = file_manifest(actual_root)
        if expected != actual:
            raise ExportError(
                f"{problem_id}: generated task is not current/deterministic; "
                + _describe_manifest_difference(expected, actual)
            )
        print(f"OK: {problem_id} matches its canonical workspace and manifest.")
        return

    actual_ids = {
        path.name
        for path in tasks_root.iterdir()
        if path.is_dir() and not path.is_symlink()
    }
    expected_ids = set(benchmark.problems)
    if actual_ids != expected_ids:
        raise ExportError(
            "Generated task set does not match MANIFEST; "
            f"missing={sorted(expected_ids - actual_ids)}, "
            f"extra={sorted(actual_ids - expected_ids)}"
        )
    for problem_id_ in sorted(expected_ids):
        validate_task(tasks_root / problem_id_, benchmark.problems[problem_id_])

    with tempfile.TemporaryDirectory(prefix="autoformbench-harbor-check-") as temp:
        expected_root = Path(temp) / "tasks"
        _build_all_tree(expected_root, benchmark)
        expected = file_manifest(expected_root)
    actual = file_manifest(tasks_root)
    if expected != actual:
        raise ExportError(
            "Generated Harbor export is not current/deterministic; "
            + _describe_manifest_difference(expected, actual)
        )
    print(
        f"OK: {len(expected_ids)} Harbor tasks match canonical targets, hashes, "
        "and deterministic regeneration."
    )


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--all", action="store_true", help="export every task")
    selection.add_argument("--problem", metavar="ID", help="select one problem")
    parser.add_argument(
        "--check",
        action="store_true",
        help="validate generated tasks without modifying them (all by default)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_TASKS_ROOT,
        help="generated tasks directory (default: harbor/tasks in this bundle)",
    )
    args = parser.parse_args(argv)
    if not args.check and not args.all and args.problem is None:
        parser.error("choose --all or --problem ID when not using --check")
    return args


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        benchmark = load_benchmark()
        if args.check:
            check_export(benchmark, args.output, args.problem)
        elif args.all:
            export_all(benchmark, args.output)
        else:
            export_problem(benchmark, args.problem, args.output)
    except ExportError as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

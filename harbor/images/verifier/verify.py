#!/usr/bin/env python3
"""Clean-room Harbor verifier for AutoformBench submissions."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import stat
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path


BENCHMARK_ROOT = Path("/opt/autoformbench-benchmark")
TRUSTED_WORKSPACES = BENCHMARK_ROOT / "workspaces"
SUBMISSION_ROOT = Path("/app")
OUTPUT_ROOT = Path("/logs/verifier")
PROBLEM_ID_PATTERN = re.compile(r"^[A-Za-z0-9_-]+$")
MAX_HELPER_FILES = 10_000
MAX_SUBMISSION_BYTES = 512 * 1024 * 1024
SHARED_PACKAGES = Path("/opt/autoformbench/packages")
SHARED_MANIFEST = Path(
    "/opt/autoformbench/tools/lean-project/lake-manifest.json"
)
COMPARATOR = Path("/usr/local/bin/comparator")
LEAN4EXPORT = Path("/usr/local/bin/lean4export")
NANODA = Path("/usr/local/bin/nanoda_bin")
LANDRUN = Path("/usr/local/bin/landrun")
COMPARATOR_TIMEOUT_SECONDS = 5_700


class SubmissionRejected(Exception):
    """The uploaded artifact is not a valid AutoformBench submission."""


class VerifierFailure(Exception):
    """Trusted verifier infrastructure is missing or malfunctioning."""

    def __init__(self, message: str, grade_output: str = "") -> None:
        super().__init__(message)
        self.grade_output = grade_output


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Verify one AutoformBench Harbor submission."
    )
    parser.add_argument("problem_id", help="Canonical AutoformBench problem ID")
    return parser.parse_args()


def regular_file_size(path: Path, label: str) -> int:
    try:
        metadata = path.lstat()
    except FileNotFoundError as error:
        raise SubmissionRejected(f"Missing required file: {label}") from error
    if not stat.S_ISREG(metadata.st_mode):
        raise SubmissionRejected(f"Expected a regular file: {label}")
    return metadata.st_size


def validate_submission() -> tuple[int, int]:
    submission_file = SUBMISSION_ROOT / "Submission.lean"
    total_bytes = regular_file_size(submission_file, "Submission.lean")
    helper_count = 0
    helper_root = SUBMISSION_ROOT / "Submission"

    if helper_root.exists() or helper_root.is_symlink():
        helper_metadata = helper_root.lstat()
        if not stat.S_ISDIR(helper_metadata.st_mode):
            raise SubmissionRejected("Submission/ must be a normal directory")

        for directory, directory_names, file_names in os.walk(
            helper_root, followlinks=False
        ):
            directory_path = Path(directory)

            for name in directory_names:
                child = directory_path / name
                if not stat.S_ISDIR(child.lstat().st_mode):
                    relative = child.relative_to(SUBMISSION_ROOT)
                    raise SubmissionRejected(
                        f"Refusing non-directory helper entry: {relative}"
                    )

            for name in file_names:
                child = directory_path / name
                relative = child.relative_to(SUBMISSION_ROOT)
                if child.suffix != ".lean":
                    raise SubmissionRejected(
                        f"Helper files must end in .lean: {relative}"
                    )
                total_bytes += regular_file_size(child, str(relative))
                helper_count += 1

                if helper_count > MAX_HELPER_FILES:
                    raise SubmissionRejected(
                        f"Too many helper files: limit is {MAX_HELPER_FILES}"
                    )
                if total_bytes > MAX_SUBMISSION_BYTES:
                    raise SubmissionRejected(
                        "Submission is too large: "
                        f"limit is {MAX_SUBMISSION_BYTES // (1024 * 1024)} MiB"
                    )

    if total_bytes > MAX_SUBMISSION_BYTES:
        raise SubmissionRejected(
            "Submission is too large: "
            f"limit is {MAX_SUBMISSION_BYTES // (1024 * 1024)} MiB"
        )

    return helper_count, total_bytes


def manifest_packages(path: Path) -> dict[str, tuple[str | None, str | None]]:
    try:
        manifest = json.loads(path.read_text())
        packages = manifest["packages"]
        return {
            package["name"]: (package.get("url"), package.get("rev"))
            for package in packages
        }
    except (OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        raise VerifierFailure(f"Invalid Lake manifest: {path}: {error}") from error


def validate_shared_packages(workspace: Path) -> None:
    shared = manifest_packages(SHARED_MANIFEST)
    required = manifest_packages(workspace / "lake-manifest.json")
    mismatches = []

    for name, expected in required.items():
        actual = shared.get(name)
        if actual != expected:
            mismatches.append(f"{name}: expected {expected!r}, shared {actual!r}")

        package = SHARED_PACKAGES / name
        if not package.is_dir():
            mismatches.append(f"{name}: package directory is missing")
            continue

        expected_url, expected_revision = expected
        if expected_url is not None:
            remote = subprocess.run(
                ["git", "-C", str(package), "remote", "get-url", "origin"],
                capture_output=True,
                text=True,
            )
            if remote.returncode != 0:
                detail = remote.stderr.strip() or "git could not read the repository"
                mismatches.append(f"{name}: cannot inspect package remote: {detail}")
            elif remote.stdout.strip() != expected_url:
                mismatches.append(
                    f"{name}: checkout URL is {remote.stdout.strip()!r}, "
                    f"expected {expected_url!r}"
                )

        if expected_revision is not None:
            revision = subprocess.run(
                ["git", "-C", str(package), "rev-parse", "HEAD"],
                capture_output=True,
                text=True,
            )
            if revision.returncode != 0:
                detail = revision.stderr.strip() or "git could not read the revision"
                mismatches.append(f"{name}: cannot inspect package revision: {detail}")
            elif revision.stdout.strip() != expected_revision:
                mismatches.append(
                    f"{name}: checkout revision is {revision.stdout.strip()!r}, "
                    f"expected {expected_revision!r}"
                )

    if mismatches:
        raise VerifierFailure(
            "Shared Lake packages do not match the trusted workspace:\n  "
            + "\n  ".join(mismatches)
        )


def locate_trusted_workspace(problem_id: str) -> Path:
    workspace = TRUSTED_WORKSPACES / problem_id
    required = (
        "Challenge.lean",
        "Solution.lean",
        "Submission.lean",
        "config.json",
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
    )
    missing = [name for name in required if not (workspace / name).is_file()]
    if missing:
        raise VerifierFailure(
            f"Trusted workspace is missing or incomplete: {problem_id} "
            f"({', '.join(missing)})"
        )
    if not SHARED_PACKAGES.is_dir():
        raise VerifierFailure(
            f"Shared Mathlib package tree is missing: {SHARED_PACKAGES}"
        )
    if not SHARED_MANIFEST.is_file():
        raise VerifierFailure(f"Shared Lake manifest is missing: {SHARED_MANIFEST}")

    proofwidgets_lock_hash = (
        SHARED_PACKAGES / "proofwidgets" / "widget" / "package-lock.json.hash"
    )
    if not proofwidgets_lock_hash.is_file():
        raise VerifierFailure(
            f"Shared ProofWidgets build metadata is missing: {proofwidgets_lock_hash}"
        )

    validate_shared_packages(workspace)
    return workspace


def assemble_clean_workspace(problem_id: str) -> Path:
    trusted = locate_trusted_workspace(problem_id)
    grading_root = Path(
        tempfile.mkdtemp(prefix=f"{problem_id}-", dir="/tmp/autoform-grade")
    )
    workspace = grading_root / "workspace"
    shutil.copytree(trusted, workspace, ignore=shutil.ignore_patterns(".lake"))

    shutil.copy2(SUBMISSION_ROOT / "Submission.lean", workspace / "Submission.lean")
    submitted_helpers = SUBMISSION_ROOT / "Submission"
    if submitted_helpers.is_dir():
        trusted_helpers = workspace / "Submission"
        if trusted_helpers.exists():
            shutil.rmtree(trusted_helpers)
        shutil.copytree(submitted_helpers, trusted_helpers)

    config_path = workspace / "config.json"
    try:
        config = json.loads(config_path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise VerifierFailure(f"Invalid trusted config: {config_path}: {error}") from error
    config["enable_nanoda"] = True
    config_path.write_text(json.dumps(config, indent=2) + "\n")

    lake_directory = workspace / ".lake"
    lake_directory.mkdir()
    (lake_directory / "packages").symlink_to(SHARED_PACKAGES)
    return workspace


def check_grading_tools() -> None:
    required = (COMPARATOR, LEAN4EXPORT, NANODA, LANDRUN)
    missing = [
        str(path)
        for path in required
        if not path.is_file() or not os.access(path, os.X_OK)
    ]
    if missing:
        raise VerifierFailure("Missing verifier tool(s):\n  " + "\n  ".join(missing))


def infrastructure_failure(output: str) -> str | None:
    lowered = output.lower()
    signatures = (
        ("permission denied", "permission failure"),
        ("read-only file system", "read-only filesystem failure"),
        ("operation not permitted", "sandbox or permission failure"),
        ("detected dubious ownership", "Git ownership validation failure"),
        ("no space left on device", "verifier storage failure"),
        ("input/output error", "verifier filesystem failure"),
        ("too many open files", "verifier resource failure"),
        ("failed to fetch", "dependency fetch failure"),
        ("failed to download", "dependency download failure"),
        ("could not resolve host", "dependency network failure"),
        ("temporary failure in name resolution", "dependency network failure"),
        ("network is unreachable", "dependency network failure"),
        ("failed to cache artifact", "Lake cache failure"),
        ("failed to restore artifact", "Lake cache failure"),
        ("failed to unpack", "Lake cache failure"),
    )
    for signature, description in signatures:
        if signature in lowered:
            line = next(
                (
                    line.strip()
                    for line in output.splitlines()
                    if signature in line.lower()
                ),
                signature,
            )
            return f"{description}: {line}"
    return None


def interpret_result(exit_code: int, output: str) -> tuple[str, str]:
    lowered = output.lower()
    if "Illegal axiom detected: 'sorryAx'" in output:
        return "rejected", "REJECTED — unsolved: a `sorry` remains"
    if "Illegal axiom detected:" in output:
        line = next(
            (line for line in output.splitlines() if "Illegal axiom detected:" in line),
            "",
        )
        return "rejected", f"REJECTED — forbidden axiom: {line.strip()}"
    if "value-pinned" in lowered:
        return "rejected", "REJECTED — a value-pinned definition was changed"
    if "statement do not match" in lowered or "statement does not match" in lowered:
        return "rejected", "REJECTED — theorem statement does not match the challenge"
    if exit_code == 0:
        return (
            "accepted",
            "ACCEPTED — proof passed Comparator and independent-kernel replay",
        )

    infrastructure_reason = infrastructure_failure(output)
    if infrastructure_reason is not None:
        raise VerifierFailure(infrastructure_reason, output)

    solution_phase = output.rfind("Building Solution")
    challenge_phase = output.rfind("Building Challenge")
    if challenge_phase >= 0 and solution_phase < challenge_phase:
        raise VerifierFailure("trusted challenge failed to build", output)

    if solution_phase >= 0:
        solution_output = output[solution_phase:]
        solution_lowered = solution_output.lower()
        if "build failed" in solution_lowered or "error:" in solution_lowered:
            return "rejected", "REJECTED — submission failed to build or type-check"

    if "nanoda kernel rejected the solution" in lowered:
        return "rejected", "REJECTED — independent kernel rejected the submission"
    if "lean default kernel rejects the solution" in lowered:
        return "rejected", "REJECTED — Lean kernel rejected the submission"

    raise VerifierFailure(
        f"Comparator failed unexpectedly with status {exit_code}", output
    )


def run_comparator(workspace: Path) -> tuple[int, str]:
    check_grading_tools()
    environment = dict(os.environ)
    environment.update(
        {
            "COMPARATOR_BIN": str(COMPARATOR),
            "COMPARATOR_LANDRUN": str(LANDRUN),
            "COMPARATOR_LEAN4EXPORT": str(LEAN4EXPORT),
            "COMPARATOR_NANODA": str(NANODA),
        }
    )

    try:
        completed = subprocess.run(
            ["lake", "env", str(COMPARATOR), "config.json"],
            cwd=workspace,
            env=environment,
            capture_output=True,
            text=True,
            timeout=COMPARATOR_TIMEOUT_SECONDS,
        )
        return completed.returncode, completed.stdout + completed.stderr
    except subprocess.TimeoutExpired as error:
        stdout = error.stdout or ""
        stderr = error.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode(errors="replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode(errors="replace")
        details = stdout + stderr
        raise VerifierFailure(
            f"Comparator timed out after {COMPARATOR_TIMEOUT_SECONDS} seconds.",
            details,
        ) from error


def write_verdict(
    problem_id: str,
    status: str,
    reason: str,
    grade_output: str,
    comparator_exit_code: int | None,
) -> None:
    OUTPUT_ROOT.mkdir(parents=True, exist_ok=True)
    reward_path = OUTPUT_ROOT / "reward.txt"
    if status == "accepted":
        reward_path.write_text("1\n")
    elif status == "rejected":
        reward_path.write_text("0\n")
    elif reward_path.exists():
        reward_path.unlink()

    grade_text = grade_output
    if grade_text and not grade_text.endswith("\n"):
        grade_text += "\n"
    grade_text += reason + "\n"
    (OUTPUT_ROOT / "grade.txt").write_text(grade_text)
    (OUTPUT_ROOT / "verdict.json").write_text(
        json.dumps(
            {
                "problem_id": problem_id,
                "status": status,
                "accepted": status == "accepted" if status != "error" else None,
                "reason": reason,
                "comparator_exit_code": comparator_exit_code,
                "verified_at": datetime.now(timezone.utc).isoformat(),
            },
            indent=2,
        )
        + "\n"
    )


def verify(problem_id: str) -> int:
    try:
        helper_count, total_bytes = validate_submission()
        print(
            f"Validated Submission.lean and {helper_count} helper file(s) "
            f"({total_bytes} bytes total)"
        )
        workspace = assemble_clean_workspace(problem_id)
        print(f"Assembled clean grading workspace: {workspace}")
        exit_code, output = run_comparator(workspace)
        status, reason = interpret_result(exit_code, output)
        write_verdict(problem_id, status, reason, output, exit_code)
        print(output, end="" if output.endswith("\n") else "\n")
        print(reason)
        return 0 if status == "accepted" else 1
    except SubmissionRejected as error:
        reason = f"REJECTED — invalid submission artifact: {error}"
        write_verdict(problem_id, "rejected", reason, "", None)
        print(reason)
        return 1
    except VerifierFailure as error:
        reason = f"VERIFIER ERROR — {error}"
        write_verdict(problem_id, "error", reason, error.grade_output, None)
        print(reason)
        return 2
    except Exception as error:
        reason = f"VERIFIER ERROR — {type(error).__name__}: {error}"
        write_verdict(problem_id, "error", reason, "", None)
        print(reason)
        return 2


def main() -> int:
    args = parse_args()
    if not PROBLEM_ID_PATTERN.fullmatch(args.problem_id):
        reason = f"VERIFIER ERROR — invalid problem ID: {args.problem_id!r}"
        write_verdict(args.problem_id, "error", reason, "", None)
        print(reason)
        return 2
    return verify(args.problem_id)


if __name__ == "__main__":
    raise SystemExit(main())

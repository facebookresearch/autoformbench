#!/usr/bin/env python3

import importlib.util
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
VERIFY_PATH = ROOT / "harbor/images/verifier/verify.py"
SPEC = importlib.util.spec_from_file_location("autoform_verify", VERIFY_PATH)
VERIFY = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(VERIFY)


class SubmissionValidationTests(unittest.TestCase):
    def test_submission_requires_regular_main_file(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Submission.lean").symlink_to("missing.lean")
            with mock.patch.object(VERIFY, "SUBMISSION_ROOT", root):
                with self.assertRaisesRegex(
                    VERIFY.SubmissionRejected, "regular file"
                ):
                    VERIFY.validate_submission()

    def test_helpers_must_be_lean_files(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Submission.lean").write_text("import Mathlib\n")
            helpers = root / "Submission"
            helpers.mkdir()
            (helpers / "notes.txt").write_text("not Lean\n")
            with mock.patch.object(VERIFY, "SUBMISSION_ROOT", root):
                with self.assertRaisesRegex(
                    VERIFY.SubmissionRejected, "must end in .lean"
                ):
                    VERIFY.validate_submission()

    def test_valid_submission_is_counted(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            main = root / "Submission.lean"
            main.write_text("import Submission.Helpers\n")
            helpers = root / "Submission"
            helpers.mkdir()
            helper = helpers / "Helpers.lean"
            helper.write_text("import Mathlib\n")
            with mock.patch.object(VERIFY, "SUBMISSION_ROOT", root):
                count, size = VERIFY.validate_submission()
            self.assertEqual(count, 1)
            self.assertEqual(size, main.stat().st_size + helper.stat().st_size)


class InterpretResultTests(unittest.TestCase):
    def test_acceptance(self) -> None:
        self.assertEqual(
            VERIFY.interpret_result(0, "Your solution is okay!"),
            (
                "accepted",
                "ACCEPTED — proof passed Comparator and independent-kernel replay",
            ),
        )

    def test_sorry_is_rejection(self) -> None:
        self.assertEqual(
            VERIFY.interpret_result(1, "Illegal axiom detected: 'sorryAx'"),
            ("rejected", "REJECTED — unsolved: a `sorry` remains"),
        )

    def test_submission_type_error_is_rejection(self) -> None:
        output = """Building Challenge
Build completed successfully
Building Solution
error: Submission.lean: unknown identifier 'bad'
error: build failed
"""
        self.assertEqual(
            VERIFY.interpret_result(1, output),
            ("rejected", "REJECTED — submission failed to build or type-check"),
        )

    def test_trusted_challenge_failure_is_infrastructure_error(self) -> None:
        output = """Building Challenge
error: Challenge.lean: unknown identifier 'brokenTrustedInput'
error: build failed
"""
        with self.assertRaisesRegex(VERIFY.VerifierFailure, "trusted challenge"):
            VERIFY.interpret_result(1, output)

    def test_permission_failure_is_infrastructure_error(self) -> None:
        output = """Building Solution
error: permission denied (error code: 13)
  file: /opt/autoformbench/packages/mathlib/Foo.olean.server.hash
error: build failed
"""
        with self.assertRaisesRegex(VERIFY.VerifierFailure, "permission failure"):
            VERIFY.interpret_result(1, output)

    def test_cache_failure_is_infrastructure_error(self) -> None:
        with self.assertRaisesRegex(VERIFY.VerifierFailure, "Lake cache failure"):
            VERIFY.interpret_result(
                1, "error: failed to restore artifact: corrupt cache"
            )

    def test_dependency_failure_is_infrastructure_error(self) -> None:
        with self.assertRaisesRegex(
            VERIFY.VerifierFailure, "dependency network failure"
        ):
            VERIFY.interpret_result(
                1, "curl: could not resolve host: example.invalid"
            )

    def test_unknown_comparator_failure_is_infrastructure_error(self) -> None:
        with self.assertRaisesRegex(VERIFY.VerifierFailure, "failed unexpectedly"):
            VERIFY.interpret_result(1, "uncaught exception: verifier tool crashed")

    def test_timeout_is_infrastructure_error_with_output(self) -> None:
        timeout = subprocess.TimeoutExpired(
            cmd=["comparator"],
            timeout=1,
            output=b"partial stdout\n",
            stderr=b"partial stderr\n",
        )
        with tempfile.TemporaryDirectory() as directory:
            with mock.patch.object(VERIFY, "check_grading_tools"), mock.patch.object(
                VERIFY.subprocess, "run", side_effect=timeout
            ):
                with self.assertRaisesRegex(
                    VERIFY.VerifierFailure, "timed out"
                ) as raised:
                    VERIFY.run_comparator(Path(directory))
        self.assertIn("partial stdout", raised.exception.grade_output)
        self.assertIn("partial stderr", raised.exception.grade_output)

    def test_error_verdict_removes_stale_reward(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output_root = Path(directory)
            reward = output_root / "reward.txt"
            reward.write_text("1\n")
            with mock.patch.object(VERIFY, "OUTPUT_ROOT", output_root):
                VERIFY.write_verdict("p", "error", "failure", "details", None)
            self.assertFalse(reward.exists())
            verdict = (output_root / "verdict.json").read_text()
            self.assertIn('"status": "error"', verdict)


class VerifyContractTests(unittest.TestCase):
    def run_with_result(self, exit_code: int, output: str) -> tuple[int, dict, bool]:
        with tempfile.TemporaryDirectory() as directory:
            output_root = Path(directory) / "logs"
            workspace = Path(directory) / "workspace"
            workspace.mkdir()
            with mock.patch.object(
                VERIFY, "OUTPUT_ROOT", output_root
            ), mock.patch.object(
                VERIFY, "validate_submission", return_value=(0, 1)
            ), mock.patch.object(
                VERIFY, "assemble_clean_workspace", return_value=workspace
            ), mock.patch.object(
                VERIFY, "run_comparator", return_value=(exit_code, output)
            ):
                status = VERIFY.verify("problem")
            verdict = json.loads((output_root / "verdict.json").read_text())
            return status, verdict, (output_root / "reward.txt").exists()

    def test_infrastructure_failures_exit_two_without_reward(self) -> None:
        failures = (
            "error: permission denied while writing Foo.olean.server.hash",
            "error: failed to restore artifact from the Lake cache",
            "curl: could not resolve host: dependency.invalid",
            "Building Challenge\nerror: trusted source failed\nerror: build failed",
            "uncaught exception: verifier tool crashed",
        )
        for output in failures:
            with self.subTest(output=output):
                status, verdict, reward_exists = self.run_with_result(1, output)
                self.assertEqual(status, 2)
                self.assertEqual(verdict["status"], "error")
                self.assertFalse(reward_exists)

    def test_invalid_submission_exits_one_with_zero_reward(self) -> None:
        output = """Building Challenge
Build completed successfully
Building Solution
error: Submission.lean: unknown identifier 'bad'
error: build failed
"""
        status, verdict, reward_exists = self.run_with_result(1, output)
        self.assertEqual(status, 1)
        self.assertEqual(verdict["status"], "rejected")
        self.assertTrue(reward_exists)

    def test_accepted_submission_exits_zero_with_one_reward(self) -> None:
        status, verdict, reward_exists = self.run_with_result(
            0, "Your solution is okay!"
        )
        self.assertEqual(status, 0)
        self.assertEqual(verdict["status"], "accepted")
        self.assertTrue(reward_exists)


if __name__ == "__main__":
    unittest.main()

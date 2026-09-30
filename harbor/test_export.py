from __future__ import annotations

import csv
import importlib.util
import json
import sys
import tempfile
import tomllib
import unittest
from pathlib import Path

EXPORT_PATH = Path(__file__).with_name("export.py")
SPEC = importlib.util.spec_from_file_location("final_benchmark_harbor_export", EXPORT_PATH)
assert SPEC is not None and SPEC.loader is not None
EXPORT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = EXPORT
SPEC.loader.exec_module(EXPORT)


class ExportTest(unittest.TestCase):
    def write_csv(
        self, path: Path, fieldnames: tuple[str, ...], rows: list[dict[str, object]]
    ) -> None:
        with path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=fieldnames, lineterminator="\n")
            writer.writeheader()
            writer.writerows(rows)

    def write_workspace(
        self,
        root: Path,
        problem_id: str,
        targets: tuple[str, ...],
        *,
        challenge_deps: bool,
    ) -> None:
        workspace = root / "workspaces" / problem_id
        (workspace / "Submission").mkdir(parents=True)
        basenames = [target.rsplit(".", 1)[-1] for target in targets]
        declarations = "\n".join(
            f"theorem {basename} : True := by sorry" for basename in basenames
        )
        files = {
            "Challenge.lean": declarations.encode(),
            "Solution.lean": ("import Submission\n" + declarations).encode(),
            "Submission.lean": declarations.encode(),
            "Submission/Helpers.lean": b"-- intentionally empty\n",
            "WorkspaceTest.lean": b"import Lean\ndef main : IO UInt32 := pure 0\n",
            "lakefile.toml": b'name = "fixture"\n',
            "lean-toolchain": b"leanprover/lean4:v4.32.2\n",
            "lake-manifest.json": (
                json.dumps(
                    {
                        "packages": [
                            {
                                "name": "mathlib",
                                "rev": "905b95818eb32af7874a58b427f50c1711a5e96c",
                            }
                        ]
                    }
                )
                + "\n"
            ).encode(),
            "config.json": (
                json.dumps(
                    {
                        "challenge_module": "Challenge",
                        "solution_module": "Solution",
                        "theorem_names": list(targets),
                        "permitted_axioms": ["propext"],
                        "enable_nanoda": False,
                    }
                )
                + "\n"
            ).encode(),
        }
        if challenge_deps:
            files["ChallengeDeps.lean"] = b"import Mathlib\n"
        for relative, contents in files.items():
            path = workspace / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(contents)

    def make_fixture(self, root: Path) -> None:
        problems = (
            ("problem_b", "book_b", ("Ns.target_b",), False),
            ("problem_a", "book_a", ("Ns.target_a1", "Ns.target_a2"), True),
        )
        self.write_csv(
            root / "MANIFEST.csv",
            EXPORT.MANIFEST_FIELDS,
            [
                {
                    "problem_id": problem,
                    "book": book,
                    "target_count": len(targets),
                    "target_declarations": ";".join(targets),
                }
                for problem, book, targets, _ in problems
            ],
        )
        self.write_csv(
            root / "SOURCES.csv",
            EXPORT.SOURCE_FIELDS,
            [
                {
                    "book": "book_b",
                    "title": "Book B",
                    "authors": "Author B",
                    "url": "https://example.test/book-b",
                },
                {
                    "book": "book_a",
                    "title": "Book A",
                    "authors": "Author A",
                    "url": "https://example.test/book-a",
                },
            ],
        )
        for problem, _, targets, challenge_deps in problems:
            self.write_workspace(
                root,
                problem,
                targets,
                challenge_deps=challenge_deps,
            )

    def test_source_free_task_preserves_exact_agent_payload(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.make_fixture(root)
            benchmark = EXPORT.load_benchmark(root)
            tasks = root / "generated"
            EXPORT.export_problem(benchmark, "problem_a", tasks)

            task = tasks / "problem_a"
            config = tomllib.loads((task / "task.toml").read_text())
            self.assertEqual("1.4", config["schema_version"])
            integrity = config["metadata"]["integrity"]
            self.assertEqual("source-free", config["metadata"]["source_condition"])
            self.assertFalse(integrity["source_included"])
            self.assertEqual(
                ["Ns.target_a1", "Ns.target_a2"],
                integrity["target_declarations"],
            )
            self.assertEqual(
                benchmark.problems["problem_a"].agent_payload_sha256,
                integrity["agent_payload_sha256"],
            )
            agent = task / "environment/workspace"
            self.assertFalse((agent / "book").exists())
            for hidden in ("WorkspaceTest.lean", "config.json"):
                self.assertFalse((agent / hidden).exists())
            for relative in benchmark.problems["problem_a"].agent_files:
                self.assertEqual(
                    (root / "workspaces/problem_a" / relative).read_bytes(),
                    (agent / relative).read_bytes(),
                )
            self.assertIn(
                "source-free benchmark condition",
                (task / "instruction.md").read_text(),
            )
            EXPORT.check_export(benchmark, tasks, "problem_a")

    def test_full_export_is_deterministic_and_manifest_order_independent(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.make_fixture(root)
            benchmark = EXPORT.load_benchmark(root)
            first = root / "first"
            second = root / "second"
            EXPORT.export_all(benchmark, first)
            EXPORT.export_all(benchmark, second)
            self.assertEqual(EXPORT.file_manifest(first), EXPORT.file_manifest(second))
            self.assertEqual(
                ["problem_a", "problem_b"],
                sorted(path.name for path in first.iterdir() if path.is_dir()),
            )
            EXPORT.check_export(benchmark, first)

    def test_check_detects_copied_workspace_drift(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.make_fixture(root)
            benchmark = EXPORT.load_benchmark(root)
            tasks = root / "generated"
            EXPORT.export_all(benchmark, tasks)
            challenge = tasks / "problem_b/environment/workspace/Challenge.lean"
            challenge.write_text(challenge.read_text() + "\n-- drift\n")
            with self.assertRaisesRegex(EXPORT.ExportError, "copied agent file changed"):
                EXPORT.check_export(benchmark, tasks, "problem_b")

    def test_manifest_config_holes_target_parity_is_required(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.make_fixture(root)
            config_path = root / "workspaces/problem_a/config.json"
            config = json.loads(config_path.read_text())
            config["theorem_names"] = ["Ns.different"]
            config_path.write_text(json.dumps(config) + "\n")
            with self.assertRaisesRegex(EXPORT.ExportError, "do not exactly match"):
                EXPORT.load_benchmark(root)


if __name__ == "__main__":
    unittest.main()

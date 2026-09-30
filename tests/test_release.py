from __future__ import annotations

import csv
import hashlib
import importlib.util
import json
import re
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_COUNT = 241
PUBLIC_IDS_SHA256 = "61b64638b868c1f439011e2f18fd53ea6ea73aa25b8a1d4beda03c0597425ffd"


def read_ids() -> list[str]:
    return [line for line in (ROOT / "problem_ids.txt").read_text().splitlines() if line]


class ReleaseIntegrityTest(unittest.TestCase):
    def test_public_cohort_parity(self) -> None:
        ids = read_ids()
        self.assertEqual(EXPECTED_COUNT, len(ids))
        self.assertEqual(len(ids), len(set(ids)))
        self.assertEqual(
            PUBLIC_IDS_SHA256,
            hashlib.sha256((ROOT / "problem_ids.txt").read_bytes()).hexdigest(),
        )

        with (ROOT / "MANIFEST.csv").open(newline="", encoding="utf-8") as handle:
            manifest_ids = [row["problem_id"] for row in csv.DictReader(handle)]
        self.assertEqual(ids, manifest_ids)

        workspace_ids = sorted(path.name for path in (ROOT / "workspaces").iterdir())
        self.assertEqual(sorted(ids), workspace_ids)

        for path in sorted((ROOT / "leaderboard_data").glob("*.csv")):
            with path.open(newline="", encoding="utf-8") as handle:
                result_ids = [row["problem_id"] for row in csv.DictReader(handle)]
            self.assertEqual(ids, result_ids, path.name)

    def test_audit_summary_is_aggregate_only(self) -> None:
        summary = json.loads(
            (ROOT / "audit/public_private_split_summary.json").read_text()
        )
        cohort = summary["cohort"]
        self.assertEqual(341, cohort["full"])
        self.assertEqual(241, cohort["public"])
        self.assertEqual(100, cohort["private"])
        self.assertEqual(PUBLIC_IDS_SHA256, cohort["public_ids_sha256"])
        self.assertNotIn("forced_private", summary)
        self.assertEqual(6, summary["forced_private_count"])
        self.assertRegex(summary["forced_private_ids_sha256"], r"^[0-9a-f]{64}$")
        text = json.dumps(summary)
        self.assertFalse(any(problem_id in text for problem_id in read_ids()))

    def test_no_disallowed_release_material(self) -> None:
        forbidden_suffixes = {".pdf", ".zip", ".tar", ".tgz"}
        forbidden_names = {".env", "Llama_keys.txt"}
        for path in ROOT.rglob("*"):
            if ".git" in path.parts or path.is_dir():
                continue
            self.assertNotIn(path.name, forbidden_names, str(path))
            self.assertNotIn(path.suffix.lower(), forbidden_suffixes, str(path))
            self.assertFalse(path.is_symlink(), str(path))

    def test_checksum_manifest_covers_release_files(self) -> None:
        covered = set()
        for line in (ROOT / "SHA256SUMS").read_text().splitlines():
            digest, relative = line.split("  ", maxsplit=1)
            self.assertRegex(digest, r"^[0-9a-f]{64}$")
            self.assertFalse(Path(relative).is_absolute())
            self.assertNotIn("..", Path(relative).parts)
            covered.add(relative.removeprefix("./"))

        actual = set()
        for path in ROOT.rglob("*"):
            if path.is_dir() or ".git" in path.parts or "__pycache__" in path.parts:
                continue
            relative = path.relative_to(ROOT)
            if relative == Path("SHA256SUMS") or relative.parts[:2] == (
                "harbor",
                "tasks",
            ):
                continue
            actual.add(relative.as_posix())
        self.assertEqual(actual, covered)

    def test_no_internal_markers_or_host_paths(self) -> None:
        forbidden = (
            b"fair" + b"internal",
            b"fwd" + b"proxy",
            b"@" + b"meta.com",
            b"@" + b"fb.com",
            b"/data/" + b"users/",
            b"sl" + b"urm",
            b"py" + b"xis",
            b"fair" + b"sc",
        )
        host_home = re.compile(
            rb"/home/(?!agent(?:/|\b)|verifier(?:/|\b)|root(?:/|\b))[^/\s]+",
            re.IGNORECASE,
        )
        for path in ROOT.rglob("*"):
            if (
                ".git" in path.parts
                or path.is_dir()
                or path == ROOT / "SHA256SUMS"
                or path == Path(__file__)
            ):
                continue
            data = path.read_bytes()
            lowered = data.lower()
            for marker in forbidden:
                self.assertNotIn(marker.lower(), lowered, str(path))
            self.assertIsNone(host_home.search(data), str(path))

    def test_readme_leaderboard_is_generated_from_public_rows(self) -> None:
        spec = importlib.util.spec_from_file_location(
            "render_leaderboard", ROOT / "scripts/render_leaderboard.py"
        )
        assert spec and spec.loader
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        readme = (ROOT / "README.md").read_text()
        match = re.search(
            r"<!-- leaderboard:start -->\n(.*?)\n<!-- leaderboard:end -->",
            readme,
            re.DOTALL,
        )
        self.assertIsNotNone(match)
        self.assertEqual(module.render(), match.group(1))


if __name__ == "__main__":
    unittest.main()

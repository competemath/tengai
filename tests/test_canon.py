"""tengai-canon on its fixtures, and the equality of its rules with conventions.toml. Run after `lake build tengai-canon TengaiFixtures` (CI does)."""

import subprocess
import sys
import tomllib
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def canon(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["lake", "exe", "tengai-canon", *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )


def violations(out: str) -> set[tuple[str, str]]:
    rows = [ln.split("\t") for ln in out.splitlines() if ln.startswith("violation\t")]
    return {(r[1], r[2]) for r in rows}


class Canon(unittest.TestCase):
    def test_the_rules_are_the_conventions(self):
        toml = tomllib.loads((ROOT / "conventions.toml").read_text(encoding="utf-8"))
        ids = [r["id"] for r in toml["rule"]]
        self.assertEqual(len(ids), len(set(ids)), "a rule is listed twice")
        r = canon("--list-rules")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(
            set(r.stdout.split()),
            set(ids),
            "TengaiCanon.rules and conventions.toml must list the same ids",
        )
        for rule in toml["rule"]:
            self.assertEqual(
                set(rule), {"id", "summary", "rationale", "tiebreak"}, rule["id"]
            )
            self.assertIn(
                rule["tiebreak"],
                {"intuitive", "scales", "least-hidden-search"},
                rule["id"],
            )

    def test_each_bad_fixture_breaks_exactly_its_rule_and_no_good_one_breaks_any(self):
        r = canon("--module", "TengaiFixtures")
        self.assertEqual(r.returncode, 1, r.stderr)
        self.assertEqual(
            violations(r.stdout),
            {
                ("gt-ge", "Fixtures.bad_gt"),
                ("gt-ge", "Fixtures.bad_ge"),
                ("not-eq", "Fixtures.bad_not_eq"),
                ("nat-succ", "Fixtures.bad_succ"),
                ("name-theorem", "Fixtures.BadName"),
                ("name-type", "Fixtures.bad_type"),
            },
        )

    def test_the_library_itself_is_canonical(self):
        r = canon("--module", "Tengai")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_no_module_is_a_usage_error(self):
        self.assertEqual(canon().returncode, 2)


if __name__ == "__main__":
    unittest.main()

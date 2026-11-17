"""tengai-normalise: the three syntactic rules of conventions.toml applied to a file. Run after `lake build tengai-normalise tengai-canon` (CI does).

The claims, each a test: the output is the stored expected file (golden); a second pass changes nothing (idempotence, invariant I2); `--check` agrees with that; every normalised
theorem has a type DEFINITIONALLY EQUAL to the original's (the rewrite keeps the meaning, proved by Lean's `isDefEq` on the two compiled modules); and `tengai-canon` finds in the
normalised corpus nothing but the one documented skip (a node with a comment inside is not rewritten).
"""

import os
import re
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "tests" / "normalise" / "corpus.lean"
EXPECTED = ROOT / "tests" / "normalise" / "corpus.expected.lean"


def lake(*args: str, env: dict | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["lake", *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
        env=env,
    )


def normalise(path: Path, *flags: str) -> subprocess.CompletedProcess:
    return lake("exe", "tengai-normalise", str(path), *flags)


class Normalise(unittest.TestCase):
    def test_the_output_is_the_expected_file(self):
        r = normalise(CORPUS)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(r.stdout, EXPECTED.read_text(encoding="utf-8"))

    def test_a_second_pass_changes_nothing(self):
        r = normalise(EXPECTED)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(r.stdout, EXPECTED.read_text(encoding="utf-8"))

    def test_check_mode(self):
        self.assertEqual(normalise(CORPUS, "--check").returncode, 1)
        self.assertEqual(normalise(EXPECTED, "--check").returncode, 0)

    def test_write_mode_rewrites_in_place(self):
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "C.lean"
            f.write_bytes(CORPUS.read_bytes())
            self.assertEqual(normalise(f, "--write").returncode, 0)
            self.assertEqual(
                f.read_text(encoding="utf-8"), EXPECTED.read_text(encoding="utf-8")
            )

    def test_the_comment_is_not_lost_and_the_skip_is_reported(self):
        r = normalise(CORPUS)
        self.assertIn("-- the larger one", r.stdout)
        self.assertIn("skipped\tcomment-inside", r.stderr)

    def test_meaning_is_preserved_and_only_the_documented_skip_remains(self):
        original = CORPUS.read_text(encoding="utf-8")
        names = re.findall(r"^theorem (\w+)", original, flags=re.M)
        self.assertGreater(len(names), 10)
        lp = lake("env", "printenv", "LEAN_PATH").stdout.strip()
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            for mod, src in (
                ("COrig", original),
                ("CNorm", EXPECTED.read_text(encoding="utf-8")),
            ):
                (tmp / f"{mod}.lean").write_text(
                    src.replace("Corpus", mod), encoding="utf-8"
                )
            env = dict(os.environ, LEAN_PATH=f"{tmp}:{lp}")
            for mod in ("COrig", "CNorm"):
                r = lake(
                    "env",
                    "lean",
                    f"--root={tmp}",
                    str(tmp / f"{mod}.lean"),
                    "-o",
                    str(tmp / f"{mod}.olean"),
                    env=env,
                )
                self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            lst = ", ".join(f"`{n}" for n in names)
            (tmp / "Check.lean").write_text(
                "import Lean\nimport COrig\nimport CNorm\nopen Lean Meta\n"
                "#eval show MetaM Unit from do\n"
                f"  for n in [{lst}] do\n"
                "    let a ← getConstInfo (`COrig ++ n)\n"
                "    let b ← getConstInfo (`CNorm ++ n)\n"
                '    unless (← isDefEq a.type b.type) do throwError "{n}: the type changed"\n'
                '  IO.println "meaning-preserved"\n',
                encoding="utf-8",
            )
            r = lake("env", "lean", f"--root={tmp}", str(tmp / "Check.lean"), env=env)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("meaning-preserved", r.stdout)
            c = lake("exe", "tengai-canon", "--module", "CNorm", env=env)
            rows = {
                tuple(ln.split("\t")[1:3])
                for ln in c.stdout.splitlines()
                if ln.startswith("violation\t")
            }
            self.assertEqual(rows, {("gt-ge", "CNorm.comment_inside")}, c.stdout)


if __name__ == "__main__":
    unittest.main()

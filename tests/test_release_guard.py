"""The release barrier (tools/release_guard.py): nothing above `max_major`, whatever way it is written. Fixtures are throw-away git repositories."""

import json
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GUARD = ROOT / "tools" / "release_guard.py"
GIT_ENV = {
    "GIT_AUTHOR_NAME": "t",
    "GIT_AUTHOR_EMAIL": "t@example.invalid",
    "GIT_COMMITTER_NAME": "t",
    "GIT_COMMITTER_EMAIL": "t@example.invalid",
    "PATH": "/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin",
}


def run(root: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["python3", str(GUARD), "--root", str(root), *args],
        capture_output=True,
        text=True,
        check=False,
    )


def git(root: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=root, check=True, capture_output=True, env=GIT_ENV)


class Fixture(unittest.TestCase):
    def setUp(self):
        self._d = tempfile.TemporaryDirectory()
        self.addCleanup(self._d.cleanup)
        self.root = Path(self._d.name)
        git(self.root, "init", "-q")
        self.write("release-guard.toml", "max_major = 0\n")
        self.write("lakefile.toml", 'name = "X"\nversion = "0.3.1"\n')
        git(self.root, "add", "-A")
        git(self.root, "commit", "-q", "-m", "init")

    def write(self, rel: str, text: str) -> None:
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text, encoding="utf-8")


class Guard(Fixture):
    def test_a_zero_version_passes(self):
        r = run(self.root)
        self.assertEqual(r.returncode, 0, r.stderr)

    def test_a_declared_version_of_one_fails_in_every_lakefile(self):
        for rel in ("lakefile.toml", "core/lakefile.toml"):
            self.write(rel, 'name = "X"\nversion = "1.0.0"\n')
            r = run(self.root)
            self.assertEqual(r.returncode, 1, rel)
            self.assertIn("major 1 > 0", r.stderr)
            self.write(rel, 'name = "X"\nversion = "0.9.9"\n')
            self.assertEqual(run(self.root).returncode, 0)

    def test_an_unreadable_version_fails_closed(self):
        self.write("lakefile.toml", 'name = "X"\nversion = "banana"\n')
        self.assertEqual(run(self.root).returncode, 1)

    def test_a_lean_lakefile_version_is_read(self):
        (self.root / "lakefile.toml").unlink()
        self.write("lakefile.lean", 'package x where\n  version := v!"2.0.0"\n')
        self.assertEqual(run(self.root).returncode, 1)

    def test_a_version_tag_above_the_cap_fails_whatever_its_spelling(self):
        for tag in ("v1", "v1.0.0", "V2.3", "1.0", "v10.0.0-rc1"):
            git(self.root, "tag", tag)
            r = run(self.root)
            self.assertEqual(r.returncode, 1, tag)
            git(self.root, "tag", "-d", tag)
        for tag in ("v0.0.7", "v0.99.0", "cache-latest", "latest"):
            git(self.root, "tag", tag)
        self.assertEqual(run(self.root).returncode, 0)

    def test_the_core_lock_may_not_pin_a_version_above_the_cap(self):
        self.write("core.lock", json.dumps({"tag": "v0.0.6", "tree": "x"}))
        self.assertEqual(run(self.root).returncode, 0)
        self.write("core.lock", json.dumps({"tag": "v1.0.0", "tree": "x"}))
        self.assertEqual(run(self.root).returncode, 1)
        self.write("core.lock", json.dumps({"tag": "latest", "tree": "x"}))
        self.assertEqual(run(self.root).returncode, 1, "a lock that is not a version is not trusted")

    def test_the_cap_is_a_non_negative_integer(self):
        for bad in ("max_major = -1", 'max_major = "0"', "max_major = true", "x = 1"):
            self.write("release-guard.toml", bad + "\n")
            self.assertNotEqual(run(self.root).returncode, 0, bad)

    def test_no_config_means_no_release(self):
        (self.root / "release-guard.toml").unlink()
        self.assertNotEqual(run(self.root).returncode, 0)

    def test_raising_the_cap_lets_the_version_through(self):
        self.write("lakefile.toml", 'name = "X"\nversion = "1.0.0"\n')
        self.write("release-guard.toml", "max_major = 1\n")
        self.assertEqual(run(self.root).returncode, 0)


class TagMode(Fixture):
    def test_tags(self):
        self.assertEqual(run(self.root, "--tag", "v0.0.7").returncode, 0)
        self.assertEqual(run(self.root, "--tag", "cache-latest").returncode, 0)
        for t in ("v1.0.0", "1.0", "V3", "v1"):
            self.assertEqual(run(self.root, "--tag", t).returncode, 1, t)


class ChangedMode(Fixture):
    def test_the_guard_files_are_watched(self):
        self.write("tools/release_guard.py", "# x\n")
        self.write(".github/workflows/release-guard.yml", "# x\n")
        self.write("tests/test_release_guard.py", "# x\n")
        git(self.root, "add", "-A")
        git(self.root, "commit", "-q", "-m", "guard files")
        base = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=self.root, capture_output=True, text=True, check=True
        ).stdout.strip()
        self.assertEqual(run(self.root, "--changed", base).returncode, 0)
        self.write("README.md", "unrelated\n")
        self.assertEqual(run(self.root, "--changed", base).returncode, 0)
        for rel in ("release-guard.toml", "tools/release_guard.py", ".github/workflows/release-guard.yml", "tests/test_release_guard.py"):
            self.write(rel, (self.root / rel).read_text(encoding="utf-8") + "\n# changed\n")
            self.assertEqual(run(self.root, "--changed", base).returncode, 3, rel)
            git(self.root, "checkout", "--", rel)


class WatchList(Fixture):
    def test_the_list_comes_from_base_and_a_pull_request_cannot_shrink_it(self):
        self.write("release-guard.toml", 'max_major = 0\nguard_files = ["extra/watched.txt"]\n')
        self.write("extra/watched.txt", "a\n")
        self.write("tools/release_guard.py", "# x\n")
        git(self.root, "add", "-A")
        git(self.root, "commit", "-q", "-m", "watch list")
        base = subprocess.run(["git", "rev-parse", "HEAD"], cwd=self.root, capture_output=True, text=True, check=True).stdout.strip()
        self.write("tools/release_guard.py", "# changed but not on base's list\n")
        self.assertEqual(run(self.root, "--changed", base).returncode, 0)
        self.write("extra/watched.txt", "b\n")
        self.assertEqual(run(self.root, "--changed", base).returncode, 3)
        git(self.root, "checkout", "--", "extra/watched.txt")
        # the pull request empties the list in its own copy of the config: the config itself is always watched
        self.write("release-guard.toml", "max_major = 0\n")
        self.assertEqual(run(self.root, "--changed", base).returncode, 3)


class ThisRepository(unittest.TestCase):
    def test_this_repository_passes_its_own_guard(self):
        r = run(ROOT)
        self.assertEqual(r.returncode, 0, r.stderr)

    def test_the_cap_here_is_zero(self):
        self.assertIn("max_major = 0", (ROOT / "release-guard.toml").read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main()

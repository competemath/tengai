#!/usr/bin/env python3
"""release_guard.py - no v1 (or later) of any library of this repository before the owner's explicit approval.

  release_guard.py [--root DIR]              the tree holds no version, tag or lock at a major above `max_major` (release-guard.toml)
  release_guard.py --tag TAG [--root DIR]    TAG may exist: a version tag whose major is above `max_major` may not
  release_guard.py --changed BASE [--root DIR]   exit 3 if the guard itself differs from git ref BASE: the files `guard_files` of BASE's release-guard.toml name
                                             (default: the config, this script, its workflow, its test). The workflow runs BASE's copy of this script, never the pull request's.

What it reads, and nothing else: `version = "x.y.z"` in every `lakefile.toml` (and `version := v!"x.y.z"` in a `lakefile.lean`), every git tag that looks like a version (`v1`, `1.0`, `V2.3.4`), and the
`tag` of `core.lock` if there is one. A version at or below `max_major` is fine; one above it is a violation and the exit status is 1.

The guard is a tripwire in the repository, not a lock: anyone who can push a tag can push one past a workflow that is not required. The lock is a tag ruleset only the owner can create
(tools/release-ruleset.json, and the command in docs/release-barrier.md). Changing `release-guard.toml` or this script needs an approving review from someone other than the author
(.github/workflows/release-guard.yml), so that raising `max_major` is a visible, explicit act.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tomllib
from pathlib import Path

VERSION = re.compile(r"^[vV]?(\d+)(?:[.\-+_].*)?$")
LAKE_LEAN_VERSION = re.compile(r'version\s*:=\s*v!"(\d+)')
GUARD_FILES = (
    "release-guard.toml",
    "tools/release_guard.py",
    ".github/workflows/release-guard.yml",
    "tests/test_release_guard.py",
)
SKIP_DIRS = {".git", ".lake", ".tengoku", "node_modules"}


def major(text: str) -> int | None:
    """the major of a version-looking string, None if it does not look like one"""
    m = VERSION.match(text.strip())
    return int(m.group(1)) if m else None


def max_major(root: Path) -> int:
    cfg = root / "release-guard.toml"
    if not cfg.is_file():
        raise SystemExit(f"release-guard: {cfg} is missing: no guard, no release")
    value = tomllib.loads(cfg.read_text(encoding="utf-8")).get("max_major")
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise SystemExit("release-guard: max_major must be a non-negative integer")
    return value


def lakefiles(root: Path):
    for p in sorted(root.rglob("lakefile.*")):
        if p.suffix in (".toml", ".lean") and not (set(p.relative_to(root).parts) & SKIP_DIRS):
            yield p


def declared_versions(root: Path) -> list[tuple[str, int]]:
    """(where, major) of every version a lakefile declares"""
    out: list[tuple[str, int]] = []
    for p in lakefiles(root):
        rel = str(p.relative_to(root))
        text = p.read_text(encoding="utf-8")
        if p.suffix == ".toml":
            v = tomllib.loads(text).get("version")
            if v is not None:
                m = major(str(v))
                out.append((rel, m if m is not None else 10**9))  # an unreadable version is as bad as a big one
        else:
            for m in LAKE_LEAN_VERSION.finditer(text):
                out.append((rel, int(m.group(1))))
    return out


def tags(root: Path) -> list[str]:
    r = subprocess.run(["git", "tag", "--list"], cwd=root, capture_output=True, text=True, check=False)
    return r.stdout.split() if r.returncode == 0 else []


def lock_tag(root: Path) -> str | None:
    p = root / "core.lock"
    return json.loads(p.read_text(encoding="utf-8")).get("tag") if p.is_file() else None


def violations(root: Path) -> list[str]:
    cap = max_major(root)
    out = [f"{where}: declares version major {m} > {cap}" for where, m in declared_versions(root) if m > cap]
    for t in tags(root):
        m = major(t)
        if m is not None and m > cap:
            out.append(f"tag {t}: major {m} > {cap}")
    lt = lock_tag(root)
    if lt is not None:
        m = major(lt)
        if m is None or m > cap:
            out.append(f"core.lock: tag {lt} is not a version at or below major {cap}")
    return out


def tag_violation(root: Path, tag: str) -> str | None:
    cap = max_major(root)
    m = major(tag)
    return f"tag {tag}: major {m} > {cap}" if m is not None and m > cap else None


def watched(root: Path, base: str) -> tuple[str, ...]:
    """the files that make up the guard, as BASE says (a pull request cannot shrink the list it is judged by): `guard_files` of BASE's release-guard.toml, else the default"""
    r = subprocess.run(["git", "show", f"{base}:release-guard.toml"], cwd=root, capture_output=True, text=True, check=False)
    files = tomllib.loads(r.stdout).get("guard_files") if r.returncode == 0 else None
    return tuple(["release-guard.toml", *files]) if isinstance(files, list) and files else GUARD_FILES


def guard_changed(root: Path, base: str) -> bool:
    r = subprocess.run(["git", "diff", "--quiet", base, "--", *watched(root, base)], cwd=root, check=False)
    return r.returncode != 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=".")
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--tag")
    g.add_argument("--changed", metavar="BASE")
    a = ap.parse_args(argv)
    root = Path(a.root).resolve()
    if a.tag is not None:
        v = tag_violation(root, a.tag)
        if v:
            print(f"release-guard: {v}: no v1 before the owner's explicit approval", file=sys.stderr)
            return 1
        return 0
    if a.changed is not None:
        return 3 if guard_changed(root, a.changed) else 0
    bad = violations(root)
    for v in bad:
        print(f"release-guard: {v}", file=sys.stderr)
    if bad:
        print("release-guard: no v1 before the owner's explicit approval (docs/release-barrier.md)", file=sys.stderr)
        return 1
    print(f"release-guard: ok (max_major {max_major(root)})")
    return 0


if __name__ == "__main__":
    sys.exit(main())

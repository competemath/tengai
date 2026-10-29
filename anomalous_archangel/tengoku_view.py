"""What has arrived in Tengoku lately, read from a checkout of it (`.tengoku`, the pinned commit): the commits, the paths they touch, and
which of them look like the work of leak-archangel (translations, staging records, memory intake). Read only, as data."""

from __future__ import annotations

import re
import subprocess
from pathlib import Path

LEAK_HINT = re.compile(r"leak|archangel|emissary|studied|memory.?intake|staging|banked|translat", re.I)
SEP = "\x1e"


def git(repo: Path, *args: str) -> str:
    r = subprocess.run(["git", "-C", str(repo), *args], capture_output=True, text=True, timeout=120, check=False)
    if r.returncode != 0:
        raise RuntimeError(r.stderr.strip()[:300])
    return r.stdout


def arrivals(repo: Path, since_days: int = 14, limit: int = 40) -> list[dict]:
    """Commits of the last `since_days` days (newest first), each with the first paths it touched and a flag for the ones that look like Leak's."""
    if not (repo / ".git").exists():
        return []
    try:
        out = git(repo, "log", f"--since={since_days}.days.ago", f"-n{limit}", f"--format={SEP}%H%x00%cI%x00%an%x00%s", "--name-only")
    except RuntimeError:
        return []
    rows = []
    for chunk in out.split(SEP):
        if not chunk.strip():
            continue
        head, _, files = chunk.partition("\n")
        parts = head.split("\x00")
        if len(parts) < 4:
            continue
        paths = [f for f in files.splitlines() if f.strip()]
        rows.append(
            {
                "sha": parts[0],
                "date": parts[1],
                "author": parts[2],
                "subject": parts[3][:200],
                "paths": paths[:8],
                "touches": len(paths),
                "leak": bool(
                    LEAK_HINT.search(parts[3]) or any(p.startswith("data/staging/") or p.startswith("data/trusted/") for p in paths)
                ),
            }
        )
    return rows


def digest(rows: list[dict], max_chars: int = 8000) -> str:
    if not rows:
        return "TENGOKU ARRIVALS — none read (no checkout, or nothing in the window)."
    lines = ["TENGOKU ARRIVALS (newest first; [leak] marks work that looks like leak-archangel's)"]
    for r in rows:
        lines.append(
            f"- {r['date'][:10]} {'[leak] ' if r['leak'] else ''}{r['subject']}  ({r['touches']} paths: {', '.join(r['paths'][:3])})"
        )
    text = "\n".join(lines)
    return text if len(text) <= max_chars else text[:max_chars] + "\n…[cut]"

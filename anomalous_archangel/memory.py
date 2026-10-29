"""What earlier drips found, so a drip does not say it again: findings, which lenses ran when, and open threads."""

from __future__ import annotations

import json
import re
from pathlib import Path

WORD = re.compile(r"[a-z][a-z0-9_]{3,}")
REPEAT_AT = 0.55


def tokens(text: str) -> set[str]:
    return set(WORD.findall(text.lower()))


def jaccard(a: set[str], b: set[str]) -> float:
    return len(a & b) / len(a | b) if a and b else 0.0


class Memory:
    def __init__(self, data: dict | None = None) -> None:
        d = data or {}
        self.findings: list[dict] = d.get("findings", [])
        self.lens_runs: dict[str, dict] = d.get("lens_runs", {})
        self.threads: list[dict] = d.get("threads", [])

    @classmethod
    def load(cls, path: Path) -> Memory:
        try:
            return cls(json.loads(path.read_text(encoding="utf-8")))
        except (OSError, ValueError):
            return cls()

    def save(self, path: Path) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            json.dumps(
                {"version": 1, "findings": self.findings[-600:], "lens_runs": self.lens_runs, "threads": self.threads[-60:]}, indent=1
            )
            + "\n"
        )

    def similarity(self, title: str, body: str) -> float:
        t = tokens(title + " " + body)
        return max((jaccard(t, set(f["tokens"])) for f in self.findings), default=0.0)

    def is_repeat(self, title: str, body: str) -> bool:
        return self.similarity(title, body) >= REPEAT_AT

    def remember(self, drip: str, lens: str, f: dict) -> None:
        self.findings.append(
            {
                "drip": drip,
                "lens": lens,
                "kind": f["kind"],
                "title": f["title"],
                "tokens": sorted(tokens(f["title"] + " " + f["body"]))[:60],
            }
        )

    def ran(self, drip: str, lens: str) -> None:
        r = self.lens_runs.setdefault(lens, {"count": 0, "last": ""})
        r["count"] += 1
        r["last"] = drip

    def staleness(self, lens: str) -> int:
        """How many runs of other lenses since this one ran (never ran: large)."""
        r = self.lens_runs.get(lens)
        if not r:
            return 10_000
        return sum(v["count"] for k, v in self.lens_runs.items() if k != lens and v["last"] > r["last"])

    def digest(self, n: int = 40) -> str:
        if not self.findings:
            return "MEMORY OF EARLIER DRIPS — none: this is the first."
        lines = ["MEMORY OF EARLIER DRIPS (do not say these again; build on them or contradict them)"]
        lines += [f"- [{f['drip']}] {f['lens']}/{f['kind']}: {f['title']}" for f in self.findings[-n:]]
        if self.threads:
            lines.append("OPEN THREADS")
            lines += [f"- {t['title']} (from {t['drip']})" for t in self.threads[-10:]]
        return "\n".join(lines)

"""The queue of statements anomalous-archangel wants proved, for leak-archangel (or anyone) to take.

unchecked -> open -> claimed -> proved (a file under Tengai/ that passed the gate), or abandoned. A statement is a Lean proposition; the request holds it as
text and records that the gate saw it elaborate (with `sorry` as its only warning) before it was queued.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

STATUSES = ("unchecked", "open", "claimed", "proved", "abandoned")


def request_id(statement: str) -> str:
    return hashlib.sha256(re.sub(r"\s+", " ", statement.strip()).encode()).hexdigest()[:12]


class Queue:
    def __init__(self, items: list[dict] | None = None) -> None:
        self.items = items or []

    @classmethod
    def load(cls, path: Path) -> Queue:
        try:
            d = json.loads(path.read_text(encoding="utf-8"))
            return cls(d["requests"] if isinstance(d, dict) else [])
        except (OSError, ValueError, KeyError):
            return cls()

    def save(self, path: Path) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({"version": 1, "requests": self.items}, indent=1, ensure_ascii=False) + "\n")

    def get(self, rid: str) -> dict | None:
        return next((i for i in self.items if i["id"] == rid), None)

    def add(self, statement: str, informal: str, why: str, drip: str, lens: str, now: str, checked: bool = True) -> tuple[dict, bool]:
        rid = request_id(statement)
        if (old := self.get(rid)) is not None:
            return old, False
        item = {
            "id": rid,
            "statement": statement.strip(),
            "informal": informal,
            "why": why,
            "drip": drip,
            "lens": lens,
            "status": "open" if checked else "unchecked",
            "created": now,
            "claimed_by": "",
            "proof_path": "",
        }
        self.items.append(item)
        return item, True

    def claim(self, rid: str, who: str) -> dict:
        item = self._need(rid)
        if item["status"] != "open":
            raise ValueError(f"{rid} is {item['status']}, not open")
        item["status"], item["claimed_by"] = "claimed", who
        return item

    def fulfil(self, rid: str, proof_path: str) -> dict:
        item = self._need(rid)
        if item["status"] not in ("open", "claimed"):
            raise ValueError(f"{rid} is {item['status']}")
        item["status"], item["proof_path"] = "proved", proof_path
        return item

    def abandon(self, rid: str, reason: str) -> dict:
        item = self._need(rid)
        item["status"], item["why_abandoned"] = "abandoned", reason[:300]
        return item

    def open_items(self) -> list[dict]:
        return [i for i in self.items if i["status"] == "open"]

    def _need(self, rid: str) -> dict:
        item = self.get(rid)
        if item is None:
            raise KeyError(f"no request {rid}")
        return item

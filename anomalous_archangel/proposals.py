"""The one thing an angel hands back: a closed JSON object, parsed and bounded here, never trusted.

An angel's final message ends with a single ```json block. Unknown keys are refused, every text is capped, a path must be under Tengai/, and
the label of a claim is one of three words: `note` (a plain statement about what is there), `observation` (something seen in a small case or
a computation) or `conjecture` (believed, not proved). The word `verified` is not available to an angel: only a Lean file that passed the
gate is verified, and the archangel says so, not the angel.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field

KINDS = ("note", "conjecture", "observation", "picture", "impact", "abstraction", "bridge")
LABELS = ("note", "observation", "conjecture")
KEYS = {"findings", "lean_files", "requests", "delegate", "verdicts", "summary"}
PATH = re.compile(r"^Tengai/[A-Za-z0-9_]+(/[A-Za-z0-9_]+)*\.lean$")
FENCE = re.compile(r"```json\s*\n(.*?)\n```", re.S)
CAPS = {
    "title": 120,
    "body": 4000,
    "purpose": 300,
    "content": 60_000,
    "statement": 2000,
    "informal": 600,
    "why": 400,
    "brief": 800,
    "reason": 400,
}
# More delegates than the breadth limit are accepted here on purpose: the spawn ledger is the authority and records each refusal.
MAX_ITEMS = {"findings": 8, "lean_files": 3, "requests": 4, "delegate": 8, "verdicts": 24}


class BadProposal(Exception):
    pass


@dataclass
class Proposal:
    findings: list[dict] = field(default_factory=list)
    lean_files: list[dict] = field(default_factory=list)
    requests: list[dict] = field(default_factory=list)
    delegate: list[dict] = field(default_factory=list)
    verdicts: list[dict] = field(default_factory=list)
    summary: str = ""


def _text(d: dict, key: str, required: bool = True) -> str:
    v = d.get(key, "")
    if not isinstance(v, str):
        raise BadProposal(f"{key} must be a string")
    if required and not v.strip():
        raise BadProposal(f"{key} is empty")
    if len(v) > CAPS[key]:
        raise BadProposal(f"{key} is {len(v)} characters, the limit is {CAPS[key]}")
    return v


def _only(d: object, keys: set[str], what: str) -> dict:
    if not isinstance(d, dict):
        raise BadProposal(f"each {what} must be an object")
    extra = set(d) - keys
    if extra:
        raise BadProposal(f"{what}: unknown keys {sorted(extra)}")
    return d


def parse(text: str, allow_delegate: bool = True) -> Proposal:
    blocks = FENCE.findall(text or "")
    if not blocks:
        raise BadProposal("no ```json block in the answer")
    try:
        data = json.loads(blocks[-1])
    except ValueError as e:
        raise BadProposal(f"the json block does not parse: {e}") from e
    data = _only(data, KEYS, "answer")
    for k, cap in MAX_ITEMS.items():
        if k in data and (not isinstance(data[k], list) or len(data[k]) > cap):
            raise BadProposal(f"{k} must be a list of at most {cap}")
    out = Proposal()
    for f in data.get("findings", []):
        f = _only(f, {"kind", "label", "title", "body", "refs"}, "finding")
        if f.get("kind") not in KINDS:
            raise BadProposal(f"finding kind must be one of {KINDS}")
        if f.get("label") not in LABELS:
            raise BadProposal(f"a finding is labelled one of {LABELS}; 'verified' is not an angel's word")
        refs = f.get("refs", [])
        if not isinstance(refs, list) or len(refs) > 8 or not all(isinstance(r, str) and len(r) <= 200 for r in refs):
            raise BadProposal("refs must be at most 8 short strings")
        out.findings.append({"kind": f["kind"], "label": f["label"], "title": _text(f, "title"), "body": _text(f, "body"), "refs": refs})
    for lf in data.get("lean_files", []):
        lf = _only(lf, {"path", "content", "purpose"}, "lean file")
        if not isinstance(lf.get("path"), str) or not PATH.match(lf["path"]):
            raise BadProposal("a Lean file's path must be Tengai/<Area>/<Name>.lean")
        out.lean_files.append({"path": lf["path"], "content": _text(lf, "content"), "purpose": _text(lf, "purpose")})
    for r in data.get("requests", []):
        r = _only(r, {"statement", "informal", "why"}, "request")
        out.requests.append({"statement": _text(r, "statement"), "informal": _text(r, "informal"), "why": _text(r, "why")})
    for d in data.get("delegate", []):
        d = _only(d, {"lens", "brief"}, "delegate")
        if not isinstance(d.get("lens"), str):
            raise BadProposal("delegate needs a lens")
        out.delegate.append({"lens": d["lens"], "brief": _text(d, "brief")})
    if out.delegate and not allow_delegate:
        out.delegate = []  # a helper at the bottom of the tree has nobody to delegate to: the archangel ignores it and records that
    for v in data.get("verdicts", []):
        v = _only(v, {"ref", "verdict", "reason"}, "verdict")
        if v.get("verdict") not in ("keep", "drop", "revise") or not isinstance(v.get("ref"), str):
            raise BadProposal("verdict: ref and one of keep|drop|revise")
        out.verdicts.append({"ref": v["ref"][:200], "verdict": v["verdict"], "reason": _text(v, "reason")})
    out.summary = str(data.get("summary", ""))[:600]
    return out

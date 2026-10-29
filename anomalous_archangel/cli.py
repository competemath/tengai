"""python -m anomalous_archangel <command>

drip      one drip (live: the claude CLI under containment, the gates Leak IV + Lake; --dry-run: a fake agent and a fake gate, in a copy)
root      regenerate Tengai.lean from the modules under Tengai/
gate      the gate on the whole tree as it is (CI): lint, then Lake with warnings as errors and the axiom audit; --leak-iv adds Leak IV
status    the index of drips and the open proof requests
requests  list | claim | fulfil | abandon: the queue leak-archangel works from
"""

from __future__ import annotations

import argparse
import json
import shutil
import sys
import tempfile
from pathlib import Path

from . import drip, gate, tree
from .agents import ClaudeCliRunner, FakeRunner
from .budget import Limits
from .requests import Queue


def repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def dry_runner() -> FakeRunner:
    """A deterministic stand-in so the whole pipeline can be seen working without spending anything."""

    def answer(spec):
        if spec.lens == "examiner":
            return {"verdicts": []}
        return {
            "summary": f"(dry run) the {spec.lens} looked at the tree.",
            "findings": [
                {
                    "kind": "note",
                    "label": "note",
                    "title": f"dry run: {spec.lens} saw the seed",
                    "body": "The tree holds the Gauss and odd-sum seeds and a bridge between them.",
                }
            ],
        }

    return FakeRunner(answer)


def cmd_drip(a) -> int:
    root = repo_root()
    if a.dry_run:
        tmp = Path(tempfile.mkdtemp(prefix="archangel-dry-"))
        for d in ("Tengai", "drips"):
            if (root / d).is_dir():
                shutil.copytree(root / d, tmp / d)
        for f in ("tengoku.pin", "Tengai.lean"):
            if (root / f).exists():
                shutil.copy(root / f, tmp / f)
        cfg = drip.Config(tmp, root / ".tengoku", a.budget, a.model, Limits(a.max_depth, a.breadth), "dry", a.breadth)
        runner, gates = dry_runner(), [gate.FakeGate("fake")]
        print(f"dry run in {tmp} (nothing in the repository changes)")
    else:
        cfg = drip.Config(root, root / ".tengoku", a.budget, a.model, Limits(a.max_depth, a.breadth), "live", a.breadth, land=not a.no_land)
        runner = ClaudeCliRunner()
        gates = [gate.LeakIVGate(), gate.LakeGate(root)] if not a.no_leak_iv else [gate.LakeGate(root)]
    rec = drip.run(cfg, runner, gates)
    print(json.dumps({"id": rec["id"], "counts": rec["counts"], "spent_usd": rec["budget"]["spent_usd"]}))
    return 0


def cmd_root(_a) -> int:
    root = repo_root()
    (root / "Tengai.lean").write_text(tree.root_file(tree.scan(root)))
    return 0


def cmd_gate(a) -> int:
    root = repo_root()
    tm = tree.scan(root)
    bad = 0
    for name, m in tm.modules.items():
        r = gate.lint(m.path, m.text)
        if not r.ok:
            bad += 1
            print(f"lint {name}: " + "; ".join(r.errors))
    if bad:
        return 1
    print(f"lint: {len(tm.modules)} modules clean")
    gates = [gate.LakeGate(root)] + ([gate.LeakIVGate()] if a.leak_iv else [])
    ok, results = gate.run_gates(gates, tm, tm.order())
    for r in results:
        print(f"{r.gate}: {r.kind} — {r.detail}")
        for e in r.errors[:20]:
            print("   ", e)
    return 0 if ok else 1


def cmd_status(_a) -> int:
    root = repo_root()
    try:
        idx = json.loads((root / "drips" / "index.json").read_text())
    except (OSError, ValueError):
        print("no drips yet")
        return 0
    print(f"{len(idx['drips'])} drips; tree {idx['tree']}; {idx['open_requests']} open proof requests")
    for d in idx["drips"][:10]:
        print(
            f"  {d['id']} {d['mode']:4} findings={d['counts']['findings']} landed={d['counts']['landed']} ${d['spent_usd']:.2f}  {d['summary'][:80]}"
        )
    return 0


def cmd_requests(a) -> int:
    root = repo_root()
    path = root / "drips" / "requests.json"
    q = Queue.load(path)
    if a.action == "list":
        for r in q.items:
            if a.all or r["status"] in ("open", "claimed"):
                print(f"{r['id']} {r['status']:9} {r['statement'][:110]}")
        return 0
    if not a.id:
        print("an id is required", file=sys.stderr)
        return 2
    try:
        if a.action == "claim":
            q.claim(a.id, a.who)
        elif a.action == "abandon":
            q.abandon(a.id, a.reason)
        elif a.action == "fulfil":
            return fulfil(root, q, path, a)
    except (KeyError, ValueError) as e:
        print(str(e), file=sys.stderr)
        return 1
    q.save(path)
    return 0


def fulfil(root: Path, q: Queue, qpath: Path, a) -> int:
    """Take a Lean file that proves a request, gate it, put it in the tree and mark the request proved."""
    item = q.get(a.id)
    if item is None or item["status"] not in ("open", "claimed"):
        print("no such open request", file=sys.stderr)
        return 1
    text = Path(a.file).read_text(encoding="utf-8")
    flat = " ".join(text.split())
    if " ".join(item["statement"].split()) not in flat:
        print("the file does not contain the request's statement verbatim", file=sys.stderr)
        return 1
    dest = f"Tengai/Proved/R{item['id']}.lean"
    cfg = drip.Config(root, root / ".tengoku")
    gates = [gate.LeakIVGate(), gate.LakeGate(root)]
    out = drip.land_candidates(cfg, [{"path": dest, "content": text, "lens": a.who, "purpose": f"proof of request {a.id}"}], gates)
    print(json.dumps(out[0]))
    if not out[0]["landed"]:
        return 1
    q.fulfil(a.id, dest)
    q.save(qpath)
    (root / "Tengai.lean").write_text(tree.root_file(tree.scan(root)))
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="anomalous_archangel", description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    d = sub.add_parser("drip")
    d.add_argument("--dry-run", action="store_true")
    d.add_argument("--budget", type=float, default=12.0, help="dollars for the whole drip, conserved down the tree of angels")
    d.add_argument("--model", default="claude-sonnet-5-5")
    d.add_argument("--max-depth", type=int, default=2)
    d.add_argument("--breadth", type=int, default=3)
    d.add_argument("--no-land", action="store_true", help="study only: nothing is written to the tree")
    d.add_argument("--no-leak-iv", action="store_true", help="gate with Lake alone")
    d.set_defaults(fn=cmd_drip)
    sub.add_parser("root").set_defaults(fn=cmd_root)
    g = sub.add_parser("gate")
    g.add_argument("--leak-iv", action="store_true")
    g.set_defaults(fn=cmd_gate)
    sub.add_parser("status").set_defaults(fn=cmd_status)
    r = sub.add_parser("requests")
    r.add_argument("action", choices=["list", "claim", "fulfil", "abandon"])
    r.add_argument("id", nargs="?")
    r.add_argument("--file")
    r.add_argument("--who", default="leak-archangel")
    r.add_argument("--reason", default="")
    r.add_argument("--all", action="store_true")
    r.set_defaults(fn=cmd_requests)
    a = ap.parse_args(argv)
    return a.fn(a)

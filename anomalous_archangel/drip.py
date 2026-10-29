"""One drip: anomalous-archangel studies the Tengai tree and acts on it.

    map the tree, read memory and Tengoku's arrivals -> choose lenses (<= breadth) -> spawn the angels with money reserved out of the
    budget -> each may send helpers one level down (limits and the ledger enforce depth, breadth and the conserved budget) -> the examiner
    wave -> drop repeats -> Lean candidates through lint and the gates, landing only what passes -> proof requests checked and queued ->
    record, report, index, memory.

The archangel is sovereign over the tree: it writes into it, replaces modules, and regenerates the root file. What it cannot do is land
anything the gate has not passed, or put a claim in a record without a label.
"""

from __future__ import annotations

import shutil
import tempfile
from dataclasses import dataclass, field
from datetime import UTC, datetime
from pathlib import Path

from . import SCHEMA, angels, gate, proposals, records, tengoku_view, tree
from .agents import AgentSpec
from .budget import Ledger, Limits, Node, Refused
from .memory import Memory
from .requests import Queue

COMPILING = ("leak-iv", "lake", "fake")


@dataclass
class Config:
    root: Path
    tengoku: Path
    budget_usd: float = 12.0
    model: str = "claude-sonnet-5-5"
    limits: Limits = field(default_factory=Limits)
    mode: str = "live"
    breadth: int = 3
    helper_share: float = 0.4
    examiner_share: float = 0.2
    land: bool = True
    timeout_s: int = 900

    @property
    def drips(self) -> Path:
        return self.root / "drips"


def now_utc() -> datetime:
    return datetime.now(UTC)


def stage_workdir(cfg: Config, ctx: dict, tm: tree.TreeMap, queue: Queue) -> Path:
    """The angels' own directory: a throwaway copy of the tree and the digests. Never the repository itself."""
    work = Path(tempfile.mkdtemp(prefix="archangel-"))
    shutil.copytree(cfg.root / "Tengai", work / "tree" / "Tengai") if (cfg.root / "Tengai").is_dir() else (work / "tree").mkdir()
    (work / "digest").mkdir()
    (work / "digest" / "map.txt").write_text(ctx["map"])
    (work / "digest" / "memory.txt").write_text(ctx["memory"])
    (work / "digest" / "tengoku-arrivals.txt").write_text(ctx["arrivals"])
    open_ = queue.open_items()
    (work / "digest" / "requests.txt").write_text(
        "OPEN PROOF REQUESTS\n" + "\n".join(f"- {r['id']}: {r['statement'][:200]}" for r in open_[:30]) + "\n"
    )
    return work


def run(cfg: Config, runner, gates: list, memory: Memory | None = None, clock=now_utc) -> dict:
    started = clock()
    cfg.drips.mkdir(parents=True, exist_ok=True)
    tm = tree.scan(cfg.root)
    mem = memory or Memory.load(cfg.drips / "memory.json")
    queue = Queue.load(cfg.drips / "requests.json")
    arr = tengoku_view.arrivals(cfg.tengoku)
    drip_id = f"{started.strftime('%Y%m%dT%H%MZ')}-{tm.hash()[:6]}"
    pin = (cfg.root / "tengoku.pin").read_text().strip() if (cfg.root / "tengoku.pin").exists() else ""
    ctx = {
        "drip": drip_id,
        "map": tm.digest(),
        "memory": mem.digest(),
        "arrivals": tengoku_view.digest(arr),
        "has_tengoku": (cfg.tengoku / "Tengoku").is_dir(),
    }
    work = stage_workdir(cfg, ctx, tm, queue)
    extra = [str(cfg.tengoku / "Tengoku")] if ctx["has_tengoku"] else []
    ledger = Ledger(cfg.budget_usd, cfg.limits)
    notes: list[str] = []
    findings: list[dict] = []
    candidates: list[dict] = []
    raw_requests: list[dict] = []
    summaries: list[str] = []

    def call(node: Node, lens_key: str, brief: str = "", items: str = "", can_delegate: bool = True) -> proposals.Proposal | None:
        node.status = "running"
        lens = angels.ROSTER[lens_key]
        reserve = cfg.helper_share if can_delegate and node.depth < cfg.limits.max_depth and lens_key != "examiner" else 0.0
        usd = node.allot_usd * (1 - reserve)
        spec = AgentSpec(
            lens=lens_key,
            prompt=angels.prompt(lens, {**ctx, "items": items}, brief, can_delegate),
            system=angels.SYSTEM,
            model=cfg.model,
            usd=usd,
            workdir=str(work),
            timeout_s=cfg.timeout_s,
            extra_read_dirs=extra,
        )
        res = runner.run(spec)
        ledger.charge(node.id, res.cost_usd)
        if not res.ok:
            notes.append(f"{lens_key} (node {node.id}) failed: {res.error[:200]}")
            ledger.finish(node.id, "failed")
            return None
        try:
            prop = proposals.parse(res.text, allow_delegate=can_delegate)
        except proposals.BadProposal as e:
            notes.append(f"{lens_key} (node {node.id}) answered badly: {e}")
            ledger.finish(node.id, "failed")
            return None
        return prop

    def absorb(node: Node, prop: proposals.Proposal) -> None:
        if prop.summary:
            summaries.append(f"{node.lens}: {prop.summary}")
        for f in prop.findings:
            findings.append({**f, "lens": node.lens, "node": node.id, "id": f"f{len(findings) + 1}"})
        for c in prop.lean_files:
            candidates.append({**c, "lens": node.lens, "node": node.id})
        for r in prop.requests:
            raw_requests.append({**r, "lens": node.lens})

    # ---- wave 1: the angels, each with helpers one level down ---------------------------------------------------------------
    lenses = angels.choose(
        mem, len(tm.modules), tm.stats()["theorems"], len(arr), sum(1 for a in arr if a["leak"]), len(queue.open_items()), cfg.breadth
    )
    wave = ledger.spawn_wave("0", lenses, fraction=1.0 - cfg.examiner_share)
    for node in wave:
        prop = call(node, node.lens)
        if prop is None:
            continue
        absorb(node, prop)
        if prop.delegate:
            ok_lenses = [d for d in prop.delegate if d["lens"] in angels.WORKERS]
            try:
                helpers = ledger.spawn_wave(node.id, [d["lens"] for d in ok_lenses])
            except Refused as e:
                helpers = []
                notes.append(f"{node.lens} asked for helpers: {e}")
            briefs = {d["lens"]: d["brief"] for d in ok_lenses}
            for h in helpers:
                hp = call(h, h.lens, brief=briefs.get(h.lens, ""), can_delegate=False)
                if hp is not None:
                    absorb(h, hp)
                    ledger.finish(h.id)
        ledger.finish(node.id)
    ledger.check()

    # ---- wave 2: the examiner ----------------------------------------------------------------------------------------------
    dropped = 0
    items = "\n".join(
        [f"- ref {f['id']} [{f['kind']}/{f['label']}] {f['title']}: {f['body'][:600]}" for f in findings]
        + [f"- ref file:{c['path']} (by {c['lens']}): {c['purpose']}\n{c['content'][:1500]}" for c in candidates]
        + [f"- ref req:{i} {r['statement'][:300]} — {r['why']}" for i, r in enumerate(raw_requests)]
    )
    if items and ledger.root.available > 0.0:
        try:
            ex_nodes = ledger.spawn_wave("0", ["examiner"], fraction=min(1.0, cfg.examiner_share * cfg.budget_usd / ledger.root.available))
        except Refused as e:
            ex_nodes = []
            notes.append(f"no examiner: {e}")
        for ex in ex_nodes:
            prop = call(ex, "examiner", items=items, can_delegate=False)
            if prop is not None:
                verdict = {v["ref"]: v for v in prop.verdicts}
                for f in list(findings):
                    v = verdict.get(f["id"])
                    if v and v["verdict"] == "drop":
                        findings.remove(f)
                        dropped += 1
                    elif v and v["verdict"] == "revise":
                        f["examiner"] = v["reason"]
                for c in list(candidates):
                    v = verdict.get(f"file:{c['path']}")
                    if v and v["verdict"] in ("drop", "revise"):
                        candidates.remove(c)
                        dropped += 1
                        notes.append(f"the examiner stopped {c['path']}: {v['reason']}")
                for i, r in reversed(list(enumerate(raw_requests))):
                    if verdict.get(f"req:{i}", {}).get("verdict") == "drop":
                        raw_requests.pop(i)
                        dropped += 1
                ledger.finish(ex.id)
    else:
        notes.append("no examination: nothing to examine, or no money left")
    for node in sorted(ledger.nodes.values(), key=lambda n: -n.depth):
        if node.id != "0" and node.status in ("pending", "running"):
            ledger.finish(node.id, "failed")
    ledger.root.status = "done"
    ledger.check()

    # ---- drop what earlier drips already said, label what is left ---------------------------------------------------------
    kept, repeats = [], 0
    for f in findings:
        if mem.is_repeat(f["title"], f["body"]):
            repeats += 1
            continue
        kept.append(f)
        mem.remember(drip_id, f["lens"], f)
    for n in ledger.nodes.values():
        if n.depth == 1:
            mem.ran(drip_id, n.lens)

    # ---- Lean: lint, gates, landing -----------------------------------------------------------------------------------------
    changes = [] if not cfg.land else land_candidates(cfg, candidates, gates)
    tm_after = tree.scan(cfg.root)
    if any(c["landed"] for c in changes):
        (cfg.root / "Tengai.lean").write_text(tree.root_file(tm_after))

    # ---- proof requests: checked by a compiling gate, then queued ---------------------------------------------------------
    stmt_gate = next((g for g in gates if hasattr(g, "compile")), None)
    queued = []
    for r in raw_requests:
        checked = False
        if stmt_gate is not None:
            res = stmt_gate.compile(f"import Tengoku.All\n\ntheorem tengai_request : {r['statement']} := by\n  sorry\n", allow_sorry=True)
            checked = res.ok
            if res.kind == "failed":
                notes.append(f"request dropped, it does not elaborate: {r['statement'][:80]} ({'; '.join(res.errors[:1])[:120]})")
                continue
        item, new = queue.add(r["statement"], r["informal"], r["why"], drip_id, r["lens"], started.isoformat(), checked)
        if new:
            queued.append(item)
    queue.save(cfg.drips / "requests.json")

    finished = clock()
    rec = {
        "schema": SCHEMA,
        "id": drip_id,
        "mode": cfg.mode,
        "started": started.isoformat(),
        "finished": finished.isoformat(),
        "tengoku_pin": pin,
        "summary": " ".join(summaries)[:900],
        "tree": {"before": tm.stats(), "after": tm_after.stats()},
        "arrivals": [{k: a[k] for k in ("date", "subject", "leak", "touches")} for a in arr[:20]],
        "spawn": {
            "limits": {"max_depth": cfg.limits.max_depth, "max_breadth": cfg.limits.max_breadth, "max_waves": cfg.limits.max_waves},
            "nodes": ledger.as_records(),
            "refused": ledger.refused,
        },
        "findings": kept,
        "changes": changes,
        "requests": queued,
        "budget": {"allot_usd": cfg.budget_usd, "spent_usd": round(ledger.spent_total(), 4)},
        "counts": {
            "findings": len(kept),
            "repeats": repeats,
            "examiner_dropped": dropped,
            "landed": sum(1 for c in changes if c["landed"]),
            "refused_files": sum(1 for c in changes if not c["landed"]),
            "requests": len(queued),
            "spawn_refused": len(ledger.refused),
        },
        "notes": notes,
    }
    records.write_record(cfg.drips, rec)
    records.update_index(cfg.drips, rec, queue.open_items(), tm_after.stats())
    mem.save(cfg.drips / "memory.json")
    shutil.rmtree(work, ignore_errors=True)
    return rec


def land_candidates(cfg: Config, candidates: list[dict], gates: list) -> list[dict]:
    """Each file is written, gated together with everything that depends on it, and kept only if every gate says ok (and at least one of them
    compiled it). A refused file is put back exactly as it was."""
    out = []
    for c in candidates:
        path = cfg.root / c["path"]
        old = path.read_text(encoding="utf-8") if path.exists() else None
        ch = {
            "path": c["path"],
            "action": "modify" if old is not None else "create",
            "lens": c["lens"],
            "purpose": c["purpose"],
            "gates": [],
            "landed": False,
            "reason": "",
        }
        out.append(ch)
        lint = gate.lint(c["path"], c["content"])
        ch["gates"].append({"gate": "lint", "kind": lint.kind, "detail": lint.detail})
        if not lint.ok:
            ch["reason"] = "; ".join(lint.errors[:3])
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(c["content"] if c["content"].endswith("\n") else c["content"] + "\n", encoding="utf-8")
        try:
            tm = tree.scan(cfg.root)
            name = tree.module_name(cfg.root, path)
            affected = [m for m in tm.order() if name in tm.closure(m)]
        except ValueError as e:  # an import cycle
            ch["reason"] = str(e)
            restore(path, old)
            continue
        ok, results = gate.run_gates(gates, tm, affected)
        ch["gates"] += [{"gate": r.gate, "kind": r.kind, "detail": r.detail[:300]} for r in results]
        compiled = any(r.ok and r.gate in COMPILING for r in results)
        if ok and compiled:
            ch["landed"] = True
        else:
            ch["reason"] = "; ".join((results[-1].errors or [results[-1].detail])[:2])[:300] if results else "no gate"
            if ok and not compiled:
                ch["reason"] = "no compiling gate was available"
            restore(path, old)
    return out


def restore(path: Path, old: str | None) -> None:
    if old is None:
        path.unlink(missing_ok=True)
    else:
        path.write_text(old, encoding="utf-8")

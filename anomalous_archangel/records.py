"""What a drip leaves behind: a record (JSON, for programs), a report (Markdown, for people), and the index the dashboard reads."""

from __future__ import annotations

import json
from pathlib import Path

INDEX_KEEP = 200


def write_record(drips: Path, rec: dict) -> Path:
    d = drips / rec["id"]
    d.mkdir(parents=True, exist_ok=True)
    (d / "record.json").write_text(json.dumps(rec, indent=1, ensure_ascii=False) + "\n")
    (d / "report.md").write_text(render_report(rec))
    return d


def render_report(rec: dict) -> str:
    c = rec["counts"]
    out = [
        f"# Drip {rec['id']}",
        "",
        f"{rec['mode']} drip · {rec['started']} · spent ${rec['budget']['spent_usd']:.2f} of ${rec['budget']['allot_usd']:.2f} · "
        f"tree {rec['tree']['before']['modules']} → {rec['tree']['after']['modules']} modules, {rec['tree']['after']['theorems']} theorems",
        "",
        f"**{c['findings']} findings kept** ({c['repeats']} repeats of earlier drips dropped, {c['examiner_dropped']} dropped by the examiner) · "
        f"**{c['landed']} Lean files landed**, {c['refused_files']} refused by the gate · **{c['requests']} proof requests** queued · "
        f"{c['spawn_refused']} spawns refused by the limits",
        "",
    ]
    if rec.get("summary"):
        out += [rec["summary"], ""]
    if rec["changes"]:
        out += ["## Lean changes", ""]
        for ch in rec["changes"]:
            gates = ", ".join(f"{g['gate']}:{g['kind']}" for g in ch["gates"])
            out.append(
                f"- `{ch['path']}` ({ch['action']}) — {'landed' if ch['landed'] else 'NOT landed'} · {gates}"
                + (f" · {ch['reason']}" if ch.get("reason") else "")
            )
        out.append("")
    by_kind: dict[str, list[dict]] = {}
    for f in rec["findings"]:
        by_kind.setdefault(f["kind"], []).append(f)
    for kind, items in by_kind.items():
        out += [f"## {kind.capitalize()}", ""]
        for f in items:
            out += [f"### {f['title']}  ·  `{f['label']}` · {f['lens']}", ""]
            out += [f"```\n{f['body']}\n```" if kind == "picture" else f["body"], ""]
            if f.get("examiner"):
                out += [f"> examiner: {f['examiner']}", ""]
    if rec["requests"]:
        out += ["## Proof requests (for leak-archangel)", ""]
        out += [f"- `{r['id']}` ({r['status']}) `{r['statement'][:160]}` — {r['why']}" for r in rec["requests"]]
        out.append("")
    out += ["## Angels", ""]
    out += [
        f"- {n['id']} {n['lens']} (depth {n['depth']}): ${n['spent_usd']:.2f} of ${n['allot_usd']:.2f}, {n['status']}"
        for n in rec["spawn"]["nodes"]
    ]
    if rec["spawn"]["refused"]:
        out += ["", "Refused by the limits: " + ", ".join(f"{r['lens']} ({r['why']})" for r in rec["spawn"]["refused"])]
    if rec.get("notes"):
        out += ["", "## Notes", ""] + [f"- {n}" for n in rec["notes"]]
    return "\n".join(out) + "\n"


def index_entry(rec: dict) -> dict:
    return {
        "id": rec["id"],
        "started": rec["started"],
        "mode": rec["mode"],
        "summary": rec.get("summary", ""),
        "counts": rec["counts"],
        "spent_usd": round(rec["budget"]["spent_usd"], 4),
        "tree": rec["tree"]["after"],
        "tengoku_pin": rec.get("tengoku_pin", ""),
        "lenses": [n["lens"] for n in rec["spawn"]["nodes"] if n["depth"] == 1],
        "top": [{"kind": f["kind"], "label": f["label"], "title": f["title"], "lens": f["lens"]} for f in rec["findings"][:4]],
        "landed": [c["path"] for c in rec["changes"] if c["landed"]],
        "path": f"drips/{rec['id']}/report.md",
    }


def update_index(drips: Path, rec: dict, open_requests: list[dict], stats: dict) -> dict:
    p = drips / "index.json"
    try:
        old = json.loads(p.read_text())["drips"]
    except (OSError, ValueError, KeyError):
        old = []
    drips_list = [index_entry(rec)] + [d for d in old if d["id"] != rec["id"]]
    index = {
        "schema": "anomalous-archangel/index/1",
        "updated": rec["finished"],
        "tree": stats,
        "open_requests": len(open_requests),
        "drips": drips_list[:INDEX_KEEP],
    }
    p.write_text(json.dumps(index, indent=1, ensure_ascii=False) + "\n")
    return index

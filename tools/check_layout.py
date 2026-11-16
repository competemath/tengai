#!/usr/bin/env python3
"""check_layout.py - the layout rules of Tengai that are not Lean's to enforce (docs/design.md, "tengai layout"). Standard library only; run from the repository root.

  cones.toml     every Tengai/<Topic>/ directory is a declared topic and every declared topic exists; the declared parents exist and form no cycle; a module imports only Lean core,
                 its own topic and its declared parents (no `import Tengoku...`, ever: invariant I3); a topic has at most `max_modules` modules.
  data/          `<id>.json`, exactly one per statement id: {"id", "name", "module"} (+ optional "promoted_from"), the file named by the id, the id in isnad's format, the module a file.
  tawatur/       `<id>/route.json` + `route-1.lean` .. `route-3.lean` (at most three), the directory named by an isnad id; and Tengai.lean (the default import cone) imports none of it.

Prints one line per problem and exits 1 when there is any.
"""

from __future__ import annotations

import json
import re
import sys
import tomllib
from pathlib import Path

ID_RE = re.compile(r"[a-z0-9]{1,8}\.\d+h\d+v\.s\d+\.[0-9a-f]{12}")
IMPORT_RE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(\S+)", re.M)
CORE = ("Init", "Std", "Lean")


def topics_on_disk(root: Path) -> dict[str, list[Path]]:
    base = root / "Tengai"
    if not base.is_dir():
        return {}
    return {d.name: sorted(d.rglob("*.lean")) for d in sorted(base.iterdir()) if d.is_dir()}


def find_cycle(parents: dict[str, list[str]]) -> list[str] | None:
    state: dict[str, int] = {}
    stack: list[str] = []

    def visit(n: str) -> list[str] | None:
        state[n] = 1
        stack.append(n)
        for p in parents.get(n, []):
            if state.get(p) == 1:
                return [*stack[stack.index(p) :], p]
            if state.get(p) is None and (c := visit(p)):
                return c
        stack.pop()
        state[n] = 2
        return None

    for n in sorted(parents):
        if state.get(n) is None and (c := visit(n)):
            return c
    return None


def check_cones(root: Path) -> list[str]:
    problems: list[str] = []
    cfg_path = root / "cones.toml"
    declared = tomllib.loads(cfg_path.read_text(encoding="utf-8")).get("topic", {}) if cfg_path.is_file() else {}
    disk = topics_on_disk(root)
    for t in sorted(set(disk) - set(declared)):
        problems.append(f"cones: Tengai/{t}/ exists and cones.toml does not declare topic {t}")
    for t in sorted(set(declared) - set(disk)):
        problems.append(f"cones: topic {t} is declared and Tengai/{t}/ does not exist")
    parents = {t: list(v.get("parents", [])) for t, v in declared.items()}
    for t, ps in parents.items():
        problems += [f"cones: topic {t} names the parent {p}, which is not a declared topic" for p in ps if p not in declared]
    cycle = find_cycle({t: [p for p in ps if p in declared] for t, ps in parents.items()})
    if cycle:
        problems.append("cones: the parents form a cycle: " + " -> ".join(cycle))
    for t, files in disk.items():
        cap = declared.get(t, {}).get("max_modules")
        if cap is not None and len(files) > cap:
            problems.append(f"cones: topic {t} has {len(files)} modules, over its budget of {cap}")
        allowed = {t, *parents.get(t, [])}
        for f in files:
            for imp in IMPORT_RE.findall(f.read_text(encoding="utf-8")):
                parts = imp.split(".")
                if parts[0] in CORE or imp == "Tengai":
                    continue
                if parts[0] == "Tengai" and len(parts) > 1 and parts[1] in allowed:
                    continue
                why = "Tengoku is never imported (I3)" if parts[0] == "Tengoku" else f"topic {t} may import only {sorted(allowed)}"
                problems.append(f"cones: {f.relative_to(root)} imports {imp}: {why}")
    return problems


def check_data(root: Path) -> list[str]:
    problems: list[str] = []
    for f in sorted((root / "data").glob("*.json")) if (root / "data").is_dir() else []:
        try:
            rec = json.loads(f.read_text(encoding="utf-8"))
        except ValueError:
            problems.append(f"data: {f.name} is not JSON")
            continue
        if not isinstance(rec, dict) or not {"id", "name", "module"} <= set(rec):
            problems.append(f"data: {f.name} needs id, name and module")
            continue
        if not ID_RE.fullmatch(str(rec["id"])):
            problems.append(f"data: {f.name}: {rec['id']!r} is not an isnad id")
        if f.stem != rec["id"]:
            problems.append(f"data: {f.name} is not named by its id {rec['id']}")
        if not (root / (str(rec["module"]).replace(".", "/") + ".lean")).is_file():
            problems.append(f"data: {f.name}: the module {rec['module']} is not a file")
    return problems


def check_tawatur(root: Path) -> list[str]:
    problems: list[str] = []
    base = root / "tawatur"
    for d in sorted(p for p in base.iterdir() if p.is_dir()) if base.is_dir() else []:
        if not ID_RE.fullmatch(d.name):
            problems.append(f"tawatur: {d.name}/ is not named by an isnad id")
        if not (d / "route.json").is_file():
            problems.append(f"tawatur: {d.name}/ has no route.json")
        routes = sorted(p.name for p in d.glob("*.lean"))
        if not routes or len(routes) > 3 or routes != [f"route-{i}.lean" for i in range(1, len(routes) + 1)]:
            problems.append(f"tawatur: {d.name}/ must hold route-1.lean .. route-3.lean, at most three and without gaps: {routes}")
    root_lean = root / "Tengai.lean"
    if root_lean.is_file() and any(i.split(".")[0].lower() == "tawatur" for i in IMPORT_RE.findall(root_lean.read_text(encoding="utf-8"))):
        problems.append("tawatur: Tengai.lean imports the alternate routes: they stay out of the default import cone")
    return problems


def main(argv: list[str] | None = None) -> int:
    root = Path(argv[0]) if argv else Path(".")
    problems = check_cones(root) + check_data(root) + check_tawatur(root)
    for p in problems:
        print(p)
    print(f"layout: {len(problems)} problem(s)" if problems else "layout: ok")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

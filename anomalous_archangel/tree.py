"""A map of the Tengai tree: modules, what they import, what they declare. Read by the archangel before every drip and handed to the angels
as a digest; also the source of the root file and the closure the Leak IV gate compiles."""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass, field
from pathlib import Path

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|nonrec)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom)\s+([^\s({\[:]+)?"
)
IMPORT = re.compile(r"^(?:public\s+)?import\s+([A-Za-z0-9_.]+)\s*$")
NAMESPACE = re.compile(r"^namespace\s+(\S+)\s*$")
SECTION = re.compile(r"^section(?:\s+(\S+))?\s*$")
END = re.compile(r"^end(?:\s+(\S+))?\s*$")
DOC = re.compile(r"^/--\s*(.*?)\s*(?:-/)?$")


@dataclass
class Decl:
    kind: str
    name: str  # fully qualified, as far as the namespaces show it
    line: int
    doc: str = ""


@dataclass
class Module:
    name: str
    path: str
    imports: list[str]
    decls: list[Decl] = field(default_factory=list)
    doc: str = ""
    lines: int = 0
    sha: str = ""
    text: str = ""


@dataclass
class TreeMap:
    modules: dict[str, Module]

    def tengai_imports(self, name: str) -> list[str]:
        return [i for i in self.modules[name].imports if i in self.modules]

    def order(self) -> list[str]:
        """Topological order, dependencies first; raises on a cycle."""
        seen: dict[str, int] = {}
        out: list[str] = []

        def visit(n: str) -> None:
            if seen.get(n) == 2:
                return
            if seen.get(n) == 1:
                raise ValueError(f"import cycle through {n}")
            seen[n] = 1
            for i in sorted(self.tengai_imports(n)):
                visit(i)
            seen[n] = 2
            out.append(n)

        for n in sorted(self.modules):
            visit(n)
        return out

    def closure(self, name: str) -> list[str]:
        """The module and everything of Tengai it needs, dependencies first."""
        need: set[str] = set()

        def go(n: str) -> None:
            if n in need:
                return
            need.add(n)
            for i in self.tengai_imports(n):
                go(i)

        go(name)
        return [n for n in self.order() if n in need]

    def hash(self) -> str:
        h = hashlib.sha256()
        for n in sorted(self.modules):
            h.update(n.encode() + b"\0" + self.modules[n].sha.encode() + b"\0")
        return h.hexdigest()[:16]

    def stats(self) -> dict:
        return {
            "modules": len(self.modules),
            "declarations": sum(len(m.decls) for m in self.modules.values()),
            "theorems": sum(1 for m in self.modules.values() for d in m.decls if d.kind in ("theorem", "lemma")),
            "lines": sum(m.lines for m in self.modules.values()),
            "hash": self.hash(),
        }

    def digest(self, max_chars: int = 24_000) -> str:
        """What the angels read first: every module with its imports and its declarations, shortest useful form."""
        out = [f"TENGAI MAP — {self.stats()}"]
        for n in self.order():
            m = self.modules[n]
            out.append(f"\n## {n}  ({m.lines} lines; imports {', '.join(m.imports) or '-'})")
            if m.doc:
                out.append(m.doc)
            for d in m.decls:
                out.append(f"- {d.kind} {d.name}" + (f" — {d.doc}" if d.doc else ""))
        text = "\n".join(out)
        return text if len(text) <= max_chars else text[: max_chars - 40] + "\n…[map cut at the size limit]"


def module_name(root: Path, path: Path) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def parse_module(name: str, rel: str, text: str) -> Module:
    imports: list[str] = []
    decls: list[Decl] = []
    stack: list[tuple[str, str]] = []  # ("ns" | "sec", name)
    doc_next = ""
    module_doc = ""
    in_module_doc = False
    for i, raw in enumerate(text.splitlines(), 1):
        line = raw.rstrip()
        if in_module_doc:
            if "-/" in line:
                in_module_doc = False
            elif len(module_doc) < 600 and line.strip():
                module_doc += line.strip() + " "
            continue
        if line.startswith("/-!"):
            in_module_doc = "-/" not in line
            continue
        if m := IMPORT.match(line):
            imports.append(m.group(1))
            continue
        if m := NAMESPACE.match(line):
            stack.append(("ns", m.group(1)))
            continue
        if m := SECTION.match(line):
            stack.append(("sec", m.group(1) or ""))
            continue
        if m := END.match(line):
            if stack:
                stack.pop()
            continue
        if m := DOC.match(line):
            doc_next = m.group(1)[:140]
            continue
        if m := DECL.match(line):
            nm = m.group(2)
            if nm and not nm.removeprefix("_root_.").startswith("_"):
                ns = ".".join(n for k, n in stack if k == "ns")
                full = nm if nm.startswith("_root_.") else (f"{ns}.{nm}" if ns else nm)
                decls.append(Decl(m.group(1), full.removeprefix("_root_."), i, doc_next))
            doc_next = ""
    return Module(name, rel, imports, decls, module_doc.strip(), text.count("\n") + 1, hashlib.sha256(text.encode()).hexdigest()[:16], text)


def scan(root: Path) -> TreeMap:
    mods: dict[str, Module] = {}
    base = root / "Tengai"
    for p in sorted(base.rglob("*.lean")) if base.is_dir() else []:
        n = module_name(root, p)
        mods[n] = parse_module(n, str(p.relative_to(root)), p.read_text(encoding="utf-8"))
    return TreeMap(mods)


def root_file(tm: TreeMap) -> str:
    head = "-- Tengai: the root. anomalous-archangel regenerates this list (python -m anomalous_archangel root); every module under Tengai/ is imported.\n"
    return head + "".join(f"import {n}\n" for n in sorted(tm.modules))

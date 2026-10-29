"""The gate. A Lean change lands in Tengai only when every configured gate says `ok`:

1. `lint`    — a static look at the text: no sorry/admit/axiom/native_decide/unsafe/extern, no global notation or macros (a library that leaks
               notation breaks everybody who imports it: Tengoku's canary exists because of one), imports only `Tengoku.All` and Tengai,
               bounded size. Runs first because it is free.
2. `leak-iv` — the file and everything of Tengai it needs, as one script, compiled by Leak IV (`verify_full_script` over MCP/SSE, the verifier
               the provers use): no errors, no warnings, no sorry.
3. `lake`    — `lake build` of the module and of every module that depends on it, against Tengoku at the pin; the lakefile turns every
               warning into an error. Then every declaration's axioms are printed and only propext, Classical.choice and Quot.sound are allowed.

A gate that cannot be asked (the space is down, there is no Lean on this machine) answers `infra`, and `infra` is not `ok`: the change is
deferred, never landed unchecked. At least one compiling gate (leak-iv or lake) must have said `ok` for a change to land.
"""

from __future__ import annotations

import http.client
import json
import os
import re
import subprocess
import threading
import time
import urllib.request
from collections.abc import Callable
from dataclasses import dataclass, field
from pathlib import Path
from urllib.parse import urlsplit

from .containment import CLI_OWN, SECRET_NAME
from .tree import TreeMap

MAX_BYTES = 60_000
MAX_LINES = 1500
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SPACES = {"leak-iv": "https://barkingtree-leak-iv.hf.space"}
ENDPOINT = re.compile(r"/messages/\?session_id=([0-9a-fA-F-]{8,64})")
DIAG = re.compile(r"^Line (\d+) \((Error|Warning)\): (.*)$", re.M)
FORBIDDEN = [
    (r"\bsorry\b", "sorry"),
    (r"\badmit\b", "admit"),
    (r"\baxiom\b", "axiom"),
    (r"\bopaque\b", "opaque"),
    (r"native_decide|bv_decide", "native_decide / bv_decide (they trust the compiler)"),
    (r"\bunsafe\b", "unsafe"),
    (r"implemented_by|@\[\s*extern|@\[\s*export|\bpartial\b", "implemented_by / extern / export / partial"),
    (r"\b(run_cmd|run_elab|run_meta|run_tac|initialize|builtin_initialize)\b|#eval|#exit|#reduce", "code that runs at elaboration"),
    (
        r"(?m)^\s*(?<!local )(?<!scoped )(notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules|declare_syntax_cat)\b",
        "global notation, syntax or macros (use `local` or `scoped`)",
    ),
    (r"set_option\s+(linter\.\S+\s+false|warningAsError\s+false|autoImplicit\s+true)", "switching a check off"),
    (r"set_option\s+maxHeartbeats\s+(\d+)", "maxHeartbeats (checked below)"),
    (r"attribute\s*\[[^\]]*\binstance\b", "a global instance attribute"),
]
IMPORT_OK = re.compile(r"^(import Tengoku\.All|import Tengai(\.[A-Za-z0-9_]+)+)\s*$")


@dataclass
class GateResult:
    gate: str
    kind: str  # ok | failed | infra
    detail: str = ""
    errors: list[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return self.kind == "ok"


def strip_noise(text: str) -> str:
    """The text without comments and string literals (nested block comments handled), keeping line structure."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        two = text[i : i + 2]
        if depth:
            if two == "/-":
                depth += 1
                i += 2
            elif two == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif two == "/-":
            depth = 1
            i += 2
        elif two == "--":
            while i < n and text[i] != "\n":
                i += 1
        elif text[i] == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            out.append('""')
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def lint(path: str, text: str) -> GateResult:
    errs = []
    if len(text.encode()) > MAX_BYTES:
        errs.append(f"{len(text.encode())} bytes, the limit is {MAX_BYTES}")
    if text.count("\n") > MAX_LINES:
        errs.append(f"more than {MAX_LINES} lines")
    clean = strip_noise(text)
    if "import Tengoku.All" not in clean:
        errs.append("the file must import Tengoku.All")
    for ln, line in enumerate(clean.splitlines(), 1):
        if line.startswith("import ") or line.startswith("public import "):
            if not IMPORT_OK.match(line.strip()):
                errs.append(f"line {ln}: import not allowed ({line.strip()}); only Tengoku.All and Tengai.*")
    for pat, why in FORBIDDEN:
        for m in re.finditer(pat, clean):
            if "maxHeartbeats" in why:
                if int(m.group(1)) > 400_000:
                    errs.append(f"maxHeartbeats {m.group(1)} is above 400000")
                continue
            errs.append(f"line {clean.count(chr(10), 0, m.start()) + 1}: {why}")
            break
    return GateResult("lint", "failed" if errs else "ok", f"{path}: {len(errs)} problem(s)" if errs else path, errs)


def closure_script(tm: TreeMap, module: str) -> str:
    """One script for Leak IV: the header, then each module of the closure (dependencies first) in its own section without its imports."""
    parts = ["import Tengoku.All", ""]
    for name in tm.closure(module):
        body = "\n".join(ln for ln in tm.modules[name].text.splitlines() if not re.match(r"^(public\s+)?import\s", ln))
        sec = name.replace(".", "_")
        parts += [f"section {sec}", body, f"end {sec}", ""]
    return "\n".join(parts)


def verdict(text: str, allow_sorry: bool = False) -> tuple[str, list[str]]:
    """('ok' | 'failed' | 'infra', messages): the reply of verify_full_script. Warnings fail it, as the Tengai gate says; a statement check
    (`allow_sorry`) forgives the warning that says `sorry` and nothing else."""
    diags = [(int(m.group(1)), m.group(2), m.group(3)) for m in DIAG.finditer(text)]
    errors = [f"line {n}: {msg[:200]}" for n, kind, msg in diags if kind == "Error"]
    warns = [f"line {n}: {msg[:200]}" for n, kind, msg in diags if kind == "Warning" and not (allow_sorry and "sorry" in msg)]
    if errors or warns:
        return "failed", errors + warns
    if "Compilation Successful" in text:
        return "ok", []
    if re.search(r"verify exceeded|timed out|timeout|Verification Error", text):
        return "infra", [text[:200]]
    return ("failed", [text[:200]]) if "Compilation Failed" in text else ("infra", [text[:200]])


class Unreachable(Exception):
    pass


def checked_space(url: str) -> str:
    u = urlsplit(url.strip())
    local = u.hostname in ("127.0.0.1", "localhost", "::1")
    if not (u.scheme == "https" or (u.scheme == "http" and local)):
        raise ValueError(f"the space must be an https URL (http only on this machine), not {url!r}")
    if not u.hostname or u.username or u.password or u.query or u.fragment or u.path not in ("", "/"):
        raise ValueError(f"the space must be an origin (https://host[:port]), not {url!r}")
    return f"{u.scheme}://{u.netloc}"


def call_tool(base: str, tool: str, args: dict, timeout: float = 900.0) -> str:
    """One MCP tool call over SSE (the way Tengoku's own canary client does it): open the stream, take the message endpoint it names,
    initialize, call, read the reply from the stream. The address is this client's (base + the path every Leak space serves)."""
    base = checked_space(base)
    replies: dict[int, dict] = {}
    cond = threading.Condition()
    state: dict = {"endpoint": None, "dead": None}
    deadline = time.monotonic() + timeout

    def pump() -> None:
        try:
            req = urllib.request.Request(f"{base}/sse", headers={"accept": "text/event-stream"})
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                event, data = None, []
                for raw in resp:
                    line = raw.decode("utf-8", "replace").rstrip("\r\n")
                    if line == "":
                        with cond:
                            if event == "endpoint":
                                m = ENDPOINT.fullmatch("\n".join(data).strip())
                                if m:
                                    state["endpoint"] = f"/messages/?session_id={m.group(1)}"
                                else:
                                    state["dead"] = Unreachable("the stream names an endpoint that is not /messages/?session_id=<hex>")
                            elif event == "message":
                                try:
                                    msg = json.loads("\n".join(data))
                                    if isinstance(msg, dict) and msg.get("id") is not None:
                                        replies[msg["id"]] = msg
                                except ValueError:
                                    pass
                            cond.notify_all()
                        event, data = None, []
                    elif line.startswith("event:"):
                        event = line[6:].strip()
                    elif line.startswith("data:"):
                        data.append(line[5:].lstrip())
        except Exception as e:  # the stream ended or never opened
            with cond:
                state["dead"] = e
                cond.notify_all()

    threading.Thread(target=pump, daemon=True).start()

    def wait(pred: Callable[[], bool]) -> None:
        with cond:
            while not pred():
                if state["dead"] is not None and not pred():
                    raise Unreachable(f"{base}: the stream ended: {state['dead']!r}")
                left = deadline - time.monotonic()
                if left <= 0:
                    raise Unreachable(f"{base}: no answer in {timeout:.0f} s")
                cond.wait(min(left, 5))

    def post(body: dict) -> None:
        u = urlsplit(base)
        conn = (http.client.HTTPSConnection if u.scheme == "https" else http.client.HTTPConnection)(u.hostname, u.port, timeout=60)
        try:
            conn.request("POST", state["endpoint"], body=json.dumps(body).encode(), headers={"content-type": "application/json"})
            resp = conn.getresponse()
            resp.read()
            if resp.status >= 400:
                raise Unreachable(f"{base}: POST answered {resp.status}")
        except Unreachable:
            raise
        except Exception as e:
            raise Unreachable(f"{base}: POST failed: {e!r}") from e
        finally:
            conn.close()

    wait(lambda: state["endpoint"] is not None)
    post(
        {
            "jsonrpc": "2.0",
            "id": 1,
            "method": "initialize",
            "params": {"protocolVersion": "2024-11-05", "capabilities": {}, "clientInfo": {"name": "anomalous-archangel", "version": "1"}},
        }
    )
    wait(lambda: 1 in replies)
    post({"jsonrpc": "2.0", "method": "notifications/initialized"})
    post({"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": tool, "arguments": args}})
    wait(lambda: 2 in replies)
    out = replies[2]
    if out.get("error"):
        raise Unreachable(f"{base}: {json.dumps(out['error'])[:300]}")
    return "\n".join(c.get("text", "") for c in (out.get("result") or {}).get("content", []))


class LeakIVGate:
    name = "leak-iv"

    def __init__(
        self, space: str = "leak-iv", caller: Callable[[str, str, dict, float], str] | None = None, timeout: float = 900.0, retries: int = 2
    ) -> None:
        self.base = SPACES[space]
        self.caller = caller or call_tool
        self.timeout, self.retries = timeout, retries

    def compile(self, script: str, allow_sorry: bool = False) -> GateResult:
        last = ""
        for attempt in range(self.retries + 1):
            try:
                text = self.caller(self.base, "verify_full_script", {"script": script}, self.timeout)
            except Unreachable as e:
                last = str(e)
                time.sleep(min(30 * (attempt + 1), 60) if self.caller is call_tool else 0)
                continue
            kind, msgs = verdict(text, allow_sorry)
            if kind != "infra":
                return GateResult(self.name, kind, "compiled by Leak IV", msgs)
            last = "; ".join(msgs)
        return GateResult(self.name, "infra", last[:300])

    def check(self, tm: TreeMap, modules: list[str]) -> GateResult:
        for m in modules:
            r = self.compile(closure_script(tm, m))
            if not r.ok:
                return GateResult(self.name, r.kind, f"{m}: {r.detail}", r.errors)
        return GateResult(self.name, "ok", f"{len(modules)} module(s) compiled by Leak IV")


class LakeGate:
    name = "lake"

    def __init__(self, root: Path, runner: Callable[..., subprocess.CompletedProcess] | None = None) -> None:
        self.root = root
        self.run = runner or (lambda *a, **k: subprocess.run(*a, **k))
        # Lean runs what it is given: the compile gets no token of any kind (the agents' login included)
        self.env = {k: v for k, v in os.environ.items() if not (SECRET_NAME.search(k) or CLI_OWN.match(k))}

    def available(self) -> str:
        if not (self.root / ".tengoku" / "lakefile.toml").exists():
            return "no .tengoku checkout (scripts/tengoku-setup.sh)"
        try:
            self.run(["lake", "--version"], capture_output=True, text=True, timeout=30, check=True)
        except (OSError, subprocess.SubprocessError):
            return "lake is not installed"
        return ""

    def check(self, tm: TreeMap, modules: list[str]) -> GateResult:
        why = self.available()
        if why:
            return GateResult(self.name, "infra", why)
        errs: list[str] = []
        for m in modules:
            r = self.run(["lake", "build", m], capture_output=True, text=True, timeout=3600, cwd=self.root, env=self.env, check=False)
            out = r.stdout + r.stderr
            bad = [ln for ln in out.splitlines() if re.match(r"^(error|warning)\b", ln.strip()) or "sorry" in ln]
            if r.returncode != 0 or bad:
                return GateResult(self.name, "failed", f"{m}: lake build failed", (bad or out.splitlines()[-8:])[:20])
        errs += self.axioms(tm, modules)
        return GateResult(
            self.name, "failed" if errs else "ok", "; ".join(errs[:3]) if errs else f"{len(modules)} module(s) built, axioms clean", errs
        )

    def axioms(self, tm: TreeMap, modules: list[str]) -> list[str]:
        names = sorted({d.name for m in modules for d in tm.modules[m].decls if d.kind in ("theorem", "lemma")})
        if not names:
            return []
        gate_dir = self.root / ".gate"
        gate_dir.mkdir(exist_ok=True)
        f = gate_dir / "Axioms.lean"
        f.write_text("import " + "\nimport ".join(modules) + "\n" + "\n".join(f"#print axioms {n}" for n in names) + "\n")
        r = self.run(
            ["lake", "env", "lean", str(f)], capture_output=True, text=True, timeout=1800, cwd=self.root, env=self.env, check=False
        )
        return axiom_problems(r.stdout + r.stderr)


def axiom_problems(out: str) -> list[str]:
    """Read the output of `#print axioms`: every name must rest on the three classical axioms at most."""
    problems = []
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
        extra = {a.strip() for a in m.group(2).split(",") if a.strip()} - ALLOWED_AXIOMS
        if extra:
            problems.append(f"{m.group(1)} rests on {sorted(extra)}")
    for ln in out.splitlines():
        if "unknown constant" in ln or "unknown identifier" in ln:
            problems.append(f"the audit could not find a name: {ln.strip()[:160]}")
    return problems


class FakeGate:
    """A gate that answers from a function of the module list (tests and --dry-run)."""

    def __init__(self, name: str = "fake", fn: Callable[[TreeMap, list[str]], GateResult] | None = None) -> None:
        self.name = name
        self.fn = fn
        self.calls: list[list[str]] = []

    def check(self, tm: TreeMap, modules: list[str]) -> GateResult:
        self.calls.append(modules)
        return self.fn(tm, modules) if self.fn else GateResult(self.name, "ok", "fake")


def run_gates(gates: list, tm: TreeMap, modules: list[str]) -> tuple[bool, list[GateResult]]:
    """Every gate must say ok; the lint comes first. Returns (landable, results). Stops at the first failure."""
    results: list[GateResult] = []
    for g in gates:
        r = g.check(tm, modules)
        results.append(r)
        if not r.ok:
            return False, results
    return bool(results), results

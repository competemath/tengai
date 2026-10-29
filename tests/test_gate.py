import json
import subprocess
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

import pytest

from anomalous_archangel import gate, tree

ROOT = Path(__file__).resolve().parent.parent
OK_FILE = "import Tengoku.All\n\nnamespace Tengai\n\ntheorem foo (n : ℕ) : n = n := rfl\n\nend Tengai\n"


def test_lint_accepts_a_clean_file_and_ignores_comments_and_strings():
    assert gate.lint("Tengai/A.lean", OK_FILE).ok
    noisy = OK_FILE + '-- sorry axiom\n/- native_decide /- nested sorry -/ still comment -/\ndef s : String := "sorry axiom"\n'
    assert gate.lint("Tengai/A.lean", noisy).ok


@pytest.mark.parametrize(
    "bad",
    [
        "theorem x : True := by sorry",
        "axiom foo : False",
        "theorem x : 1 = 1 := by native_decide",
        "unsafe def f := 1",
        'notation "∘∘" => Nat.add',
        'macro "foo" : tactic => `(tactic| rfl)',
        "#eval 1",
        "set_option linter.unusedVariables false",
        "set_option maxHeartbeats 4000000",
        "attribute [instance] foo",
        "import Mathlib.Data.Nat.Basic",
        "opaque f : Nat",
        "@[implemented_by foo] def g := 1",
    ],
)
def test_lint_refuses(bad):
    assert not gate.lint("Tengai/A.lean", OK_FILE + "\n" + bad + "\n").ok


def test_local_and_scoped_notation_are_fine():
    assert gate.lint("Tengai/A.lean", OK_FILE + '\nlocal notation "ff" => Nat.succ\nscoped infixl:65 " +++ " => Nat.add\n').ok


def test_a_file_must_import_tengoku_and_be_small():
    assert not gate.lint("p", "theorem x : True := trivial\n").ok
    assert not gate.lint("p", OK_FILE + "-- " + "x" * 70_000).ok


def test_verdicts():
    assert gate.verdict("Compilation Successful")[0] == "ok"
    assert gate.verdict("Compilation Successful\nLine 3 (Warning): unused variable")[0] == "failed"
    assert gate.verdict("Line 2 (Error): boom")[0] == "failed"
    assert gate.verdict("verify exceeded the time limit")[0] == "infra"
    sorry = "Line 3 (Warning): declaration uses 'sorry'\nCompilation Successful"
    assert gate.verdict(sorry)[0] == "failed" and gate.verdict(sorry, allow_sorry=True)[0] == "ok"


def test_axiom_audit():
    out = "'Tengai.a' depends on axioms: [propext, Classical.choice, Quot.sound]\n'Tengai.b' depends on axioms: [sorryAx]\n'Tengai.c' does not depend on any axioms"
    assert gate.axiom_problems(out) == ["Tengai.b rests on ['sorryAx']"]
    assert gate.axiom_problems("error: unknown constant 'Tengai.z'")


def _mini_tree(tmp_path):
    (tmp_path / "Tengai").mkdir()
    (tmp_path / "Tengai" / "A.lean").write_text("import Tengoku.All\n\nnamespace Tengai\ndef a := 1\nend Tengai\n")
    (tmp_path / "Tengai" / "B.lean").write_text("import Tengoku.All\nimport Tengai.A\n\nnamespace Tengai\ndef b := a + 1\nend Tengai\n")
    return tree.scan(tmp_path)


def test_the_closure_script_is_one_header_and_sectioned_bodies(tmp_path):
    s = gate.closure_script(_mini_tree(tmp_path), "Tengai.B")
    assert s.count("import ") == 1 and s.startswith("import Tengoku.All")
    assert s.index("section Tengai_A") < s.index("def a") < s.index("end Tengai_A") < s.index("section Tengai_B") < s.index("def b")


def test_leak_iv_gate_with_a_fake_caller(tmp_path):
    tm = _mini_tree(tmp_path)
    seen = []

    def caller(base, tool, args, timeout):
        seen.append((base, tool, args["script"][:20]))
        return "Compilation Successful"

    g = gate.LeakIVGate(caller=caller)
    assert g.check(tm, ["Tengai.B"]).ok and seen[0][1] == "verify_full_script"
    bad = gate.LeakIVGate(caller=lambda *a: "Line 1 (Error): no")
    assert bad.check(tm, ["Tengai.B"]).kind == "failed"

    def down(*a):
        raise gate.Unreachable("down")

    assert gate.LeakIVGate(caller=down, retries=1).check(tm, ["Tengai.B"]).kind == "infra"


def test_lake_gate_without_tengoku_is_infra_not_ok(tmp_path):
    assert gate.LakeGate(tmp_path).check(_mini_tree(tmp_path), ["Tengai.A"]).kind == "infra"


def test_lake_gate_reads_the_build_output(tmp_path):
    tm = _mini_tree(tmp_path)
    (tmp_path / ".tengoku").mkdir()
    (tmp_path / ".tengoku" / "lakefile.toml").write_text("")

    def runner(cmd, **kw):
        if cmd[:2] == ["lake", "--version"]:
            return subprocess.CompletedProcess(cmd, 0, "Lake", "")
        if cmd[:2] == ["lake", "build"]:
            return subprocess.CompletedProcess(cmd, 0, warning, "")
        return subprocess.CompletedProcess(cmd, 0, "'Tengai.a' depends on axioms: [propext]", "")

    warning = "warning: Tengai/A.lean:3:4: unused variable `x`"
    r = gate.LakeGate(tmp_path, runner).check(tm, ["Tengai.A"])
    assert r.kind == "failed" and "Tengai/A.lean" in r.errors[0]
    # Lake replays the saved warnings of Tengoku's own modules on every build: those are not Tengai's
    warning = "warning: Tengoku/LeanPool/Foo.lean:365:66: This simp argument is unused:"
    assert gate.LakeGate(tmp_path, runner).check(tm, ["Tengai.A"]).kind == "ok"


def test_run_gates_stops_at_the_first_failure_and_needs_one():
    tm = tree.TreeMap({})
    bad = gate.FakeGate("a", lambda *_: gate.GateResult("a", "failed", "no"))
    never = gate.FakeGate("b")
    ok, res = gate.run_gates([bad, never], tm, [])
    assert not ok and never.calls == [] and len(res) == 1
    assert gate.run_gates([], tm, []) == (False, [])


class _FakeSpace(BaseHTTPRequestHandler):
    """A minimal Leak space: /sse names an endpoint and then answers the posted JSON-RPC messages on the stream."""

    box: dict = {}

    def log_message(self, *a):
        pass

    def do_GET(self):
        self.send_response(200)
        self.send_header("content-type", "text/event-stream")
        self.end_headers()
        sid = "abcdef0123456789"
        self.wfile.write(f"event: endpoint\r\ndata: /messages/?session_id={sid}\r\n\r\n".encode())
        self.wfile.flush()
        q = self.box.setdefault("q", [])
        for _ in range(200):
            while q:
                msg = q.pop(0)
                self.wfile.write(f"event: message\r\ndata: {json.dumps(msg)}\r\n\r\n".encode())
                self.wfile.flush()
                if msg.get("id") == 2:
                    return
            threading.Event().wait(0.05)

    def do_POST(self):
        body = json.loads(self.rfile.read(int(self.headers["content-length"])))
        self.send_response(202)
        self.end_headers()
        if body.get("method") == "initialize":
            self.box.setdefault("q", []).append({"jsonrpc": "2.0", "id": 1, "result": {}})
        elif body.get("method") == "tools/call":
            self.box["script"] = body["params"]["arguments"]["script"]
            self.box.setdefault("q", []).append(
                {"jsonrpc": "2.0", "id": 2, "result": {"content": [{"type": "text", "text": "Compilation Successful"}]}}
            )


def test_the_mcp_client_against_a_local_fake_space():
    _FakeSpace.box = {}
    srv = ThreadingHTTPServer(("127.0.0.1", 0), _FakeSpace)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    try:
        text = gate.call_tool(f"http://127.0.0.1:{srv.server_port}", "verify_full_script", {"script": "import Tengoku.All"}, timeout=20)
    finally:
        srv.shutdown()
    assert text == "Compilation Successful" and _FakeSpace.box["script"] == "import Tengoku.All"


def test_spaces_must_be_origins_over_https():
    for bad in ("http://evil.example", "https://u:p@x.y", "https://x.y/path", "file:///etc/passwd", "https://x.y?q=1"):
        with pytest.raises(ValueError):
            gate.checked_space(bad)
    assert gate.checked_space("https://x.y/") == "https://x.y"

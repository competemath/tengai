import json
import shutil
from datetime import UTC, datetime
from pathlib import Path

from anomalous_archangel import cli, drip, gate, tree
from anomalous_archangel.agents import FakeRunner
from anomalous_archangel.budget import Limits
from anomalous_archangel.memory import Memory
from anomalous_archangel.requests import Queue

ROOT = Path(__file__).resolve().parent.parent
GOOD = "import Tengoku.All\n\nnamespace Tengai\n\ntheorem lifted (n : ℕ) : n + 0 = n := rfl\n\nend Tengai\n"
CLOCK = lambda: datetime(2026, 10, 29, 12, 0, tzinfo=UTC)  # noqa: E731


def make_root(tmp_path):
    shutil.copytree(ROOT / "Tengai", tmp_path / "Tengai")
    (tmp_path / "tengoku.pin").write_text("a" * 40 + "\n")
    (tmp_path / "Tengai.lean").write_text(tree.root_file(tree.scan(tmp_path)))
    return tmp_path


def cfg(root, **kw):
    return drip.Config(root, root / ".tengoku", **{"budget_usd": 10.0, "mode": "dry", **kw})


def script(answers):
    """lens -> answer, a dict, a callable of the spec, or a string; unknown lenses answer with nothing"""

    def answer(spec):
        a = answers.get(spec.lens, {})
        return a(spec) if callable(a) else a

    return FakeRunner(answer, cost=0.5)


def test_a_whole_drip_with_a_fake_agent(tmp_path):
    root = make_root(tmp_path)
    runner = script(
        {
            "abstractor": {
                "summary": "generalised",
                "findings": [
                    {
                        "kind": "abstraction",
                        "label": "conjecture",
                        "title": "odd sum in a semiring",
                        "body": "needs only a commutative semiring",
                        "refs": [],
                    }
                ],
                "lean_files": [{"path": "Tengai/Seed/Lifted.lean", "content": GOOD, "purpose": "a lift"}],
                "requests": [{"statement": "∀ n : ℕ, n + 0 = n", "informal": "trivial", "why": "test"}],
            }
        }
    )
    g = gate.FakeGate("leak-iv")
    g.compile = lambda script, allow_sorry=False: gate.GateResult("leak-iv", "ok")
    rec = drip.run(cfg(root), runner, [g], Memory(), CLOCK)
    assert rec["counts"]["landed"] == 1 and (root / "Tengai/Seed/Lifted.lean").read_text().strip() == GOOD.strip()
    assert "import Tengai.Seed.Lifted" in (root / "Tengai.lean").read_text()
    assert rec["counts"]["requests"] == 1 and Queue.load(root / "drips/requests.json").items[0]["status"] == "open"
    assert all(f["label"] in ("note", "observation", "conjecture") for f in rec["findings"])
    d = root / "drips" / rec["id"]
    assert (d / "record.json").exists() and "Lean changes" in (d / "report.md").read_text()
    idx = json.loads((root / "drips/index.json").read_text())
    assert idx["drips"][0]["id"] == rec["id"] and idx["open_requests"] == 1 and idx["tree"]["modules"] == 4
    assert rec["budget"]["spent_usd"] <= rec["budget"]["allot_usd"]
    # the next drip does not say the same thing again
    everyone_says_it = FakeRunner(lambda spec: {} if spec.lens == "examiner" else runner.answer(type("S", (), {"lens": "abstractor"})()))
    again = drip.run(cfg(root), everyone_says_it, [g], Memory.load(root / "drips/memory.json"), lambda: datetime(2026, 10, 30, tzinfo=UTC))
    assert again["counts"]["repeats"] >= 1 and again["counts"]["requests"] == 0


def test_a_file_the_gate_refuses_is_not_kept(tmp_path):
    root = make_root(tmp_path)
    before = (root / "Tengai.lean").read_text()
    runner = script({"abstractor": {"lean_files": [{"path": "Tengai/Seed/Bad.lean", "content": GOOD, "purpose": "p"}]}})
    failing = gate.FakeGate("lake", lambda tm, mods: gate.GateResult("lake", "failed", "boom", ["error: boom"]))
    rec = drip.run(cfg(root), runner, [failing], Memory(), CLOCK)
    assert rec["counts"]["landed"] == 0 and not (root / "Tengai/Seed/Bad.lean").exists()
    assert (root / "Tengai.lean").read_text() == before
    assert "boom" in rec["changes"][0]["reason"]


def test_sorry_is_stopped_before_any_gate_runs(tmp_path):
    root = make_root(tmp_path)
    g = gate.FakeGate("leak-iv")
    runner = script(
        {"abstractor": {"lean_files": [{"path": "Tengai/Seed/S.lean", "content": GOOD.replace("rfl", "by sorry"), "purpose": "p"}]}}
    )
    rec = drip.run(cfg(root), runner, [g], Memory(), CLOCK)
    assert rec["counts"]["landed"] == 0 and g.calls == [] and not (root / "Tengai/Seed/S.lean").exists()


def test_an_unavailable_gate_defers_and_nothing_lands_unchecked(tmp_path):
    root = make_root(tmp_path)
    runner = script({"abstractor": {"lean_files": [{"path": "Tengai/Seed/D.lean", "content": GOOD, "purpose": "p"}]}})
    down = gate.FakeGate("lake", lambda tm, mods: gate.GateResult("lake", "infra", "no lean here"))
    rec = drip.run(cfg(root), runner, [down], Memory(), CLOCK)
    assert rec["counts"]["landed"] == 0 and not (root / "Tengai/Seed/D.lean").exists()
    none = drip.run(cfg(root), runner, [], Memory(), CLOCK)
    assert none["counts"]["landed"] == 0


def test_replacing_a_module_gates_everything_that_depends_on_it(tmp_path):
    root = make_root(tmp_path)
    g = gate.FakeGate("leak-iv")
    runner = script(
        {
            "abstractor": {
                "lean_files": [
                    {"path": "Tengai/Seed/Gauss.lean", "content": (ROOT / "Tengai/Seed/Gauss.lean").read_text() + "\n", "purpose": "p"}
                ]
            }
        }
    )
    drip.run(cfg(root), runner, [g], Memory(), CLOCK)
    assert g.calls and "Tengai.Bridge.GaussOdd" in g.calls[0] and "Tengai.Seed.Gauss" in g.calls[0]


def test_spawn_limits_hold_and_helpers_cannot_spawn(tmp_path):
    root = make_root(tmp_path)

    def abstractor(spec):
        return {"delegate": [{"lens": k, "brief": "b"} for k in ("bridger", "experimenter", "illustrator", "historian", "cartographer")]}

    def helper(spec):  # a helper tries to delegate too
        return {
            "delegate": [{"lens": "bridger", "brief": "again"}],
            "findings": [{"kind": "note", "label": "note", "title": f"helper {spec.lens}", "body": f"unique body {spec.lens}"}],
        }

    runner = script(
        {k: helper for k in ("bridger", "experimenter", "illustrator", "historian", "cartographer")} | {"abstractor": abstractor}
    )
    c = cfg(root, limits=Limits(2, 3, 2))
    # make the abstractor one of the chosen lenses: a first drip with an empty memory ranks cartographer, abstractor, bridger first
    rec = drip.run(c, runner, [gate.FakeGate("fake")], Memory(), CLOCK)
    depths = [n["depth"] for n in rec["spawn"]["nodes"]]
    assert max(depths) == 2 and depths.count(1) <= 3 + 1  # three angels plus the examiner
    for parent in {n["parent"] for n in rec["spawn"]["nodes"] if n["parent"]}:
        assert sum(1 for n in rec["spawn"]["nodes"] if n["parent"] == parent and n["lens"] != "examiner") <= 3
    assert any(r["why"] == "breadth" for r in rec["spawn"]["refused"])
    assert rec["budget"]["spent_usd"] <= rec["budget"]["allot_usd"] + 1e-6
    assert not any(n["depth"] > 2 for n in rec["spawn"]["nodes"])


def test_the_examiner_can_drop_a_finding(tmp_path):
    root = make_root(tmp_path)
    runner = script(
        {
            "cartographer": {
                "findings": [{"kind": "note", "label": "note", "title": "wrong claim", "body": "the sum of odd numbers is cubic"}]
            },
            "examiner": lambda spec: {"verdicts": [{"ref": "f1", "verdict": "drop", "reason": "false"}]},
        }
    )
    rec = drip.run(cfg(root), runner, [gate.FakeGate("fake")], Memory(), CLOCK)
    assert rec["counts"]["examiner_dropped"] == 1 and not any(f["title"] == "wrong claim" for f in rec["findings"])


def test_a_broken_angel_costs_something_and_stops_nothing(tmp_path):
    root = make_root(tmp_path)
    runner = script({"cartographer": "no json block here at all"})
    rec = drip.run(cfg(root), runner, [gate.FakeGate("fake")], Memory(), CLOCK)
    assert any("answered badly" in n for n in rec["notes"]) and rec["budget"]["spent_usd"] > 0


def test_the_cli_dry_run_changes_nothing_in_the_repository(tmp_path, capsys):
    before = {p: p.read_bytes() for p in (ROOT / "Tengai").rglob("*.lean")}
    assert cli.main(["drip", "--dry-run", "--budget", "3"]) == 0
    assert "dry run in" in capsys.readouterr().out
    assert before == {p: p.read_bytes() for p in (ROOT / "Tengai").rglob("*.lean")}

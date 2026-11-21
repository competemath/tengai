"""tengai-replay: an export of a fixture becomes a built .olean through the kernel; a corrupted export is refused. CI runs it after building lean4export.

Needs: LEAN4EXPORT (path of the lean4export binary), and `lake build tengai-replay` done. Without LEAN4EXPORT every test is skipped (a laptop has no Lean here: CI is where this runs).
"""

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / "tests" / "replay" / "fixture"
EXPORTER = os.environ.get("LEAN4EXPORT")


def run(cmd, cwd, **kw):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False, **kw)


@unittest.skipUnless(EXPORTER, "LEAN4EXPORT is not set")
class Replay(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        cls.dir = Path(cls.tmp.name)
        b = run(["lake", "build"], FIXTURE)
        assert b.returncode == 0, b.stdout + b.stderr
        e = run(["lake", "env", EXPORTER, "Fx"], FIXTURE)
        assert e.returncode == 0, e.stderr
        cls.export = cls.dir / "fx.ndjson"
        cls.export.write_text(e.stdout, encoding="utf-8")

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def replay(self, export, out, *extra):
        return run(["lake", "exe", "tengai-replay", str(export), "--module", "TengaiData.Fx", "--out", str(out), *extra], ROOT)

    def check(self, out, name):
        env = {**os.environ, "LEAN_PATH": f"{out}:{run(['lake', 'env', 'printenv', 'LEAN_PATH'], ROOT).stdout.strip()}"}
        return run(["lake", "env", "lean", str(ROOT / "tests" / "replay" / name)], ROOT, env=env)

    def test_the_fixture_is_replayed_and_used(self):
        out = self.dir / "out"
        r = self.replay(self.export, out)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        stats = json.loads(r.stdout.strip().splitlines()[-1])["replay"]
        self.assertGreater(stats["added"], 10)
        self.assertGreater(stats["skipped"], 5)  # Lean core's own constants are not added again
        self.assertGreaterEqual(stats["inductives"], 3)  # Color, Pt, Tree
        self.assertTrue((out / "TengaiData" / "Fx.olean").exists())
        env = {**os.environ, "LEAN_PATH": f"{out}:{run(['lake', 'env', 'printenv', 'LEAN_PATH'], ROOT).stdout.strip()}"}
        c = run(["lake", "env", "lean", str(ROOT / "tests" / "replay" / "check.lean")], ROOT, env=env)
        self.assertEqual(c.returncode, 0, c.stdout + c.stderr)
        # the axioms are the ones the proofs use, and nothing else
        self.assertIn("'Fx.add_swap' does not depend on any axioms", c.stdout)
        self.assertIn("Quot.sound", c.stdout.split("Fx.fun_ext_ex")[1].split("Fx.")[0])
        self.assertIn("Classical.choice", c.stdout.split("Fx.em_ex")[1])

    def test_extension_entries_are_carried_and_without_them_the_goal_fails(self):
        # negative control: a plain replay holds the kernel constants only, so instance synthesis and reducible unfolding find nothing
        plain = self.dir / "plain"
        self.assertEqual(self.replay(self.export, plain).returncode, 0)
        c = self.check(plain, "check_ext.lean")
        self.assertNotEqual(c.returncode, 0, c.stdout)
        self.assertIn("synthesize", c.stdout + c.stderr)
        # what Lean keeps about the constants, read where they were built, then put back
        added, ext, withext = self.dir / "added.jsonl", self.dir / "ext.jsonl", self.dir / "withext"
        self.assertEqual(self.replay(self.export, self.dir / "pass1", "--added", str(added)).returncode, 0)
        x = run(["lake", "env", str(ROOT / ".lake" / "build" / "bin" / "tengai-extinfo"), str(added), "Fx"], FIXTURE)
        self.assertEqual(x.returncode, 0, x.stderr)
        ext.write_text(x.stdout, encoding="utf-8")
        rows = [json.loads(ln) for ln in x.stdout.splitlines()]
        kinds = {k for r in rows for k in r if k != "n"}
        self.assertEqual(kinds, {"red", "proj", "class", "inst"})
        r = self.replay(self.export, withext, "--ext", str(ext))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        counts = json.loads(r.stdout.strip().splitlines()[-1])["ext"]
        self.assertGreaterEqual(counts["instances"], 1)
        self.assertGreaterEqual(counts["classes"], 1)
        self.assertGreaterEqual(counts["reducibility"], 1)
        c = self.check(withext, "check_ext.lean")
        self.assertEqual(c.returncode, 0, c.stdout + c.stderr)
        self.assertIn("instSzNat", c.stdout)

    def test_binder_annotations_survive_the_export(self):
        """the binder annotations lean4export wrote for constants whose annotations are known (Lean core): the exporter and the reader agree on them"""
        names, exprs, decls = {0: ""}, {}, {}
        for ln in self.export.read_text(encoding="utf-8").splitlines():
            o = json.loads(ln)
            if "in" in o:
                v = o.get("str") or o["num"]
                part = v["str"] if "str" in v else str(v["i"])
                names[o["in"]] = f"{names[v['pre']]}.{part}" if names[v["pre"]] else part
            elif "ie" in o:
                exprs[o["ie"]] = o
            else:
                for kind in ("def", "thm", "axiom", "opaque"):
                    if kind in o:
                        decls[names[o[kind]["name"]]] = o[kind]["type"]
                if "inductive" in o:
                    for t in o["inductive"]["types"] + o["inductive"]["ctors"]:
                        decls[names[t["name"]]] = t["type"]

        def chain(name):
            out, e = [], exprs[decls[name]]
            while "forallE" in e:
                out.append(e["forallE"]["binderInfo"])
                e = exprs[e["forallE"]["body"]]
            return out

        got = {n: chain(n) for n in ("Inhabited.default", "Nat.add_comm", "Eq.mpr", "Fx.Sz.n", "Fx.add_swap", "Fx.Sz.mk", "Add.add", "instAddNat") if n in decls}
        known = {"Inhabited.default": ["implicit", "instImplicit"], "Nat.add_comm": ["default", "default"], "Add.add": ["implicit", "instImplicit", "default", "default"]}
        for n, want in known.items():
            self.assertEqual(got.get(n), want, f"{n}: lean4export wrote {got.get(n)}, Lean core declares {want}; all: {got}")

    def test_typeinfo_reads_the_same_statement_in_both_environments(self):
        names = self.dir / "names.jsonl"
        names.write_text(json.dumps(["Fx", "add_swap"]) + "\n" + json.dumps(["Fx", "Sz", "n"]) + "\n", encoding="utf-8")
        src = run(["lake", "env", str(ROOT / ".lake" / "build" / "bin" / "tengai-typeinfo"), str(names), "Fx"], FIXTURE)
        self.assertEqual(src.returncode, 0, src.stderr)
        out = self.dir / "ti"
        self.assertEqual(self.replay(self.export, out).returncode, 0)
        env = {**os.environ, "LEAN_PATH": f"{out}:{run(['lake', 'env', 'printenv', 'LEAN_PATH'], ROOT).stdout.strip()}"}
        rep = run(["lake", "env", str(ROOT / ".lake" / "build" / "bin" / "tengai-typeinfo"), str(names), "TengaiData.Fx"], ROOT, env=env)
        self.assertEqual(rep.returncode, 0, rep.stderr)
        a = [json.loads(x) for x in src.stdout.splitlines()]
        b = [json.loads(x) for x in rep.stdout.splitlines()]
        self.assertEqual(len(a), 2)
        for x, y in zip(a, b):
            self.assertNotIn("missing", x)
            # the replay keeps every binder, annotation and head constant; the node count may be smaller by the expression metadata it drops.
            # Binder NAMES are not compared: lean4export shares alpha-equivalent terms and keeps the first it saw (Fx.add_swap comes back with Nat.add_comm's `n m`, not its own `a b`)
            shape = lambda r: [(b["info"], b["head"]) for b in r["binders"]]  # noqa: E731
            self.assertEqual(shape(x), shape(y), x["n"])
            self.assertEqual(x["size"] - x["mdata"], y["size"] - y["mdata"], x["n"])

    def test_the_replay_is_deterministic(self):
        a, b = self.dir / "a", self.dir / "b"
        self.assertEqual(self.replay(self.export, a).returncode, 0)
        self.assertEqual(self.replay(self.export, b).returncode, 0)
        self.assertEqual((a / "TengaiData" / "Fx.olean").read_bytes(), (b / "TengaiData" / "Fx.olean").read_bytes())

    def test_a_wrong_proof_is_refused_by_the_kernel(self):
        # point a theorem's value at its own type: the kernel must say the value does not have the type
        lines = self.export.read_text(encoding="utf-8").splitlines()
        bad = []
        done = False
        names = {0: ""}
        for ln in lines:
            o = json.loads(ln)
            if "in" in o:
                v = o.get("str") or o["num"]
                part = v["str"] if "str" in v else str(v["i"])
                pre = names[v["pre"]]
                names[o["in"]] = f"{pre}.{part}" if pre else part
            # a theorem of the fixture, not one of Lean core (a core constant is skipped, so corrupting it proves nothing)
            if not done and "thm" in o and names[o["thm"]["name"]] == "Fx.add_swap":
                o["thm"]["value"] = o["thm"]["type"]
                done = True
            bad.append(json.dumps(o, separators=(",", ":")))
        self.assertTrue(done)
        corrupted = self.dir / "bad.ndjson"
        corrupted.write_text("\n".join(bad) + "\n", encoding="utf-8")
        r = self.replay(corrupted, self.dir / "badout")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("kernel", r.stderr + r.stdout)
        self.assertFalse((self.dir / "badout" / "TengaiData" / "Fx.olean").exists())


if __name__ == "__main__":
    sys.exit(unittest.main())

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
        self.assertEqual(kinds, {"red", "proj", "class", "inst", "bi", "st"})
        r = self.replay(self.export, withext, "--ext", str(ext))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        counts = json.loads(r.stdout.strip().splitlines()[-1])["ext"]
        self.assertGreaterEqual(counts["instances"], 1)
        self.assertGreaterEqual(counts["classes"], 1)
        self.assertGreaterEqual(counts["reducibility"], 1)
        c = self.check(withext, "check_ext.lean")
        self.assertEqual(c.returncode, 0, c.stdout + c.stderr)
        self.assertIn("instSzNat", c.stdout)

    def test_structure_information_is_carried_and_without_it_the_notation_fails(self):
        """`{ x := 1 }`, `{ p with x := 2 }` and `p.x` through a parent read a structure's field information, which Lean keeps outside the kernel like instances and reducibility."""
        added, ext = self.dir / "sadded.jsonl", self.dir / "sext.jsonl"
        self.assertEqual(self.replay(self.export, self.dir / "spass1", "--added", str(added)).returncode, 0)
        x = run(["lake", "env", str(ROOT / ".lake" / "build" / "bin" / "tengai-extinfo"), str(added), "Fx"], FIXTURE)
        self.assertEqual(x.returncode, 0, x.stderr)
        ext.write_text(x.stdout, encoding="utf-8")
        rows = [json.loads(ln) for ln in x.stdout.splitlines()]
        st = {".".join(str(c) for c in r["n"]): r["st"] for r in rows if "st" in r}
        self.assertEqual(sorted(st), ["Fx.Pt", "Fx.Pt3", "Fx.Sz"])  # the structures and the class of the fixture
        self.assertEqual([f["f"] for f in st["Fx.Pt3"]["fields"]], [["toPt"], ["z"]])
        self.assertEqual(st["Fx.Pt3"]["fields"][0]["sub"], ["Fx", "Pt"])  # the embedded parent
        self.assertEqual(st["Fx.Pt3"]["parents"], [{"s": ["Fx", "Pt"], "sub": True, "proj": ["Fx", "Pt3", "toPt"]}])
        # the control: the same entries without the structure information
        without = self.dir / "swithout.jsonl"
        kept = [{k: v for k, v in r.items() if k != "st"} for r in rows]
        without.write_text("".join(json.dumps(r) + "\n" for r in kept if len(r) > 1), encoding="utf-8")
        plain = self.dir / "sout_plain"
        r = self.replay(self.export, plain, "--ext", str(without))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        c = self.check(plain, "check_struct.lean")
        self.assertNotEqual(c.returncode, 0, c.stdout)
        full = self.dir / "sout_full"
        r = self.replay(self.export, full, "--ext", str(ext))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        counts = json.loads(r.stdout.strip().splitlines()[-1])["ext"]
        self.assertEqual(counts["structures"], 3)
        self.assertEqual(counts["failed"], 0, r.stderr)
        c = self.check(full, "check_struct.lean")
        self.assertEqual(c.returncode, 0, c.stdout + c.stderr)

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

    def test_the_binder_names_and_annotations_of_the_source_are_restored(self):
        """lean4export shares terms equal up to binder names and annotations and keeps the first it saw: the plain replay of `Fx.Sz.n` has {α} and an explicit self, `Fx.add_swap` has `n m`.
        With the extension file the leading binders are put back before the kernel sees the type, and tengai-typeinfo reads the same telescope in both environments."""
        names = self.dir / "tnames.jsonl"
        names.write_text(json.dumps(["Fx", "add_swap"]) + "\n" + json.dumps(["Fx", "Sz", "n"]) + "\n", encoding="utf-8")
        typeinfo = str(ROOT / ".lake" / "build" / "bin" / "tengai-typeinfo")
        src = run(["lake", "env", typeinfo, str(names), "Fx"], FIXTURE)
        self.assertEqual(src.returncode, 0, src.stderr)
        added, ext = self.dir / "tadded.jsonl", self.dir / "text.jsonl"
        self.assertEqual(self.replay(self.export, self.dir / "tpass1", "--added", str(added)).returncode, 0)
        x = run(["lake", "env", str(ROOT / ".lake" / "build" / "bin" / "tengai-extinfo"), str(added), "Fx"], FIXTURE)
        self.assertEqual(x.returncode, 0, x.stderr)
        ext.write_text(x.stdout, encoding="utf-8")

        def read(out):
            env = {**os.environ, "LEAN_PATH": f"{out}:{run(['lake', 'env', 'printenv', 'LEAN_PATH'], ROOT).stdout.strip()}"}
            r = run(["lake", "env", typeinfo, str(names), "TengaiData.Fx"], ROOT, env=env)
            self.assertEqual(r.returncode, 0, r.stderr)
            return [json.loads(ln) for ln in r.stdout.splitlines()]

        plain_out, fixed_out = self.dir / "tplain", self.dir / "tfixed"
        self.assertEqual(self.replay(self.export, plain_out).returncode, 0)
        r = self.replay(self.export, fixed_out, "--ext", str(ext))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        a = [json.loads(ln) for ln in src.stdout.splitlines()]
        plain, fixed = read(plain_out), read(fixed_out)
        self.assertEqual(len(a), 2)
        # the control: without the file the telescope of the class projection is not the source's
        self.assertNotEqual([b["info"] for b in plain[1]["binders"]], [b["info"] for b in a[1]["binders"]], plain[1])
        for x_, y_ in zip(a, fixed):
            self.assertNotIn("missing", y_)
            self.assertEqual(x_["binders"], y_["binders"], x_["n"])  # names, annotations and heads
            self.assertEqual(x_["size"] - x_["mdata"], y_["size"] - y_["mdata"], x_["n"])

    def test_a_promotion_in_layers_loads_a_layer_with_what_it_imports_and_no_more(self):
        # two theorems share a definition: it is the foundation layer, each theorem is a layer of its own that imports it (`--only` names what a layer adds, `--import` what it starts from)
        out = self.dir / "layers"
        for stem, names in (("f", ["Fx.shared"]), ("a", ["Fx.left_use"]), ("b", ["Fx.right_use"])):
            (self.dir / f"{stem}.names").write_text("".join(json.dumps(n.split(".")) + "\n" for n in names))
        lean_path = f"{out}:{run(['lake', 'env', 'printenv', 'LEAN_PATH'], ROOT).stdout.strip()}"
        env = {**os.environ, "LEAN_PATH": lean_path}

        def layer(module, stem, *imports):
            cmd = ["lake", "exe", "tengai-replay", str(self.export), "--module", module, "--out", str(out), "--only", str(self.dir / f"{stem}.names")]
            for m in imports:
                cmd += ["--import", m]
            r = run(cmd, ROOT, env=env)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            return json.loads(r.stdout.strip().splitlines()[-1])["replay"]

        foundation = layer("TengaiData.F", "f")
        left = layer("TengaiData.A", "a", "TengaiData.F")
        right = layer("TengaiData.B", "b", "TengaiData.F")
        # each layer holds exactly the constants it was given; everything else of the export was left out (or is in an imported layer)
        self.assertEqual((foundation["added"], left["added"], right["added"]), (1, 1, 1))
        self.assertGreater(foundation["filtered"], 0)

        def check(name):
            return run(["lake", "env", "lean", str(ROOT / "tests" / "replay" / name)], ROOT, env=env)

        a = check("check_layer_a.lean")
        self.assertEqual(a.returncode, 0, a.stdout + a.stderr)  # layer A sees its theorem and the foundation it imports
        self.assertIn("'Fx.left_use' does not depend on any axioms", a.stdout)
        b = check("check_layer_b.lean")
        self.assertEqual(b.returncode, 0, b.stdout + b.stderr)
        self.assertIn("'Fx.right_use' does not depend on any axioms", b.stdout)
        # layers are independent of each other: A does not pull B in
        only = check("check_layer_a_only.lean")
        self.assertNotEqual(only.returncode, 0, only.stdout)
        self.assertIn("right_use", only.stdout + only.stderr)
        both = check("check_layer_ab.lean")
        self.assertEqual(both.returncode, 0, both.stdout + both.stderr)
        # the replay of a layer is itself kernel-checked: a layer given a constant whose dependency is in no imported layer is refused
        broken = run(["lake", "exe", "tengai-replay", str(self.export), "--module", "TengaiData.Bad", "--out", str(out), "--only", str(self.dir / "a.names")], ROOT, env=env)
        self.assertNotEqual(broken.returncode, 0, broken.stdout)  # Fx.left_use without Fx.shared: unknown constant

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

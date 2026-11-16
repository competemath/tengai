import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import check_layout as cl  # noqa: E402

ID = "eq.0h2v.s4.0123456789ab"


def write(root: Path, rel: str, text: str = "") -> None:
    p = root / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text, encoding="utf-8")


class Cones(unittest.TestCase):
    def run_in(self, files: dict[str, str]) -> list[str]:
        with tempfile.TemporaryDirectory() as d:
            for rel, text in files.items():
                write(Path(d), rel, text)
            return cl.check_cones(Path(d))

    def test_the_repository_itself_is_clean(self):
        self.assertEqual(cl.main([str(Path(__file__).resolve().parents[1])]), 0)

    def test_declared_and_existing_topics_agree(self):
        probs = self.run_in({"cones.toml": "[topic.A]\nparents=[]\n", "Tengai/B/X.lean": "import Init\n"})
        self.assertTrue(any("does not declare topic B" in p for p in probs))
        self.assertTrue(any("topic A is declared" in p for p in probs))

    def test_imports_follow_the_declared_parents(self):
        toml = "[topic.A]\nparents=[]\n[topic.B]\nparents=['A']\n"
        ok = {
            "cones.toml": toml,
            "Tengai/A/X.lean": "import Lean\n",
            "Tengai/B/Y.lean": "import Tengai.A.X\nimport Tengai.B.Z\n",
            "Tengai/B/Z.lean": "",
        }
        self.assertEqual(self.run_in(ok), [])
        bad = {**ok, "Tengai/A/X.lean": "import Tengai.B.Y\n"}
        self.assertTrue(any("topic A may import only" in p for p in self.run_in(bad)))

    def test_tengoku_is_never_imported(self):
        probs = self.run_in({"cones.toml": "[topic.A]\nparents=[]\n", "Tengai/A/X.lean": "import Tengoku.All\n"})
        self.assertTrue(any("never imported (I3)" in p for p in probs))

    def test_cycle_unknown_parent_and_budget(self):
        probs = self.run_in(
            {
                "cones.toml": "[topic.A]\nparents=['B']\n[topic.B]\nparents=['A','C']\nmax_modules=1\n",
                "Tengai/A/X.lean": "",
                "Tengai/B/X.lean": "",
                "Tengai/B/Y.lean": "",
            }
        )
        self.assertTrue(any("cycle" in p for p in probs))
        self.assertTrue(any("parent C" in p for p in probs))
        self.assertTrue(any("over its budget of 1" in p for p in probs))


class Records(unittest.TestCase):
    def test_data_records(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            write(root, "Tengai/A/X.lean")
            write(root, f"data/{ID}.json", json.dumps({"id": ID, "name": "A.t", "module": "Tengai.A.X"}))
            self.assertEqual(cl.check_data(root), [])
            write(root, "data/eq.0h2v.s4.ffffffffffff.json", json.dumps({"id": ID, "name": "A.t", "module": "Tengai.A.Missing"}))
            write(root, "data/bad.json", "{")
            probs = "\n".join(cl.check_data(root))
            self.assertIn("is not named by its id", probs)
            self.assertIn("is not a file", probs)
            self.assertIn("bad.json is not JSON", probs)

    def test_tawatur_routes(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            for f in ("route.json", "route-1.lean", "route-2.lean"):
                write(root, f"tawatur/{ID}/{f}")
            write(root, "Tengai.lean", "import Tengai.A.X\n")
            self.assertEqual(cl.check_tawatur(root), [])
            write(root, f"tawatur/{ID}/route-4.lean")
            write(root, "tawatur/notanid/route.json")
            probs = "\n".join(cl.check_tawatur(root))
            self.assertIn("at most three", probs)
            self.assertIn("not named by an isnad id", probs)
            write(root, "Tengai.lean", "import Tawatur.X\n")
            self.assertIn("default import cone", "\n".join(cl.check_tawatur(root)))


if __name__ == "__main__":
    unittest.main()

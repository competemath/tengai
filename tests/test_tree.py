from pathlib import Path

import pytest

from anomalous_archangel import tree

ROOT = Path(__file__).resolve().parent.parent


def test_the_real_tree_is_mapped():
    tm = tree.scan(ROOT)
    assert {"Tengai.Seed.Gauss", "Tengai.Seed.OddSum", "Tengai.Bridge.GaussOdd"} <= set(tm.modules)
    names = {d.name for m in tm.modules.values() for d in m.decls}
    assert {"Tengai.sum_range_mul_two", "Tengai.sum_range_odd", "Tengai.sum_range_odd_of_gauss"} <= names
    assert tm.tengai_imports("Tengai.Bridge.GaussOdd") == ["Tengai.Seed.Gauss", "Tengai.Seed.OddSum"]
    assert tm.order().index("Tengai.Seed.Gauss") < tm.order().index("Tengai.Bridge.GaussOdd")
    assert tm.closure("Tengai.Seed.Gauss") == ["Tengai.Seed.Gauss"]


def test_the_root_file_lists_every_module():
    """Tengai.lean is generated; this fails when a module is added without regenerating it (python -m anomalous_archangel root)."""
    assert (ROOT / "Tengai.lean").read_text() == tree.root_file(tree.scan(ROOT))


def test_namespaces_sections_and_private_names():
    m = tree.parse_module(
        "Tengai.X",
        "Tengai/X.lean",
        "import Tengoku.All\nnamespace Tengai\nsection S\n/-- doc here -/\ntheorem t : True := trivial\nend S\nprivate def hidden := 1\ntheorem _root_.Nat.mine : True := trivial\nend Tengai\ntheorem outside : True := trivial\n",
    )
    assert [(d.kind, d.name) for d in m.decls] == [
        ("theorem", "Tengai.t"),
        ("def", "Tengai.hidden"),
        ("theorem", "Nat.mine"),
        ("theorem", "outside"),
    ]
    assert m.decls[0].doc == "doc here"


def test_cycles_are_found(tmp_path):
    (tmp_path / "Tengai").mkdir()
    (tmp_path / "Tengai" / "A.lean").write_text("import Tengai.B\n")
    (tmp_path / "Tengai" / "B.lean").write_text("import Tengai.A\n")
    with pytest.raises(ValueError):
        tree.scan(tmp_path).order()


def test_the_digest_is_bounded():
    assert len(tree.scan(ROOT).digest(max_chars=300)) <= 300

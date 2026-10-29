import subprocess

from anomalous_archangel import tengoku_view
from anomalous_archangel.memory import Memory
from anomalous_archangel.requests import Queue


def test_memory_notices_repeats_and_rotates_lenses(tmp_path):
    m = Memory()
    f = {
        "kind": "note",
        "title": "Gauss sum in any commutative ring",
        "body": "induction removes truncated subtraction from the natural number statement",
    }
    assert not m.is_repeat(f["title"], f["body"])
    m.remember("d1", "abstractor", f)
    assert m.is_repeat("Gauss sum in any commutative ring", "induction removes the truncated subtraction of the natural number statement")
    assert not m.is_repeat("Dimension lifting of the odd sum", "squares as sums along an n dimensional grid")
    m.ran("d1", "abstractor")
    m.ran("d2", "bridger")
    assert m.staleness("abstractor") == 1 and m.staleness("bridger") == 0 and m.staleness("never") > 100
    m.save(tmp_path / "m.json")
    assert Memory.load(tmp_path / "m.json").findings == m.findings
    assert "Gauss sum" in m.digest()
    assert Memory.load(tmp_path / "missing.json").findings == []


def test_the_request_queue_lifecycle(tmp_path):
    q = Queue()
    item, new = q.add("∀ n : ℕ,  n = n", "i", "w", "d1", "experimenter", "t")
    again, new2 = q.add("∀ n : ℕ, n = n", "i", "w", "d2", "bridger", "t")
    assert new and not new2 and again["id"] == item["id"]  # whitespace does not make a new request
    unchecked, _ = q.add("∀ n : ℕ, n + 0 = n", "i", "w", "d1", "x", "t", checked=False)
    assert unchecked["status"] == "unchecked" and len(q.open_items()) == 1
    q.claim(item["id"], "leak-archangel")
    assert q.open_items() == []
    try:
        q.claim(item["id"], "someone")
        raise AssertionError("a claimed request cannot be claimed again")
    except ValueError:
        pass
    q.fulfil(item["id"], "Tengai/Proved/R.lean")
    q.save(tmp_path / "r.json")
    assert Queue.load(tmp_path / "r.json").get(item["id"])["status"] == "proved"


def git(repo, *a):
    subprocess.run(["git", "-C", str(repo), "-c", "user.name=t", "-c", "user.email=t@t", *a], check=True, capture_output=True)


def test_arrivals_from_a_tengoku_checkout(tmp_path):
    git(tmp_path, "init", "-q", "-b", "main")
    (tmp_path / "data/staging/lib").mkdir(parents=True)
    (tmp_path / "data/staging/lib/a.jsonl").write_text("{}\n")
    git(tmp_path, "add", "-A")
    git(tmp_path, "commit", "-q", "-m", "content: banked by leak")
    (tmp_path / "x.py").write_text("print(1)\n")
    git(tmp_path, "add", "-A")
    git(tmp_path, "commit", "-q", "-m", "tooling: a script")
    rows = tengoku_view.arrivals(tmp_path)
    assert [r["subject"] for r in rows] == ["tooling: a script", "content: banked by leak"]
    assert [r["leak"] for r in rows] == [False, True]
    assert "[leak]" in tengoku_view.digest(rows)
    assert tengoku_view.arrivals(tmp_path / "nope") == [] and "none read" in tengoku_view.digest([])

import random

import pytest

from anomalous_archangel.budget import Ledger, Limits, Refused


def test_children_never_hold_more_than_the_parent_has():
    for seed in range(200):
        rng = random.Random(seed)
        total = rng.uniform(0.5, 50)
        lg = Ledger(total, Limits(max_depth=2, max_breadth=3, max_waves=2))
        frontier = ["0"]
        while frontier:
            nid = frontier.pop()
            for _ in range(rng.randint(0, 2)):
                try:
                    kids = lg.spawn_wave(
                        nid,
                        ["x"] * rng.randint(1, 5),
                        [rng.random() + 0.01 for _ in range(5)][: rng.randint(1, 5)] or None,
                        rng.uniform(0.1, 1.0),
                    )
                except (Refused, ValueError):
                    continue
                lg.check()
                assert len(kids) <= 3
                for k in kids:
                    lg.charge(k.id, rng.uniform(0, k.allot_usd * 1.2))
                    frontier.append(k.id)
        for n in sorted(lg.nodes.values(), key=lambda n: -n.depth):
            if n.id != "0" and n.status in ("pending", "running"):
                lg.finish(n.id)
        lg.check()
        assert max(n.depth for n in lg.nodes.values()) <= 2
        # what the whole tree spent is bounded by the budget plus at most the overshoot of the individual calls
        assert lg.spent_total() <= total * 1.2 + 1e-6


def test_depth_breadth_and_waves():
    lg = Ledger(10, Limits(max_depth=2, max_breadth=3, max_waves=1))
    a = lg.spawn_wave("0", ["a", "b", "c", "d", "e"])
    assert [n.lens for n in a] == ["a", "b", "c"]
    assert [r["lens"] for r in lg.refused] == ["d", "e"]
    with pytest.raises(Refused):
        lg.spawn_wave("0", ["f"])  # its one wave is spent
    (h,) = lg.spawn_wave(a[0].id, ["h"])
    assert h.depth == 2
    with pytest.raises(Refused):
        lg.spawn_wave(h.id, ["too deep"])
    assert {"parent": h.id, "lens": "too deep", "why": "depth"} in lg.refused


def test_unspent_money_returns_to_the_parent():
    lg = Ledger(10, Limits())
    (k,) = lg.spawn_wave("0", ["a"], fraction=0.5)
    assert k.allot_usd == 5 and lg.root.available == 5
    lg.charge(k.id, 1.5)
    lg.finish(k.id)
    assert lg.root.available == 10 - 1.5 and lg.root.spent_usd == 1.5
    lg.check()


def test_bad_arguments():
    lg = Ledger(1)
    with pytest.raises(ValueError):
        lg.spawn_wave("0", ["a"], weights=[0.0])
    with pytest.raises(ValueError):
        lg.spawn_wave("0", ["a"], fraction=0)
    with pytest.raises(ValueError):
        Ledger(-1)

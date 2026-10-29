"""Spawn control with a conserved budget.

The archangel is depth 0, its angels depth 1, an angel's helpers depth 2. A node may spawn at most `max_breadth` children in one wave and
`max_waves` waves, and never below `max_depth`. A child's allowance is reserved out of its parent's remaining money before it starts, so
the allowances of a node's children never add up to more than the parent had left (the invariant `check()` verifies, and the tests
hammer with random spawn trees), and when a child finishes what it did not spend returns to the parent. Nothing here spawns a process: it is
the ledger the drip consults before it launches anything.
"""

from __future__ import annotations

from dataclasses import dataclass, field

EPS = 1e-9


@dataclass(frozen=True)
class Limits:
    max_depth: int = 2
    max_breadth: int = 3
    max_waves: int = 2


@dataclass
class Node:
    id: str
    parent: str | None
    depth: int
    lens: str
    allot_usd: float
    spent_usd: float = 0.0
    reserved_usd: float = 0.0  # handed to children that are still running
    status: str = "pending"  # pending | running | done | failed | refused
    waves: int = 0
    children: list[str] = field(default_factory=list)

    @property
    def available(self) -> float:
        return self.allot_usd - self.spent_usd - self.reserved_usd


class Refused(Exception):
    """A spawn the limits do not allow."""


class Ledger:
    def __init__(self, total_usd: float, limits: Limits | None = None, lens: str = "archangel") -> None:
        if total_usd < 0:
            raise ValueError("the budget cannot be negative")
        self.limits = limits or Limits()
        self.nodes: dict[str, Node] = {"0": Node("0", None, 0, lens, float(total_usd), status="running")}
        self.refused: list[dict] = []
        self._seq = 0

    @property
    def root(self) -> Node:
        return self.nodes["0"]

    def _new_id(self) -> str:
        self._seq += 1
        return str(self._seq)

    def spawn_wave(self, parent_id: str, lenses: list[str], weights: list[float] | None = None, fraction: float = 1.0) -> list[Node]:
        """Reserve a wave of children. Children beyond the breadth limit are refused (and recorded); a parent that is too deep or has had its
        waves raises Refused. The wave's money is split by `weights` out of what the parent has available now."""
        parent = self.nodes[parent_id]
        if parent.depth + 1 > self.limits.max_depth:
            self._refuse(parent, lenses, "depth")
            raise Refused(f"depth {parent.depth + 1} is beyond the limit {self.limits.max_depth}")
        if parent.waves >= self.limits.max_waves:
            self._refuse(parent, lenses, "waves")
            raise Refused(f"{parent.id} has had its {self.limits.max_waves} waves")
        if len(lenses) > self.limits.max_breadth:
            self._refuse(parent, lenses[self.limits.max_breadth :], "breadth")
            lenses = lenses[: self.limits.max_breadth]
            weights = weights[: self.limits.max_breadth] if weights else None
        if not lenses:
            return []
        w = list(weights) if weights else [1.0] * len(lenses)
        if len(w) != len(lenses) or any(x < 0 for x in w) or sum(w) <= 0:
            raise ValueError("weights must be non-negative, as many as lenses, and not all zero")
        if not 0.0 < fraction <= 1.0:
            raise ValueError("fraction must be in (0, 1]")
        pot = max(parent.available, 0.0) * fraction
        parent.waves += 1
        out = []
        for lens, x in zip(lenses, w, strict=True):
            share = pot * x / sum(w)
            node = Node(self._new_id(), parent.id, parent.depth + 1, lens, share)
            parent.reserved_usd += share
            parent.children.append(node.id)
            self.nodes[node.id] = node
            out.append(node)
        return out

    def _refuse(self, parent: Node, lenses: list[str], why: str) -> None:
        for lens in lenses:
            self.refused.append({"parent": parent.id, "lens": lens, "why": why})

    def charge(self, node_id: str, usd: float) -> float:
        """Record spending; a node cannot spend past its allowance (the overshoot is clipped and returned as 0 left)."""
        n = self.nodes[node_id]
        n.spent_usd += max(float(usd), 0.0)
        return max(n.allot_usd - n.spent_usd, 0.0)

    def finish(self, node_id: str, status: str = "done") -> None:
        """A child is over: the unspent part of its allowance goes back to the parent, and what it spent is the parent's spending."""
        n = self.nodes[node_id]
        n.status = status
        if n.parent is None:
            return
        p = self.nodes[n.parent]
        p.reserved_usd -= n.allot_usd
        # a child that overspent (a runner that cannot stop mid-call) is paid for by its parent's allowance, never hidden
        p.spent_usd += n.spent_usd

    def spent_total(self) -> float:
        """Everything spent below the root plus what the root spent itself."""
        return self.root.spent_usd

    def check(self) -> None:
        """The invariants: children's allowances fit in the parent's, depth and breadth hold, nothing is negative."""
        for n in self.nodes.values():
            if n.depth > self.limits.max_depth:
                raise AssertionError(f"{n.id} is too deep")
            live = [self.nodes[c] for c in n.children if self.nodes[c].status in ("pending", "running")]
            if sum(c.allot_usd for c in live) > max(n.allot_usd - n.spent_usd, 0.0) + EPS:
                raise AssertionError(f"the live children of {n.id} hold more than it has left")
            if abs(sum(c.allot_usd for c in live) - n.reserved_usd) > 1e-6:
                raise AssertionError(f"{n.id} reserved {n.reserved_usd}, its live children hold {sum(c.allot_usd for c in live)}")
            if n.reserved_usd < -EPS or n.spent_usd < -EPS:
                raise AssertionError(f"{n.id} has a negative balance")

    def as_records(self) -> list[dict]:
        return [
            {
                "id": n.id,
                "parent": n.parent,
                "depth": n.depth,
                "lens": n.lens,
                "allot_usd": round(n.allot_usd, 4),
                "spent_usd": round(n.spent_usd, 4),
                "status": n.status,
            }
            for n in self.nodes.values()
        ]

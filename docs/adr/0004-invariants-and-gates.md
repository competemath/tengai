# ADR-0004: invariants and readiness gates

- Status: accepted (2026-11-16)

## Invariants

I1 untrusted search, trusted checking (ADR-0003). I2 one canonical form, idempotent: `canon(canon(x)) = canon(x)`, enforced in CI, every convention a machine-readable entry with its rationale and tie-breaker (most intuitive and scalable; on a tie, least hidden background search). I3 tengai never imports Tengoku. I4 visible, not active: everything is searchable through indexes, only `scoped`/`local` attributes in small topic modules activate simp lemmas, instances, notation. I5 no upstream unfolding: exported definitions are `irreducible` with API lemmas; lint bans `unseal`, `unfold`, `delta` on foreign constants. I6 tenro contains tengai exactly: `tenro/core/` is byte-identical to a tengai tag (tree-hash check, identical `lean-toolchain`) or that tag plus named registered hypothesis patches; a daily `git am` dry run on every live hypothesis. I7 hypotheses are pre-registered with metric, expected effect and sample size. I8 harvest from non-evaluation intake runs only.

## Readiness gates (before any Mathlib A/B)

1. Soundness and hygiene: 100% on the axiom and vacuity locks, `data/` lemma-to-definition ratio <= 4:1, 0% structural duplicates, cold `import Tengai` <= `C_load` seconds on the pinned runner image and per-module latency growth <= `b` ms (both measured at P1 in `perf-budget.toml`, only ever lowered).
2. Discoverability: blind-signature Recall@10 >= 85% on held-out goals with target names stripped; the pass-rate drop under identifier scrambling of **both** library and problem < 5%.
3. Migration: >= 98% automatic bidirectional lens migration on the real-migration corpus, 100% isnad round-trip.
4. Anti-tampering: 0% undetected statement/definition tampering (frozen file prefix, external `#print axioms`), harness infrastructure error < 1%, 100% two-sided validity.
5. Stratified evaluation at identical model weights, turn caps and sample budgets, with the power analysis and non-inferiority margins fixed in `eval/protocol.md` (hashed, registered) before any campaign.

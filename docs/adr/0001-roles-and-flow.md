# ADR-0001: roles, flow, visibility

- Status: accepted (2026-11-16)
- Deciders: the owner

## Context

Three repositories were planned around Tengoku: a clean AI-first core (`tengai`), a high-churn furnace (`tenro`) and the guarded source (`tengoku`). `tengai` already existed with an open pull request (#1) that described it as the *volatile* upstream of Tengoku, with the drip (`anomalous-archangel`) and its gate. That is the furnace's role.

## Decision

1. `tengai` is the clean, canonical, performance-first Lean 4 core consumed by ATP harnesses. `tenro` is the furnace. `tengoku` stays the frozen, guarded source of record.
2. The content of `tengai#1` is the seed of `tenro` (history kept: `competemath/tenro` `main` starts at that branch's head `f86c22c3`). `tengai#1` is closed.
3. Content moves one way only: `tengoku -> tenro -> tengai`. Tengoku receives nothing from tenro or tengai. `tengai` never imports Tengoku.
4. `tengai` and `tenro` are public: standard hosted runners are free and unlimited for public repositories, which heavy Lean builds need. The held-out evaluation suite lives in a separate minimal private repository, `competemath/tenro-eval`, created at P5, pulled by deploy key during promotion gates; held-out problem text is masked in CI logs.

## Consequences

- A promoted theorem is re-proved inside tengai's own cone, so it never shares an isnad id with its Tengoku source when canonicalisation changed the statement; it carries `source_id` and an equivalence proof (the promotion lens). See ADR-0003.
- tenro must contain tengai exactly (invariant I6 of `docs/design.md`), so that promotion is a patch that applies cleanly.
- No secret is shared between the repositories. tenro's drip workflow needs its own token and skips cleanly without one.

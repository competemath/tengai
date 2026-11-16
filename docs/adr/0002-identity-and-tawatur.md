# ADR-0002: statement identity, `data/`, and `tawatur`

- Status: accepted (2026-11-16)

## Context

Tengoku's isnad v1 names a statement by the hash of its canonical elaborated form (`id`), plus name-blind `shape` and `vocab` hashes. Tengoku's `docs/tawatur.md` proposes *tawatur* as a status for a statement with several independent proofs. The brief for tengai asks for a folder of alternate routes called `tawatur/`.

## Decision

1. A **statement** is an isnad `id`. `data/` holds exactly one proof per id (0% structural duplicates in `data/`).
2. `tawatur/<id>/` holds at most three further routes to a statement already in `data/`. It is the **input**; the *status* tawatur (>= 3 pairwise independent routes) is **computed** from it. One definition, in `docs/tawatur.md`.
3. Routes are not imported by `Tengai.All` (no cost in the default import cone) but are built and gated in CI.
4. A route is admitted only if its structural divergence from every stored route is above calibrated thresholds on **both** axes: the dependency footprint of the *reduced* proof term (unused `have`/`let_fun` eliminated, so padding changes nothing; minus the forced layer X) and the set of isnad ids of its `have` statements. Raw edit distance and length are never used. Thresholds are calibrated on the 69 labelled groups (51 aliases must fail, 7 independent must pass), not chosen.
5. Eviction keeps the triple that maximises the minimum pairwise divergence, then compactness.
6. A generalised theorem (hypotheses dropped) is deduplicated before insertion: its isnad `shape` is a prefilter over `data/` and a hit is **confirmed by the full `id`**. A confirmed match is not inserted; the specialisation is an index edge.

## Consequences

- The closure extractor (P1) is a prerequisite: it computes footprints and unblocks Tengoku's tawatur reference test.
- `shape` is 8 hex characters and may collide: it never decides alone.

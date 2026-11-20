# ADR-0005: content enters tengai by kernel replay of an export

Status: proposed 2026-11-20 (the first transplant, with measurements, decides whether it is adopted).

## Context
Tengai builds on Lean core alone (I3), loads under an absolute cap (C_load) and must hold a strong amount of Tengoku. Measured on 330 Tengoku theorems (tenro `tools/promote/sizing.py`): none is
closed over Lean core; a theorem needs a median of about 12,500 constants outside it, 10 theorems need 35,000 distinct constants together, 100 need 78,500 and 330 need 87,600 (5.0M if nothing were shared).
Content is therefore one shared foundation of about 80,000 constants plus about 40 new constants a theorem. A proof written against Mathlib cannot be re-proved on Lean core by source copying.

## Decision
A promotion is a **kernel replay** of a `lean4export` file (format 3.x), done by `tengai-replay`: every declaration goes through `addDecl`, so a wrong term is refused whatever produced it (I1); what Lean core already
holds must have the same type and is not added again; the result is a built `.olean` (`TengaiData.<Topic>`), which a prover imports with the snapshot on `LEAN_PATH`. The release is the `.olean` snapshot
(`docs/design.md`). The replay tool imports `Lean`; no library module imports it and the modules it writes do not, so the import stays as small as the content. Nothing is registered (no simp set, no instance,
no attribute): a replayed module is searchable, and active only through the scoped layer of a topic (I4).

## Consequences
- The source of a promoted theorem is its export (hashed, in `data/`), not a Lean file; readable statements come from the statement text carried by Tengoku's record and are checked against the replayed constant by isnad id (the promotion lens, ADR-0003).
- A replayed constant has no compiled code (no IR): it can be checked, applied and rewritten with, not evaluated. That is all a prover needs; anything that must run is written in Tengai itself.
- An independent checker re-checks the `.olean` snapshot (I1), as Tengoku's nightly does.
- Whether the foundation fits C_load is measured next on a built module; if it does not, the foundation is trimmed (fewer, higher-leverage theorems), never the cap.

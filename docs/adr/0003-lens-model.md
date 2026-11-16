# ADR-0003: versions are lenses; migrations are checked, not trusted

- Status: accepted (2026-11-16)

## Decision

1. **Untrusted search, trusted checking.** Agents, repair tools and lens search may be wrong. A migrated theorem is accepted only if the kernel checks it, the independent check agrees, the axiom/vacuity locks pass, and the isnad round trip holds. The trusted base never includes migration or repair code.
2. **One model.** A change between two versions is an isomorphism up to a complement, `D_old ~ D_new x R`. `R` is trivial for a one-to-one change and is the stored residual complement for a split, so lifting back loses nothing.
3. **Acceptance.** For a theorem `t` migrated to `t'`, the lens maps `id(t')` back to a statement whose id equals `id(t)`. Any mismatch rejects the migration (no silent weakening).
4. **Composition.** Lenses compose along a commit range; checkpoint skip-lenses are stored so a long migration costs O(log n) compositions.
5. **isnad extension.** Add `deps`: the hash of the sorted set of statement ids of direct dependencies (proof-irrelevant: rewriting a dependency's proof does not change it). `shape` and `vocab` remain the name-blind semantic hashes.
6. **Promotion lens.** Promotion from tenro to tengai is a lens too (`source_id` plus an equivalence proof).

## Consequences

- A corpus of real migrations (Tengoku's reseeds) is the first deliverable of P4; the 98% target is reported with its denominator.
- Convention changes are versioned events that generate a lens; they are never swept silently.

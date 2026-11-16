# tengai / tenro: architecture and phased plan

Status: **adopted 2026-11-16** (the four rulings of section 2 and the five fixes of section 7 are approved). This is the single design document of tengai; decisions are recorded one by one in `docs/adr/`. Where the two differ, the ADR wins and this file is corrected.

## 1. What existed when the design was made (read 2026-11-16, before the rulings)

| Thing | State |
|---|---|
| `competemath/tengai` | exists since 2026-10-29: LICENSE + a five-line README on `main`. **Open PR #1 `feat/tengai-v0`** (3,255 lines, 43 files, unmerged): a Lean project built against a pinned Tengoku commit (`tengoku.pin`, `scripts/tengoku-setup.sh`), `anomalous-archangel` (a "drip" of agent lenses, a gate of lint + Leak IV + `lake build` with warnings as errors + `#print axioms`), 65 tests. Its own README and `docs/flows.md` say: **Tengai is the volatile upstream**; settled content flows *to* Tengoku. |
| `competemath/tenro` | did not exist; created on 2026-11-16 from the history of `tengai#1`. |
| isnad (tengoku `docs/isnad.md`, `TengokuIsnad.lean`, `scripts/isnad*.py`) | built and merged (v1): statement identity `id` = sha256 of the canonical elaborated statement (de Bruijn vars, constants by cleaned name, proof terms erased), plus `shape` (name-blind) and `vocab` hashes; tagger; tags live in docstrings. **Not built:** dependency-set hash, runtime layer, tawatur. |
| tawatur (tengoku `docs/tawatur.md`, `scripts/tawatur.py`) | a *proposal*: a status for a statement with >= 3-4 proofs whose closures are pairwise disjoint after a set X is ignored. Reference test exists; **no closure extractor exists**; calibration data exists (2026-10-04: 69 duplicate-statement groups = 51 alias / 11 similar / 7 independent). |
| axiom / vacuity / independent checks | built: axiom check per new declaration, `scripts/ci/vacuity.py` + `tools/vacuity/vacuity.lean`, nightly `independent-check.yml` (nanoda re-checks every declaration), `jinshi`, `warrant`. Not built: hypothesis-dropping, counterexample probes, native_decide ban beyond the axiom list. |
| migration support (tengoku `docs/migration-support.md`) | a proposal: `data/migrations/` records computed from git; no lens. A private `tengoku-adapters` repo transfers theorems across toolchain versions. |
| retrieval | Leak I (Loogle + Moogle + Chroma). `shape` from isnad is already a name-blind pattern key. |
| promotion machinery | `scripts/promote.py` (staging to trusted, builds each candidate), the factory (`emissary-archangel`), the queue gates. |

## 2. Rulings (2026-11-16)

The brief and the repositories disagreed on four points. Each is now settled; the reasoning is in ADR-0001 and ADR-0002.

1. **Roles.** `tengai` is the clean, canonical, performance-first core. `tenro` is the furnace. The content of the old open PR `competemath/tengai#1` (the drip, its gate, the pinned-Tengoku Lean seed) became the seed of `tenro` (history kept); that PR was closed.
2. **Flow.** Strictly one way: `tengoku -> tenro -> tengai`. Tengoku never receives from either; tengai never imports Tengoku.
3. **Visibility.** `tenro` and `tengai` are public (unlimited standard runner minutes for heavy Lean builds). The held-out evaluation suite lives in a separate minimal **private** repository, `competemath/tenro-eval`, pulled by deploy key during promotion gates, with held-out problem text masked from CI logs. It is created at P5, not before.
4. **`tawatur`.** The folder `tawatur/` is the input (alternate routes); the *status* tawatur (>= 3 pairwise independent routes, `docs/tawatur.md` of Tengoku) is computed from it. One definition.

A consequence of ruling 1 that is easy to miss: canonicalising a statement changes its isnad id, so a promoted theorem is never "the same id" as its Tengoku source. Every promoted theorem therefore records `source_id` and a proof that the two statements are equivalent (`Iff.rfl`, `simp`, or a lemma): the **promotion lens**. Without it canonicalisation would be silent statement drift.

## 3. Invariants (what the machinery must make impossible, not just discouraged)

- **I1 Untrusted search, trusted checking.** Agents, repair tools and lens search may be wrong. Acceptance is only: kernel check + independent check + isnad round trip + axiom/vacuity locks. The trusted base never includes the migration or repair code.
- **I2 One canonical form, idempotent.** `canon(canon(x)) = canon(x)`, enforced in CI. A convention is a machine-readable entry (`conventions.toml`) with its rationale and tie-breaker; changing one is a versioned event that *generates* a lens, never a silent sweep.
- **I3 tengai never imports tengoku.** Promoted content is re-proved inside tengai's own cone; provenance and credit travel in tags and records. tengai builds with no dependency except Lean core (and the minimal seed it carries).
- **I4 Visible but not active.** Everything is searchable through indexes; only `scoped` / `local` attributes inside small topic modules activate simp lemmas, instances, notation. Lint bans global ones.
- **I5 No upstream unfolding.** Definitions exported across a module boundary are `irreducible` with API lemmas (`def_eq`, `unfold_iff`); lint bans `unseal`, `unfold`, `delta` on foreign constants. This makes internal rewrites non-breaking and keeps defeq search shallow.
- **I6 tenro contains tengai exactly.** `tenro/core/` is byte-identical to a tengai tag (tree-hash check) *or* that tag plus named, registered hypothesis patches. Promotion = replaying a patch on tengai main with `git am`; CI runs this as a daily dry run on every live hypothesis. Overlays (intake, harvest) never edit `core/`.
- **I7 Pre-registration.** A hypothesis states its metric, expected effect and sample size before any run. Promotion needs a net Pareto improvement with confidence intervals, not a point estimate.
- **I8 No contamination.** Harvested partial subgoals carry the problem and run they came from; anything from a held-out problem is quarantined and never enters the library, the indexes or the prover's context.

## 4. Architecture

```
tengoku (frozen source, guarded)            tenro (private furnace)                 tengai (clean core)
  data/, cache, isnad tags  --pin-->   core/    = exact tengai tag (+ hyp patches) ---promote--> Tengai/
                                       intake/  = pinned tengoku cache (not copied)              data/  one record per statement id
                                       harvest/ = kernel-checked partial subgoals                tawatur/ <=3 routes per id
                                       hyp/<id> = branch + manifest.json                         lenses/  v_old <-> v_new
                                       eval/    = harness specs, scramblers (runs are yours)     indexes/ intent, shape, dep graph
                                                                                                 release: .olean snapshot + manifest
```

### tengai layout
- `Tengai/<Topic>/...`: small walled cones; a module imports only its declared parents (budgeted in `cones.toml`).
- `data/<id>.json`: exactly one proof per statement id (id = isnad). The Lean module is the source of truth; `data/` is derived and diffed in CI.
- `tawatur/<id>/route-{1,2,3}.lean` + `route.json`. **Not imported by `Tengai.All`** (zero cost in the default import cone) but built and gated in CI.
- `lenses/<from>-<to>/`: Lean lens definitions with proven round-trip laws + residual-complement types + a JSON map; composed chains and cached skip-lenses (checkpoints every N versions so a long migration is O(log n) compositions).
- `indexes/`: (a) intent (text), (b) name-blind pattern shape (isnad `shape`), (c) static dependency graph by statement id. Release assets, not git.
- Release = `.olean` snapshot + the three indexes + manifest with hashes, attested like tengoku's nightly cache.

### tawatur admission (structural, not textual)
- Footprint F(p) = constants reached by the *reduced* proof term (unused `have`/`let_fun` eliminated first, so padding cannot change F) minus the forced layer X of `docs/tawatur.md`.
- Waypoints W(p) = set of isnad ids of the `have` statements of p (canonical, so reordering algebra does not count).
- Divergence d(p,q) requires **both** 1 - J(F_p,F_q) >= a and 1 - J(W_p,W_q) >= b. Thresholds a, b are calibrated on the 69 labelled groups (51 alias must fail, 7 independent must pass), not guessed.
- Cap 3. A newcomer replaces a route only if the best triple of the four (maximising the minimum pairwise divergence, then compactness) contains it.

### lens model (one model for everything)
A version change is an **isomorphism up to a complement**: `D_old ≃ D_new x R`. R is trivial for 1-to-1 changes and is the residual for splits; it is stored with the lens, so lifting back loses nothing. Statement-level transport is a Lean meta program that emits a term the kernel checks; proof bodies are re-elaborated or repaired by untrusted search (I1). Acceptance of a migrated theorem t to t': the lens maps id(t') back to a statement whose id equals id(t). Any mismatch rejects (this is the brief's isnad check, made precise).
- isnad extension: add `deps` = hash of the *sorted set of statement ids* of direct dependencies (proof-irrelevant: rewriting a dependency's proof does not change it) and keep `shape`/`vocab` as the name-blind semantic hashes.

### tenro
Lake workspace: package `tengai` (path = `core/`, mirror-hash enforced), package `tengoku` (pinned dependency, compiled cache), package `harvest`. Hypotheses are branches with `manifest.json` (change, metric, expected effect, sample size, mirror hash). Every benchmark record keys on (core tree hash, hypothesis hash, harness hash, model, seeds), so results are reproducible and comparable across hypotheses.

## 5. Mapping the brief's requirements to work

| Requirement | Reuse | New |
|---|---|---|
| single canonical convention | isnad canonical form, bundle-lint | `conventions.toml`, `tengai-canon` normaliser, idempotence test, ADRs for each choice |
| axiom/vacuity locks | axiom check, `vacuity.py`, nanoda independent check, jinshi | hypothesis-dropping probe, counterexample probe (small `decide`/`simp` to False), `Lean.ofReduceBool` ban, clean-rebuild gate |
| performance first | warning-as-error builds, Lake cache | per-module elaboration profile, import-latency benchmark, synthesis-step budget (low default heartbeats), cone-size budget, all as regression gates |
| data/ vs tawatur/ | `scripts/tawatur.py`, isnad id | closure extractor (also unblocks `docs/tawatur.md`), reduced-term closure, divergence metric, calibration |
| bidirectional lenses | tengoku-adapters, migration-support proposal | lens framework, residual types, composition + checkpoints, migration corpus from real bumps, round-trip harness |
| isnad meaning check | isnad v1 | `deps` hash, round-trip comparator |
| tenro | PR #1 drip + gate, tengoku cache | mirror invariant, overlay layout, hypothesis registry, harvest schema + quarantine |
| eval | Leak services | held-out protocol, identifier scrambler (library *and* problems), stats plan, harness specs |

## 6. Phases (each with exit criteria that need no prover run)

- **P0 Decisions and skeletons.** Resolve section 8. ADR-0001 roles/flow, ADR-0002 identity and `tawatur`, ADR-0003 lens model, ADR-0004 conventions process. Create/repurpose the repos. Exit: ADRs merged; repos build an empty cone in CI.
- **P1 Measure first.** Closure extractor; performance profiler and gates; isnad `deps`; name-blind index builder; wrapper around the existing soundness checks. Exit: each produces numbers on a 1,000-theorem slice of Tengoku, reproducibly, in CI.
- **P2 tengai v0.1 + tenro bootstrap.** Conventions v1 and the normaliser; first topic cones; `data/` one-per-statement; mirror invariant and the daily promotion dry run in tenro; harvest schema with quarantine. Exit: a theorem travels tengoku to tenro to tengai through the gate with a promotion lens, and the dry run applies cleanly.
- **P3 tawatur tier.** Calibrated divergence; admission and eviction; status computed. Exit: the 51/7 calibration passes; padding attack test fails to admit.
- **P4 Lenses.** Migration corpus from tengoku's real reseeds; lens framework; round-trip harness. Exit: a measured auto-migration rate on the corpus (target 98%, reported with its denominator), 100% isnad round-trip.
- **P5 Evaluation harness.** Held-out protocol, scrambler, stats plan, harness specs, anti-tampering (frozen prefix, external `#print axioms`). Exit: dry runs on fake agents; **real campaigns are yours** (I do not run provers or FATE-X).
- **P6 Readiness gates.** Automate the five gates as one report; no A/B against Mathlib until all pass.

## 7. Fixes to the brief (approved) and remaining risks

Approved fixes:
1. **Load latency is an absolute cap, not a ratio to Mathlib.** A ratio is passed trivially while tengai is small. Gate 1 becomes: cold `import Tengai` <= `C_load` seconds on the pinned reference runner image, **and** a per-module scaling budget (import latency may grow by at most `b` ms per added module). `C_load` and `b` are measured at P1, written into `perf-budget.toml`, and may only be lowered. Mathlib is reported alongside as context, not as the gate.
2. **Name-obfuscation scrambles both sides.** The library's identifiers and the problem's identifiers are scrambled by one consistent map, so the test measures retrieval by structure rather than by recalled names.
3. **Generalised theorems are deduplicated before insertion.** Hypothesis dropping produces a candidate; the candidate's isnad `shape` is used as a cheap prefilter over `data/`, and a shape hit is **confirmed by the full isnad id** (the `shape` is 8 hex characters and can collide; it must not decide alone). A confirmed match is not inserted; the specialisation is recorded as an index edge to the general theorem.
4. **Harvesting is restricted to non-evaluation intake runs.** A partial subgoal is admitted to `harvest/` only if its run's problem id is not in any held-out split. The check runs at harvest time and again at promotion time, against the list in `tenro-eval` (ids only, no text).
5. **The power analysis and non-inferiority margins are fixed before any campaign.** `eval/protocol.md` (P5) states, per metric, the minimum detectable effect, the sample size that gives it at the chosen power, and the margin for each metric that must not regress. It is merged and hashed first; the promotion tool refuses a result whose protocol hash is not the registered one.

Remaining risks (unchanged by the approval, to be watched):
- Compression (<= 4 lemmas per definition), generality and speed can pull apart; the Pareto rule names its margins in advance (fix 5).
- Selection of the "highest-leverage" proof needs a measure: dependency-graph centrality from the static graph plus prover usage logs, with a per-topic budget.
- A convention flip is a lens over the whole library: freeze conventions per major version; a flip is a release with a generated lens and a full round-trip run.
- tenro's "perfect copy" fails silently if an overlay edits `core/` or a toolchain differs: invariant I6 plus an identical `lean-toolchain` check.
- Tengoku is ~331k theorems and a 3 GB checkout: nothing here needs a clone; tenro uses the pinned cache, selection and indexes read Tengoku's published data and tags.

## 8. Open items

- `competemath/tenro-eval` (private) is created at P5 with its deploy key; until then no held-out material exists anywhere.
- Rulesets (no deletion, no force-push on `main`) for `tengai` and `tenro` are a repository setting: requested of the owner, not applied by the tooling.
- Calibration thresholds for tawatur admission (P3) and `C_load`, `b` (P1) are measured values, not chosen ones.

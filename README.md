# Tengai

The clean core: a small, canonical, performance-first Lean 4 library for AI theorem provers, distilled from
[Tengoku](https://github.com/competemath/tengoku) through [Tenro](https://github.com/competemath/tenro).

- **One canonical form.** Every statement has exactly one representation; where two are equally intuitive, the one that
  minimises hidden search wins.
- **Fast by construction.** Small walled dependency cones, no global automation, a measured import-latency budget.
- **Sound by construction.** Nothing lands that depends on `sorryAx`, an unapproved axiom or `native_decide`; vacuity and
  hypothesis-dropping probes run on every candidate.
- **One proof per statement** in `data/`, up to three structurally different alternates in `tawatur/`.
- **Migrations are lenses**, checked by the kernel and by an isnad round trip, not trusted.

Content flows one way, `tengoku -> tenro -> tengai`: Tengai never imports Tengoku, and Tengoku receives nothing from it.
Everything arrives as a promotion from Tenro, through the same gates.

**Status: experimental (0.x; no v1 before the owner's explicit approval, [docs/release-barrier.md](docs/release-barrier.md)).** Start with
[docs/design.md](docs/design.md) and the decisions in [docs/adr/](docs/adr/).

Built, and checked in CI on every change:

- **`tengai-replay`**: content from a Tengoku export becomes a built `.olean` by kernel replay (every declaration goes through `addDecl`, so a wrong proof is refused whatever produced it), in layers
  (`--import`, `--only`: a foundation and a layer per topic; `--save-tables` and `--tables`: the export is parsed once, its terms kept as records of 5 to about 20 bytes and its declarations as text, and every layer replays from the parsed file, building only the terms its own declarations reach), with what elaboration needs besides the kernel's constants (`tengai-extinfo` and `--ext`: reducibility, classes, instances, projection and structure
  information, the binder names and annotations of the source). [ADR-0005](docs/adr/0005-promotion-by-replay.md) says what is carried and what is not. `tengai-typeinfo` reads the shape of a statement in any environment.
- **The canonical form** (`conventions.toml`): `tengai-canon` checks the elaborated statements of the library against it, `tengai-normalise` produces it (idempotent).
- **The layout and release rules**: cones, `data/` and `tawatur/` (`tools/check_layout.py`, no import of Tengoku, ever) and the release guard (`tools/release_guard.py`).

Not built yet: no theorem lives in this repository (there is no `Tengai/` topic, `data/` or `tawatur/`). What is promoted is built in Tenro by its transplant workflow as a snapshot of `.olean` layers; that snapshot is a
workflow artifact today, not a published release. Also not built: the retrieval indexes (intent, shape, dependency graph), lenses and a native tactic package (a replayed library carries no tactic code: a session on it has
Lean core's tactics only, ADR-0005). The measurements of the transplant so far are in [Tenro's `docs/transplant.md`](https://github.com/competemath/tenro/blob/main/docs/transplant.md).

The volatile experiments, the drip agents and the benchmarks of hypotheses live in
[Tenro](https://github.com/competemath/tenro), not here.

Licence: Apache-2.0 (see `LICENSE`). Content promoted from Tengoku keeps its upstream licence and credit in its record.

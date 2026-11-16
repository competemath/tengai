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

**Status: P0.** Nothing is built yet; this repository holds the design. Start with [docs/design.md](docs/design.md) and the
decisions in [docs/adr/](docs/adr/).

The volatile experiments, the drip agents and the benchmarks of hypotheses live in
[Tenro](https://github.com/competemath/tenro), not here.

Licence: Apache-2.0 (see `LICENSE`). Content promoted from Tengoku keeps its upstream licence and credit in its record.

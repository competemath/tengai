# Tengai

The volatile upstream of [Tengoku](https://github.com/competemath/tengoku).

| | Tengoku | Tengai |
|---|---|---|
| What it is | the store: one self-contained tree of verified Lean 4 | the workshop: mathematics made, restructured and thrown away quickly |
| How it changes | slowly, append-only, through a gate and a merge queue | violently and rapidly, by anomalous-archangel and by pull request |
| Names | permanent | free to move |
| Depends on | nothing | Tengoku, at the commit in `tengoku.pin` |

Everything in `Tengai/` compiles against Tengoku (`import Tengoku.All`) with every warning an error, no `sorry`, and only the three classical
axioms.

## The seed

A small, finished piece of abstraction, to have something real for the first drip to read:

- `Tengai.Seed.Gauss`: twice the sum of `0 … n-1` is `n (n-1)`, in any commutative ring (Tengoku has it for the naturals, with truncated subtraction).
- `Tengai.Seed.OddSum`: the sum of the first `n` odd numbers is `n²`, in any commutative ring.
- `Tengai.Bridge.GaussOdd`: the second is the first, twice, plus `n`.

## anomalous-archangel

On every drip it reads the whole tree like a mathematician: understands and maps it, pictures it, tries to abstract it (3-d to n-d, discrete to
real, finite to infinite, commutative to general), weighs what a result does to other mathematics, and bridges pieces that look unrelated. It
has angels under it, with a spawn limit of depth 2, breadth 3 and a budget that is conserved down the tree. It is sovereign: it may rewrite
anything, but only Lean that passed the gate lands, and every other claim carries a label (`note`, `observation`, `conjecture`).
See [docs/anomalous-archangel.md](docs/anomalous-archangel.md). Its findings are in `drips/`; the proof requests it wants leak-archangel to take
are in `drips/requests.json`. The dashboard at competemath.com/tengai shows both.

How content moves between leak-archangel, Tengai and Tengoku: [docs/flows.md](docs/flows.md).

## Running it

```bash
scripts/tengoku-setup.sh                  # Tengoku at the pin, with its compiled cache (several GB), in .tengoku
python -m anomalous_archangel gate        # lint, Lake with warnings as errors, the axiom audit
python -m anomalous_archangel drip --dry-run
python -m pytest -q
```

In CI (`.github/workflows`): `ci` on every pull request (lint, tests, sign-off, the Lean build); `drip` daily and on demand
(`gh workflow run drip.yml -R competemath/tengai -f budget_usd=8`; `-f dry_run=true` spends nothing). The drip needs the repository secret
`CLAUDE_CODE_OAUTH_TOKEN` (`claude setup-token`, then `gh secret set CLAUDE_CODE_OAUTH_TOKEN -R competemath/tengai`); without it the run says
so and ends green.

Commits are signed off (`git commit -s`). Python is linted by ruff 0.12.2 (line length 140), workflows pin every action to a commit.

Licence: Apache-2.0.

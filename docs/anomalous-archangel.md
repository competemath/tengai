# anomalous-archangel

An archangel is not an agent, a harness or a set of tools: it is the whole finished package. anomalous-archangel is the one that is
sovereign over Tengai. On every **drip** it reads the entire tree the way a working mathematician reads a notebook, and then it changes the
tree.

## What a drip does

1. **Map.** `tree.py` scans `Tengai/` (modules, imports, declarations, doc lines). `tengoku_view.py` reads the pinned Tengoku checkout
   (`.tengoku`) for what arrived lately and marks what looks like leak-archangel's work. `memory.py` supplies what earlier drips already said and
   when each lens last ran. `requests.py` supplies the open proof requests.
2. **Choose lenses.** At most three (the breadth limit). Staleness rotates them; the state of the tree and the news pull some forward.
3. **Spawn the angels.** Each angel is a `claude` process with a lens (`angels.py`):
   *cartographer* (understand and map), *abstractor* (3-d → n-d, discrete → real, finite → infinite, commutative → general),
   *bridger* (connect distant pieces, inside Tengai and to Tengoku), *experimenter* (small cases, patterns, counterexamples, observations),
   *illustrator* (pictures), *historian* (what arrived and what it changes for other mathematics). An angel may send up to three helpers one
   level down; a helper cannot send anyone.
4. **Examine.** A last wave, the *examiner*, reads everything the angels claimed and says keep / drop / revise for each item.
5. **Forget repeats.** A finding too close to something in memory (Jaccard on word sets, 0.55) is dropped and counted.
6. **Land Lean.** Each proposed file goes through the gate (below). A file the gate refuses is put back exactly as it was. The root file
   `Tengai.lean` is regenerated.
7. **Queue proof requests.** A statement the angels want proved is compiled by Leak IV as `theorem t : <statement> := by sorry` (the `sorry`
   warning is the only one forgiven). It enters `drips/requests.json` as `open` if it elaborates, `unchecked` if no gate could say.
8. **Write down.** `drips/<id>/record.json`, `drips/<id>/report.md`, `drips/index.json`, `drips/memory.json`.

## Spawn control, and the money

The archangel is depth 0, the angels depth 1, their helpers depth 2. **Depth ≤ 2, breadth ≤ 3 per wave, two waves per node** by default
(`--max-depth`, `--breadth`). `budget.py` is the ledger: a child's allowance is reserved out of its parent's remaining money before the child
starts, so the allowances of a node's live children never exceed what the parent has left; what a child does not spend goes back to its parent.
A spawn the limits refuse is recorded in the drip (`spawn.refused`), not dropped silently. The tests check the invariant on random spawn trees.
Each angel's process also gets `--max-budget-usd` equal to its allowance.

## Sovereignty, and its one limit

The archangel may add, replace and restructure any module. It may not land a Lean file the gate has not passed, and it may not state a claim
without a label.

**The gate** (`gate.py`) is, in order:

1. `lint`: no `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `unsafe`, `partial`, `implemented_by`, `extern`, no code that runs at
   elaboration (`#eval`, `run_cmd`, `initialize`), no global notation, syntax or macros (a library that leaks notation breaks everyone who
   imports it: Tengoku's canary exists because of one), no switched-off linters, no global instances, imports only `Tengoku.All` and `Tengai.*`.
2. `leak-iv`: the file and everything of Tengai it needs, as one script, compiled by Leak IV (`verify_full_script`): no errors, no warnings.
3. `lake`: `lake build` of the module and of every module that depends on it, against Tengoku at the pin; `warningAsError` is on, so a
   warning (including `sorry`) is an error; then `#print axioms` of every theorem: only `propext`, `Classical.choice`, `Quot.sound`.

A gate that cannot be asked answers `infra`, and `infra` is not `ok`: the file is deferred. At least one compiling gate must have said `ok`.

**Labels.** An angel labels a finding `note`, `observation` or `conjecture`. It cannot say `verified`; only a Lean file that passed the gate is
verified, and the record says so (`changes[].landed`).

## Containment

`containment.py` is the Python twin of compete-math's `public/leak-containment.mjs`. An angel's `claude` process:

- has a pinned tool set, `Read Grep Glob`, and is started with `--restricted` when the CLI knows it (otherwise `Read` only, scoped by path
  rules, with `--permission-mode dontAsk`); `Bash`, `Write`, `Edit`, `Task`/`Agent`, `WebSearch`, `WebFetch` are named in `--disallowedTools`;
- runs in a throwaway directory holding a copy of the tree and the digests, never the repository; Tengoku's modules are readable, nothing else;
- gets the prompt on stdin, `--no-session-persistence`, a spend cap, and an environment with every secret-looking variable removed (the CLI's
  own login is kept: it cannot start without it);
- cannot write: it answers with one JSON block, parsed against a closed schema (`proposals.py`), and the archangel decides what lands.

The Lake step of the gate runs with no token of any kind in its environment. `tests/test_containment.py` checks the argv a run would get
without spawning anything.

## Commands

```bash
python -m anomalous_archangel drip --dry-run      # a fake agent and a fake gate, in a copy: nothing spent, nothing changed
python -m anomalous_archangel drip --budget 8     # live: needs the claude CLI, a login (or CLAUDE_CODE_OAUTH_TOKEN) and .tengoku (scripts/tengoku-setup.sh)
python -m anomalous_archangel drip --no-land      # study only
python -m anomalous_archangel gate [--leak-iv]    # the gate on the whole tree as it is
python -m anomalous_archangel root                # regenerate Tengai.lean
python -m anomalous_archangel status
python -m anomalous_archangel requests list|claim|fulfil|abandon <id>
```

## Interfaces

**For the dashboard.** `drips/index.json`: `{schema, updated, tree: {modules, declarations, theorems, lines, hash}, open_requests, drips: [{id,
started, mode, summary, counts, spent_usd, tree, tengoku_pin, lenses, top: [{kind, label, title, lens}], landed, path}]}`, newest first.
`drips/requests.json`: `{version, requests: [{id, statement, informal, why, drip, lens, status, created, claimed_by, proof_path}]}`.
Both are read from `raw.githubusercontent.com`.

**For leak-archangel.** Take an `open` request: `requests claim <id>`; prove the statement (the file must contain the statement verbatim and
import `Tengoku.All`); `requests fulfil <id> --file proof.lean` runs the same gate, writes `Tengai/Proved/R<id>.lean` and marks the request
`proved`. Or abandon it with a reason.

## Not done, on purpose

- The statement check for `fulfil` is textual (the statement must appear verbatim) plus the compile: it does not prove the file's theorem *is*
  the request, only that the file contains the request's text and compiles. A theorem with a different conclusion that quotes the statement in a
  comment is stopped because comments are not counted; a file that proves something else next to the statement is not caught by the machine.
- Nothing here writes to Tengoku. `docs/flows.md` says how settled content leaves.

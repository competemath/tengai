# ADR-0005: content enters tengai by kernel replay of an export

Status: proposed 2026-11-20 (the first transplant, with measurements, decides whether it is adopted).

## Context
Tengai builds on Lean core alone (I3), loads under an absolute cap (C_load) and must hold a strong amount of Tengoku. Measured on 330 Tengoku theorems (tenro `tools/promote/sizing.py`): none is
closed over Lean core; a theorem needs a median of about 12,500 constants outside it, 10 theorems need 35,000 distinct constants together, 100 need 78,500 and 330 need 87,600 (5.0M if nothing were shared).
Content is therefore one shared foundation of about 80,000 constants plus about 40 new constants a theorem. A proof written against Mathlib cannot be re-proved on Lean core by source copying.

## Decision
A promotion is a **kernel replay** of a `lean4export` file (format 3.x), done by `tengai-replay`: every declaration goes through `addDecl`, so a wrong term is refused whatever produced it (I1); what Lean core already
holds must have the same type and is not added again; the result is a built `.olean` (`TengaiData.<Topic>`), which a prover imports with the snapshot on `LEAN_PATH`. The release is the `.olean` snapshot
(`docs/design.md`). The replay tool imports `Lean`; no library module imports it and the modules it writes do not, so the import stays as small as the content. What the kernel does not hold but elaboration needs is carried in a second, small file
(`tengai-extinfo` reads it where the constants were built, `tengai-replay --ext` puts it back): reducibility, projection information, classes, instances (global, or scoped with `--scoped-instances`), structure
information (the fields and parents: `{ x := 1 }`, `{ p with x := 2 }`, `p.x` through a parent) and the binder names and annotations that the export's term sharing replaced. Nothing else is registered: no simp set,
no `ext`, `norm_cast` or `elab_as_elim` entry, no notation (macros and elaborators are code, which a replay does not carry). The equation lemmas of recursive definitions (the structural and well-founded tables that `unfold` and `simp [f]` read), matcher information, the smart-unfolding auxiliary definitions and docstrings are not carried either, and neither is any tactic code: Mathlib's `ring`, `linarith`, `norm_num`, `positivity`, `gcongr` and `aesop` are code and attribute tables, which a replay does not carry, so a session on a replayed library has Lean core's tactics only. A prover works with the API lemmas of a replayed constant, not with its unfolding (I5). A replayed module is searchable, and those are active only through the scoped layer of
a topic (I4). Structure instance notation (`{ x := 1 }`, `{ p with x := 2 }`) needs more than the structure information: the structure's flat constructor `S.mk._flat_ctor`, an abbreviation Lean adds with every structure, and its projections.
These are constants of their own. An export of the closure of some theorems holds them only if a theorem mentions them (the flat constructor has an internal name, so not even the exporter's default mode writes it), so a
promotion that wants a structure constructible with `{ }` names them as roots (`tests/replay/check_struct_inst.lean` shows an export with and without); the transplant does not do this yet. The default value of a structure field
(`S.f._default`) is the same kind of constant, and `{ }` notation asks for the fields whose defaults are missing.

## Consequences
- The source of a promoted theorem is its export (hashed, in `data/`), not a Lean file; readable statements come from the statement text carried by Tengoku's record and are checked against the replayed constant by isnad id (the promotion lens, ADR-0003).
- A replayed constant has no compiled code (no IR): it can be checked, applied and rewritten with, not evaluated. That is all a prover needs; anything that must run is written in Tengai itself.
- An independent checker re-checks the `.olean` snapshot (I1), as Tengoku's nightly does.
- Whether the foundation fits C_load is measured next on a built module; if it does not, the foundation is trimmed (fewer, higher-leverage theorems), never the cap.

## Layers (2026-11-21)
One module holding everything promoted is loaded whole by every session, so the cold import grows with the library and meets C_load (measured: +0.093 s for 5,000 theorems, one module). A promotion is therefore a **stack of
layers**: a foundation layer holding the constants more than one topic needs, and one layer per topic holding the constants only it needs, each importing the layers it depends on. A session imports the layers
of the topic it works in and nothing else. The mechanism is two options of `tengai-replay`: `--import MODULE` starts the replay from an earlier layer (found on `LEAN_PATH`) instead of Lean core alone, and `--only NAMES.jsonl`
adds only the declarations whose first name is listed (an inductive block is one unit, its constructors and recursors come with it); everything else of the export is read and left out. Every layer is
kernel-checked on its own, so a layer that names a constant whose dependency is in no imported layer is refused. Which constant goes in which layer is a property of the dependency closures: a constant's layer is
decided by the set of topics whose closure holds it, and a constant's dependencies are used by at least the topics that use it, so the foundation never depends on a topic layer.

### Each layer is its own process
A promotion writes one module per layer, and each layer is written by its own `tengai-replay` process, which reads the whole export again. This is on purpose. Lean writes one module per process: the exports of two
premise-selection extensions (`symbolFrequency` and `sineQueNon`) read process-wide caches (`localSymbolFrequencyMapRef`, `symbolFrequencyMapRef`, private to Lean), so a process that writes several modules gives every later one the
first one's data. It was tried on 2026-11-21 (a `--layers PLAN` mode that reads and parses the export once and replays every layer from it): the counts and the sizes of the layers equalled those of one process per layer, but the
`sineQueNon` trigger of the second layer of a three-layer fixture was `HAdd.hAdd` where a fresh process writes `Fx.shared`. Recomputing the first extension's entry per layer is not enough (the second reads the first's
imported cache), and the caches cannot be reset from outside Lean. The cost of a layer is therefore one reading of the export (on the test fixture, 6.5 million lines, a layer that adds one constant takes 15 s, nearly all of it reading; the layers of the real runs are in tenro `docs/transplant.md`).
The way to avoid it without sharing a process is a parsed snapshot of the export (names, levels, expressions, declaration lines) that each layer's process reads instead of the JSON: not built.

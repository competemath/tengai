# How content moves

```
leak-archangel ──proofs──▶  Tengai  ──settled──▶  Tengoku
      ▲                       │  ▲
      │                       │  │ reads, studies, rewrites
      └──proof requests───────┘  └── anomalous-archangel (the drip)
```

**Into Tengai.** Two ways. leak-archangel proves an `open` request (`python -m anomalous_archangel requests fulfil`), and the file lands after the
same gate as the archangel's own. Or a person opens a pull request: `ci` builds the tree with warnings as errors.

**Inside Tengai.** anomalous-archangel rewrites freely. Names, modules and statements move; that is the point of the upstream. Nothing outside
Tengai may depend on a Tengai name staying put.

**Out of Tengai.** Tengoku is the store that does not change. A Tengai module is *settled* when it has stood unchanged through several drips,
its theorems rest on the three classical axioms only, and the gate is clean. Settled content reaches Tengoku the way every contribution does,
through its pull request gate and the memory-intake pipeline of emissary-archangel (a person approves). This repository does not push to
Tengoku and holds no token that could.

**Tengoku into Tengai.** `tengoku.pin` names the commit of Tengoku Tengai is built against; its compiled cache is Tengoku's own release asset.
`scripts/tengoku-setup.sh --latest` moves the pin to the newest published cache. The drip does that before it reads, so it studies the newest
Tengoku, and commits the new pin with its files.

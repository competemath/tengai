# The release barrier: no v1 before the owner's explicit approval

Tengai (and Tenro, and any library either of them contains) is experimental. Nothing at version 1 or later is released until the owner has said so, after a baseline of quality has been
shown (the readiness gates of ADR-0004). Three layers, from the one that can be got round to the one that cannot:

1. **The guard (`tools/release_guard.py`, run by `.github/workflows/release-guard.yml`).** It fails if a `lakefile` declares a version above `max_major` of `release-guard.toml` (now 0), if a
   version tag above it exists, or if `core.lock` pins one. On a pushed tag or a published release above the cap, the workflow deletes the tag (and the release) and fails. A change to the guard
   itself (its config, script, workflow or test) needs an approving review by a collaborator with write access who is not the author. This is a tripwire: whoever can push can also push
   a workflow change, so it only catches a mistake.
2. **The required check.** Make `release-guard` a required status check (part of the ruleset the owner is creating for `main`).
3. **The tag ruleset (the lock).** One owner command, which no workflow and no collaborator can override (`bypass_actors` is empty):

```bash
gh api -X POST repos/competemath/tengai/rulesets --input tools/release-ruleset.json
gh api -X POST repos/competemath/tenro/rulesets --input tools/release-ruleset.json
```

   It forbids creating, moving or deleting any tag that starts with a digit 1-9 (after an optional `v`). To release 1.0, the owner edits or deletes this ruleset and raises `max_major`
   in `release-guard.toml` in a reviewed pull request: two deliberate acts, both visible.

Versions at 0.x are not covered: Tengai's own tags (v0.0.N) are the pins Tenro mirrors.

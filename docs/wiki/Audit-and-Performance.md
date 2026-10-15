# Adversarial audit, CI and performance

## Reproducible baseline (15 October 2026)

At `main` commit `491886a8788fdf5f3098cf4b7b83f181d2ba0666`:

- 773 Lean files, including 363 under `SuccessorTree/V10/`.
- 256 Lean checking scripts under `scripts/` and 20 workflow files.
- `SuccessorTree.lean` imports many endpoint and intermediate modules; `V10/All.lean` imports 231 V10 modules directly. Direct-import omission is **not** evidence that another module is unused.
- A successful main branch `Lean` run spent about **1 min 44 sec** in the cached full build, while the full job took about **10 min**.
- A successful `V10 counting audit` checked **240** named scripts. Its dependency build took about **1 min 27 sec**, then the **serial axiom-check step took about 12 min 24 sec**; the job took about **19 min**.
- The CI cache restoration alone transferred roughly **738 MB** of Lean toolchains and **2.06 GB** of Lake workspace. Removing proof files without dependency analysis may not materially reduce that cost.

Those are observed workflow logs, not predicted speedups.

## Improvements in the audit PR

- `scripts/run-v10-checks.py` retains one isolated `lake env lean` process and one exact named-axiom validation per checker, but uses **three bounded workers** and saves `v10-check-timings.json` to measure wall time and outliers.
- `scripts/select-v10-checks.py` compares the actual full `push` range (`github.event.before` through HEAD), as well as the PR synthetic-merge base. Imported dependencies are followed transitively and unknown modified V10 modules are rejected.
- A daily scheduled **full** V10 audit and workflow dispatch keep exhaustive coverage even when routine main merges use affected-consumer selection.
- `scripts/audit-import-graph.py` generates `successor-import-audit.json`: module reachability from public umbrella and named checks, orphan **candidates**, direct-import hotspots, and indicative risk-token counts. It never deletes files or claims comments containing `sorry` are proof holes.
- Axiom checking continues to reject unexpected axioms, duplicate/substituted endpoint names, error reports and `sorryAx`. Allowed axiom names are `propext`, `Classical.choice` and `Quot.sound`.

## Measured results and complete-source review

At PR [#493](https://github.com/janhubicka/lean-successors/pull/493),
exact-head workflow 38776681095 compiled the selected V10 targets and passed
**240/240** named transitive-axiom checkers. The three-worker check stage took
**344.191 seconds**, versus about **744 seconds** for the preceding serial
full audit (about **54% less** wall time). The full job fell from roughly
16 minutes to roughly 10 minutes; this includes runner/cache differences.
The fastest path for a changed V10 endpoint remains the selected closure,
while the daily full audit preserves complete coverage. The CI artifact
contains per-check timing and source-import JSON.

The checked source snapshot contains **518** source modules (including the
root umbrella) and **254** checker modules. Reachability found **zero** source
modules outside *both* the root umbrella and all checker entry points.
Only these three were not imported by the root umbrella, and each has an
explicit checked entry point:

- `FatTree.A4RootPigeonhole` via `CheckFatTreeReplay.lean`;
- `V10.M3StepGraphB3` via `CheckV10M3StepGraphB3.lean`;
- `V10.PrescribedKptOrderEmbedding` via `CheckV10PrescribedKptOrderEmbedding.lean`.

Consequently, there is **no evidence for safely deleting a batch of orphaned
Lean files**. Every apparent `axiom` or `admit` token found by the static
inventory was inside a comment, not an executable declaration. The separate
transitive checker is still decisive for the exported theorem endpoints.

The cached full Lean build produced **989 warning lines**. A measured breakdown
includes 429 transitional Mathlib module-system import warnings, 159
deprecations, 67 unnecessary-`simpa` suggestions, 45 unused simp arguments,
26 unused-tactic warnings and 20 implicit section-variable warnings; further
warnings concern tactic suggestions, unused binders and similar lint.
About **398 of 517** source files directly import the broad
`Mathlib.Tactic` umbrella. These are useful *profiling and cleanup targets*,
not evidence that the proof is wrong or that all warnings cause the slow build.

See [compiler warning triage](Compiler-Warnings.md) for a staged strategy.
Do **not** suppress warnings globally merely to reduce log size.

## Developer commands

```bash
lake exe cache get
# Fast abstract development: no V10 application loaded
lake build SuccessorTree.Core
# Fast Section 6 iteration:
lake build SuccessorTree.V10.HUniformEnvelopeBound
lake env lean scripts/CheckV10HUniformEnvelopeBound.lean \
  > h-envelope-axioms.log 2>&1
python3 scripts/check-axiom-log.py h-envelope-axioms.log \
  scripts/CheckV10HUniformEnvelopeBound.lean

# Full clean validation:
lake build
lake env lean scripts/CheckShapeProofRoutes.lean

# Selection is full outside a PR/push GitHub Actions event.
python3 scripts/select-v10-checks.py
python3 scripts/run-v10-checks.py --checks-file v10-selected-checks.txt --jobs 3
python3 scripts/audit-import-graph.py
```

Use the pinned `lean-toolchain` and `lakefile.toml`. `lake-manifest.json` is currently gitignored; this means reproducible dependency resolution deserves a separate, tested change. Keep the transitive axiom audit for any exported theorem even if a local `lake build` succeeds.

## Adversarial review checklist

1. **Statement audit:** compare every final `#check` type with the manuscript quantifiers, ambient structures, positive/negative relations, empty boundaries, finite ranges and language arities.
2. **Axiom audit:** run the named `#print axioms` check transitively. Do not confuse a proof of a conditional lemma with discharge of its premises.
3. **Dependency audit:** ensure finite `V10` properties do not leak into the reusable abstract `SMTree` theorem. Verify the two shape proof routes separately.
4. **Dead-code audit:** inspect each orphan candidate with `git grep`, local imports, workflow scripts and downstream repositories. Preserve any actual theorem API. Only then delete/merge stale experiments; history preserves the previous version.
5. **Performance audit:** profile individual slow proof files, warning volume and memory use before large rewriting. Favor narrower imports, specialized endpoints and split CI validation over blindly increasing elaborator limits.
6. **Manuscript integrity:** do not change author prose as a side effect of Lean cleanup. Distinguish corrected B3 and finite `L`-age witnesses from the original printed B3. Review all TODO/validation notes independently.

## One owner for each axiom check

The general `Lean` workflow previously repeated **73**
`scripts/CheckV10*.lean` verification steps already discovered and checked
by the dedicated `V10 counting audit`. Those duplicate shell steps have
been removed. The general workflow still performs the complete `lake build`,
abstract Ramsey proof-route independence and transitive axiom checks,
fat-tree checks, free-ancestral checks and envelope proofs.

The `V10 counting audit` remains the one authoritative CI owner of every
`CheckV10*.lean` script. Its dependency-sensitive selection, nightly
exhaustive run, conservative batch parser, 240-script coverage regression,
named-axiom validator and retained artifacts are unchanged. Source edits
under `SuccessorTree/**` trigger both workflows. The structural ownership
guard is `scripts/check-ci-audit-ownership.py`; the checkers' own proof
correctness is still verified by Lean and `scripts/check-axiom-log.py`.

This change removes nearly 800 lines of redundant workflow code. Its
end-to-end runtime saving should be measured against an exact-head build,
not inferred just from line count. No proof source or public theorem was
modified.

## Next cleanup phases

- Source reachability found no orphan Lean modules. Audit *private declarations and redundant lemmas inside active files* before considering deletions; obsolete fat-tree maintenance workflows were removed in PR #494.
- Audit the root umbrella and `V10/All.lean` for redundant import lists; keep public APIs stable until known downstream repositories are updated.
- Keep the shared Lean workflow compact; any new V10 theorem check goes in the dynamically discovered dedicated V10 checker suite, not into a second hard-coded list.
- Triage the categorized compiler warnings, then gradually replace broad `Mathlib.Tactic` imports with verified narrower dependencies. Avoid moving hundreds of modules until incremental build behavior is measured.

Open performance issue: avoid a repository-wide re-elaboration on every minor Section 6 patch and investigate why the 2 GB Lake cache can become stale when the cache key does not change with sources.

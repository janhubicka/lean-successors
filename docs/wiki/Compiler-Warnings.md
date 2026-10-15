# Compiler warnings and incremental build triage

This inventory is from the exact Lean build log of the successful
[main workflow](https://github.com/janhubicka/lean-successors/actions/runs/38767247619)
on 15 October 2026, not from a guess based on source filenames. The
project currently uses Lean 4.35.0-rc3 and pinned Mathlib.

## What the 989 warning lines actually mean

| Category | Warning lines | Priority |
| --- | ---: | --- |
| Transitional Mathlib module-system imports | 429 | Architectural migration; do not fix by inserting `module` blindly |
| Deprecated names | 159 | Safe candidate for small mechanically reviewed patches |
| `simp` already closes a `simpa` goal | 67 | Clean opportunistically during proof edits |
| Unused simp arguments | 45 | Simplify locally; verify the actual simplifier dependencies |
| Unused tactics and tactics never executed | 26 | Remove redundant steps after rebuilding the affected module |
| Automatically included unused section variables | 20 | Improve declaration signatures and binder scopes where appropriate |
| Other binder, tactic-suggestion and linter warnings | Remaining | Review individually |

The category counts above do not exhaustively classify all 989 lines.
No category should be interpreted as a Lean proof gap.

## First candidates for low-risk cleanup

Deprecation warnings are concentrated around the currently accepted Lean
aliases `if_pos`, `if_neg`, `dif_pos`, `dif_neg` and other renamed lemmas.
The compiler recommends `ite_eq_left`, `ite_eq_right`,
`dite_eq_left`, `dite_eq_right`, respectively. In addition:
`if_true`/`if_false` → `ite_true`/`ite_false`, and
`Set.mem_setOf_eq` → `Set.mem_ofPred_eq`. Apply these with scoped
module-level CI and the exact named transitive-axiom checks, **not** an
unreviewed global search-and-replace across Section 6.

About **398 of 517** files under `SuccessorTree/` directly import
`Mathlib.Tactic`. This broad umbrella is an important candidate for
selective import narrowing, but changing it may expose implicit tactic
dependencies. Begin with a small, stable non-V10 leaf module, find its
actual tactic/library imports, and measure the difference in an uncached
incremental build before applying the pattern elsewhere.

There are isolated long modules such as `FatTree/Lift.lean`,
`FatTree/Amalgamation.lean`, `FatTree/ShapeCorrespondence.lean`,
`Canonical.lean` and `FatTree/A4Trace.lean`. File size is not by itself
an elaboration-time measurement. Split a module only when it has a
logical reuse boundary or contributes unusually to measured runtime.

## Build-time distinction

The recent cached full root build finished in approximately
**1 minute 44 seconds**. The much slower initial V10 CI job was primarily
its serial **240 separate Lean processes**, not source elaboration; PR #493
improved that bottleneck without modifying proofs. Work on checker batching
is intentionally kept in a separate experimental PR and must pass all
original named endpoints before being merged.

Preserve these separate profiles:

1. cold toolchain and Mathlib cache acquisition;
2. warm dependency and project module rebuilds;
3. per-module Lean elaboration time and peak memory;
4. transitive `#print axioms` check time;
5. Python finite-model regression time.

Reducing warning count alone is not a proven wall-clock improvement.
Changing the public `SMTree` assumptions for a new paper must be measured
separately from cleanup of the verified v10 theorem.

## Reproducible commands

```bash
lake exe cache get
lake build SuccessorTree.Core
lake build SuccessorTree.V10.HUniformEnvelopeBound
lake build

# Axiom check for a selected Section 6 result
lake env lean scripts/CheckV10HUniformEnvelopeBound.lean \
  > h-axioms.log 2>&1
python3 scripts/check-axiom-log.py h-axioms.log \
  scripts/CheckV10HUniformEnvelopeBound.lean
```

The complete nightly V10 audit is an indispensable independent check of
changed imports, exported theorem assumptions and internal checker coverage.
Avoid global linter suppression, unchecked native evaluation, new `axiom`
declarations, or replacing the existing two independent shape proof routes
with an unverified compatibility wrapper.

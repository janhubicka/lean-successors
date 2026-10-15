# Lean successors — formalization wiki

**Status:** 15 October 2026. This is the maintained entry point for the reusable library `janhubicka/lean-successors` and the verification of the successor-tree manuscript. It records **theorems and their exact scope**, not merely which sections have received Lean files.

## Start here

- [Architecture and dependency boundaries](Architecture.md): `LevelTree`, `STree`, `SMTree`, Hales–Jewett, two independent Ramsey proof routes, and the `V10` application.
- [Verified theorems and manuscript correspondence](Theorems-and-Manuscript.md): named public declarations, additional Lean lemmas, proof adjustments, and unproved final transfers.
- [Adversarial audit and build performance](Audit-and-Performance.md): proof-assumption checks, removal policy for abandoned branches, CI commands, benchmark baseline, and practical profiling.
- [Axioms and future generalizations](Axioms-and-Future-Work.md): how to preserve the existing theorem while eventually weakening duplication assumptions.
- [Compiler warning triage](Compiler-Warnings.md): measured warning categories and safe incremental-import cleanup.

The proof routes are explained in [`docs/shape-proof-routes.md`](../shape-proof-routes.md). The precise Section 6 validation ledger is [`docs/v10-section6-final-assembly-20261015.md`](../v10-section6-final-assembly-20261015.md). These are part of the audit trail, not a substitute for compiled declarations and transitive axiom checks.

## Status at a glance

| Component | Status | What is established |
| --- | --- | --- |
| Finite starred Hales–Jewett | Verified | `starHJ_finite` is proved, not postulated as a theorem input. |
| Abstract successor tree | Verified at the Lean `SMTree` interface | M1–M3, canonical maps and shape-preserving Ramsey. |
| Fat-tree Ramsey space | Verified | Unconditional typed A4 and abstract Ellentuck endpoints. |
| Finite Ramsey corollaries | Verified | Bounded/exact terminal variants, including common-terminal padding. |
| `V10` normalized finite-type tree | Verified | `normalizedKptSMTree` instantiates M1, corrected M2, literal M3. |
| Section 6 finite `H^+` envelope bound | Verified at its stated normalized, parameterized scope | Actual Algorithm 5.4 run and sharp finite bound. |
| Section 6 universal `K → H^+ → G^+` transfer and Theorem 6.26 | **In progress** | Do not mark the source theorem as completely formalized on the strength of the finite envelope bound. |
| Arbitrary relation arities / weakened duplication axioms | **Deliberately deferred** | Not part of the validation of the current v10 draft. |

`V10` source and its checking scripts are sizeable; a passing compilation is **not** an assertion that every English prose statement is literally equivalent to the Lean theorem. The [theorem index](Theorems-and-Manuscript.md) lists the remaining adapters and hypotheses.

## Policy

1. Keep the current v10 theorem, the four manuscript repairs, and their reviewed annotations distinct from prospective axiom changes.
2. Clean the Lean library, its workflows and auxiliary documentation freely; do **not** silently alter the frozen authorial manuscript prose.
3. Retain genuine mathematical results and proof routes. Delete a development experiment only after checking references and downstream users; Git history remains the archive.
4. Before claiming a result is checked, record the precise declaration, all explicit hypotheses, `#print axioms` output, successful exact-head CI and any unproved manuscript adapter.
5. Favor small stable lemmas and module import boundaries over one large application-specific theorem file.

This directory is repository-hosted wiki source so its updates can be reviewed and checked in PRs. It can be copied into the separate GitHub Wiki repository without changing the documentation links or theorem statements.

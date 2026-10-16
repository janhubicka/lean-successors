# Successor trees — Lean research library

**Lean validation checkpoint: 16 October 2026.** On
[`main` commit `1e084eb47aee`](https://github.com/janhubicka/lean-successors/commit/1e084eb47aee283f94ced58290455baf882a5285),
the [full Lean workflow](https://github.com/janhubicka/lean-successors/actions/runs/38916948261)
and [V10 transitive-axiom workflow](https://github.com/janhubicka/lean-successors/actions/runs/38916948218)
both succeeded. This supersedes earlier pages that described the
universal Gω / age-universal K big-Ramsey transfer as unproved.

This wiki documents the precise *verified Lean statements*, the
human mathematical proof architecture, maintenance and refactoring,
and the distinction between a checked normalized statement and
its identification with the author's current external manuscript.

## Chapters

| Chapter | Purpose |
| --- | --- |
| [Using the library](Using-the-library.md) | Install/import public theorem modules; copyable `#check` statements; hypotheses |
| [Theorems and manuscript](Theorems-and-Manuscript.md) | Exhaustive principal theorem index, source scope, formalized repairs |
| [Architecture](Architecture.md) | Successor monoids, two independent shape-Ramsey routes, fat trees and Kpt |
| [Adversarial referee record](Adversarial-referee-record.md) | Mathematical scope, transitive axioms and dependency/maintenance scrutiny |
| [Audit and performance](Audit-and-Performance.md) | Actual workflow evidence, import audit, CI speed improvements |
| [M1–M3 dependency map](M1-M3-Dependency-Map.md) | Exact replay, habitation, padding and fusion clients |
| [Axioms and future work](Axioms-and-Future-Work.md) | Controlled replay and future M3 relaxation, not yet claimed |
| [Fat-tree A4 review](A4-Adversarial-Verification.md) | Edge cases, unconditional A4 and circularity firewall |
| [Compiler warnings](Compiler-Warnings.md) | Categorized warnings and import improvement strategy |
| [Wiki publishing](Publishing.md) | Source-controlled documentation sync instructions |

## Verified theorem families

| Result | Scope and status |
| --- | --- |
| Starred Hales–Jewett | Kernel checked |
| Abstract M1–M3 shape Ramsey | Kernel checked by two independent one-dimensional inputs |
| Fat-tree Ramsey-space A4 and Ellentuck | Kernel checked at typed interfaces |
| Finite bounded and exact-terminal corollaries | Kernel checked, including common-terminal padding |
| Envelope minimality | Kernel checked with explicit E1 and nonempty-top assumptions |
| Normalized finite unary/binary Kpt monoid | Kernel checked M1, M2, M3 and concrete E1 |
| Finite H+ sharp actual-run level bound | Kernel checked |
| Big Ramsey in canonical Gω and arbitrary countable age-universal K | Kernel checked at normalized unary/binary all-Emb(A,K) scope |
| Arbitrary higher arity / weakened M3 | Deliberately deferred |
| Literal full author `main.tex` equivalence | Requires direct manuscript source comparison |

The final checked
`V10.universalBinaryUnaryModel_allEmbeddings_bigRamsey_bound` includes
*all* injective induced pattern embeddings, not just increasing
finite enumerations. Its original language retains unary predicates,
both directed binary orientations, binary diagonal facts and all
negative relations. The countable target is required to satisfy
`UniversalForNormalizedFamily`, rather than just avoiding forbidden
patterns.

## Library design

`SuccessorTree.Library.Abstract` exposes application-neutral
M1–M3/shape/Hales–Jewett/fat-tree/envelope results.
`SuccessorTree.Library.Applications` exposes normalized Kpt and
finite big-Ramsey theorems.
`SuccessorTree.Library.Examples` exposes the free-ancestral model.
The top-level `SuccessorTree.Library` combines them, but the
historical `SuccessorTree` remains a complete *research-development*
build. There are no active downstream API users, so implementation
aliases and wrappers need not be maintained.

The author mathematical text remains frozen except approved
TODO/validation annotations. The author-edited TeX is not hosted in
this Lean repository; do not silently replace a source-fidelity
check with a passing Lean kernel report.

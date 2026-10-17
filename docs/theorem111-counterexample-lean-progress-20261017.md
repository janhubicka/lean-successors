# Theorem 1.11 direct-monoid counterexample — complete Lean verification

**Status:** all mathematical parts of the ZFC counterexample are checked
by the Lean kernel. The full formal proof merged on 17 October 2026 as
[PR #565](https://github.com/janhubicka/lean-successors/pull/565)
(commit [2b3fb28a](https://github.com/janhubicka/lean-successors/commit/2b3fb28a871f89282c6ad8d899d7014cf0223010)).
Its focused exact-head compilation and named transitive-axiom checks
[passed](https://github.com/janhubicka/lean-successors/actions/runs/38986241498).
No `sorry`, `admit`, new mathematical axiom, CH or regularity
assumption on continuum was used.

## Checked mathematical modules

| Module (`SuccessorTree.Counterexample`) | Mathematical content |
| --- | --- |
| `NowhereDense` | Right compatibility; incompatible antichain; late proper gaps; nonempty basic local escape |
| `Topology` | Upgrade to `IsNowhereDense` in the **direct monoid** Ellentuck topology |
| `MaskCodes`, `StretchHistory` | Explicit root-marker codes, source-level parameter remapping and raw history model |
| `MarkedFusion` | Genuine infinite `Q_A` shape maps from M1 fusion of verified one-gap maps, level-range and root-image laws |
| `RootMarkerRigidity`, `RootMarkerTransport`, `MarkerIntervals`, `MarkerTransfer` | Mandatory successor codes cannot carry original-root markers at retained levels; every omitted target level of `Q_A` carries one, and root-fixing outer maps preserve them |
| `CompatibilityLevels`, `CompatibilityMarker` | A common algebraic right multiple forces an **infinite** fixed meeting-level set into the retained-level range of `Q_A` |
| `BinarySupports`, `SupportRigidity` | Continuum many explicit binary-prefix almost-disjoint supports and unique-compatible-candidate lemma |
| `PureEnumeration`, `GreedySelection` | Enumerate all pure shape maps by binary sequences, ZFC greedy recursion along a minimal continuum well-order, no CH |
| `ConcreteAntichain` | Incompatible transversal meeting every pure same-depth root neighbourhood |
| `Final` | **Closed nowhere-dense, meagre, non-avoidable** witness for the original depth-preserving Theorem 1.11 |

## Source-facing exact endpoint

`SuccessorTree.Counterexample.exists_closed_nowhereDense_not_avoidable` asserts
the existence of `Z` that is *closed nowhere dense in the actual
monoid Ellentuck topology* and satisfies `¬ AvoidableAtRoot Z`.
Here `AvoidableAtRoot Z` means precisely
\[
\exists H\in[1,\mathrm{Id}]\quad [f,H]\cap Z=\varnothing,
\qquad f(\text{root})=s.
\]
The new literal topological corollary
`SuccessorTree.Counterexample.exists_meagre_not_avoidable` asserts
meagreness rather than just nowhere density.

**Crucial convention:** the manuscript's pure neighbourhood
`[1,Id]` fixes source levels 0 and 1, although the corresponding
abstract Ramsey-space finite-approximation index is 2. This
depth-preserving definition is *stronger* than a variant allowing
arbitrary finite-stem end-extensions; the latter has not been
refuted by this counterexample.

The positive Theorem 1.17 (fat-tree Ellentuck) and finite shape
Ramsey Theorem 1.6 stay checked. The manuscript remains frozen:
only source-facing TODOs and validation status are to be updated
after author review.

## Test and public API

- Exact-name audit: `scripts/CheckTheorem111Counterexample.lean`
  with `#print axioms` for all principal lemmas, including the final theorem.
- Focused CI: `.github/workflows/theorem111-counterexample-lean.yml`.
- Binary-prefix support independent CI:
  `.github/workflows/theorem111-binary-supports.yml`.
- The finite history-code regression remains a separate *diagnostic*,
  not a substitute for the complete infinite Lean proof.
- Exported via `SuccessorTree.Library.Examples`, not the
  lightweight abstract library import boundary.

The proof is the **original counterexample itself**, not a conditional
interface that assumes the missing compatibility or almost-disjointness
lemma. The English [standalone note](theorem111-zfc-counterexample-20261016.md)
and [adversarial referee audit](theorem111-zfc-counterexample-referee-20261016.md)
remain useful independent explanations.

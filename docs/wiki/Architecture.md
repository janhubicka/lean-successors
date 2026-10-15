# Architecture and proof organization

The project contains an abstract, reusable theorem and several concrete applications. The present organization is **logical**, not an instruction to rename hundreds of Lean files merely for cosmetic symmetry.

## Dependency overview

```text
HalesJewett/*       Tree, Successor, Approximation, Monoid, Replay
       \                  /
        \    SMTree + shape subspaces
         \       /
          ShapeFiniteInduction
         /                   \
ShapeFiniteRamsey       FatTree/* → ShapeEllentuckRamsey
         \                   /
          ShapeFiniteCorollaries

SMTree + Algorithm 5.4 envelope modules
                    |
          V10/KptCompleteSMTree
                    |
          V10/H* finite numerical geometry
                    |
          V10/GPlus*, final Section 6 transfer (ongoing)
```

The diagram records proof dependence conceptually. The main project root
and the V10 aggregation now use *minimal transitive import frontiers*: 8
rather than 96 direct root imports, and 16 rather than 231 V10 imports
(after deleting four obsolete printer-only modules).
The initial import-only refactor preserved exactly the checked module
reachability. A separate follow-up removes four source files containing only
`#print axioms` (no proofs or definitions); their unique named checks now
live in maintained `scripts/CheckV10M2*.lean` checker files. All actual proof
dependencies remain reachable. The frontiers
are not compatibility layers; concrete new proof endpoints may be added
directly when their imports are not already reachable.

## Main interfaces

**Tree and monoid:** `SuccessorTree.Tree`, `SuccessorTree.Successor`, `SuccessorTree.Approximation`, `SuccessorTree.Monoid`, `SuccessorTree.Canonical`. The tree is a `LevelTree`; `STree` describes successors/labels; `SMTree` packages the distinguished monoid and assumptions M1–M3. This separation is intentional. The abstract Ramsey argument should not assume concrete model-specific finite-age properties.

**Starred Hales–Jewett:** `SuccessorTree.HalesJewett.*` develops variable words, fusion/forcing, alphabet induction and the actual finite starred Hales–Jewett endpoint `starHJ_finite`. Historical texts claiming that starred HJ is an unproved global input are obsolete.

**Direct Ramsey route:** `SuccessorTree.ShapeFiniteRamsey` obtains one-dimensional homogeneity from the large-set fusion. `SuccessorTree.ShapeFiniteInduction` supplies the shared relative reduction and induction. The public endpoint is `shapePreservingRamsey`.

**Fat-tree route:** `SuccessorTree.FatTree.A4ReviewComplete` proves `fatTreeA4` and `fatTreeEllentuck` without adding a pruning/saturation/pigeonhole hypothesis. `SuccessorTree.ShapeEllentuckRamsey` uses this route for the same finite-dimensional theorem. Both routes share the induction **but not** the one-step Ramsey input. The dependency-sensitive checker `scripts/CheckShapeProofRoutes.lean` distinguishes them.

**Finite shape results:** `SuccessorTree.ShapeFiniteBounds` and `SuccessorTree.ShapeFiniteCorollaries` provide bounded and exact finite-terminal corollaries. Their compactness and padding steps are not arbitrary-strength infinite theorems.

**Envelope construction:** `SuccessorTree.Envelope*` builds the `SMTree` envelope machinery and Algorithm 5.4-style invariants. These modules should continue to expose abstract input/output statements rather than importing the `V10` finite model.

**Normalized v10 application:** `SuccessorTree.V10.KptCompleteSMTree` proves M1, corrected M2 with finite common-socle age, and literal M3. The `V10/I3*`, `V10/H*`, and `V10/GPlus*` modules are specialized to finite relational-type records and the Section 6 counting/application proofs.

**Auxiliary families:** `SuccessorTree.FreeAncestral*` supplies a separate
concrete model/check. The previously documented
`SuccessorTree/NonPrecompact/` directory does **not** exist in this
repository; the BANANA lower-bound projects are separate and must not be
silently advertised as successor exports. Neither application justifies
adding model-specific assumptions to `SMTree`.

## Source organization recommendations

- Make the main public endpoint modules easy to import. Prefer `lake build SuccessorTree.ShapeFiniteRamsey` or a single `V10` endpoint while developing a proof, not a full umbrella rebuild after each edit.
- Preserve a lightweight abstract layer that depends on Mathlib and the pinned Todorčević Ramsey-space library, not on `V10`.
- Keep proof-implementation helpers below final theorem modules. Avoid cycles or exporting a convenient implementation assumption as a theorem premise.
- Move truly abandoned branches out of the active source tree after the import-graph audit and downstream check, not by deleting every file with `Review` or `Experimental` in its name.
- `SuccessorTree.Core` is the lightweight abstract endpoint; the root umbrella
  is a complete build/development convenience. We permit breaking public
  proof-implementation APIs and deleting redundant wrappers. Update any
  actual downstream consumers directly rather than retaining compatibility
  shims. Preserve the *types and axiom provenance of verified theorems* until
  mathematical generalization is undertaken separately.

For the detailed two-route dependency and conventions see [shape proof routes](../shape-proof-routes.md).

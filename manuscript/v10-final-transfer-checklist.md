# Successor v10: the remaining G+ action and Ramsey transfer

15 October 2026. Review/tracking only; no author mathematical prose is changed.

## Current proof boundary

PR 463, exact head `de5913638fb72164432a8232cbde2c9f02fe5fc7`, has completed successful Lean/transitive-axiom run 38728699198 and V10 run 38728699434. This proves the actual canonical countable C+ to G+ prefix-code embedding, including the numerical H+ specialization. The merge tool call was blocked in this continuation; the PR has not been merged by an alternative mechanism.

PR 464 is stacked on that checked head. It contains candidates for the exhaustive nondecreasing-size enumeration and the ordered H-to-G-omega embedding. Its review note is `manuscript/v10-Gplus-enumeration-review.tex`. Check exact-head full Lean and transitive axioms before treating these candidates as certified.

The new enumeration is explicit: let the width of layer n be the number of valid codes of size n+1. The canonical prefix map provides an inhabitant of every layer. Rank a numbered vertex (n,i) by the sum of all earlier widths plus i. The rank is injective; the least cumulative upper endpoint supplies a preimage for every natural number. Thus the inverse rank is a bijection whose sizes do not decrease. Composing inverse-enumeration rank with the canonical prefix-code map is strictly increasing, because its code sizes are v+1.

## The next manuscript bridge is Observation 6.42

The available reviewed v10 text defines v(S,T) as the ordinary initial code of T of size level(S)+1, for S properly below T. The exact next obligations are:

1. Represent every valid G+ vertex by such a pair of actual admissible partial types. Use the existing neutral-cap construction and hereditary admissibility, not a new representation hypothesis.
2. Prove the displayed equivalence in Observation 6.42: equality of the represented G+ vertices holds if and only if equality holds after applying a genuine Kpt shape map to both pairs. Full ordinary L+ records, including E and absent atoms, matter.
3. Define the resulting well-defined injective action Phi_F on G+ and prove every induced unary, diagonal, directed-binary and E identity. Prove compatibility with identity, composition and finite restrictions as required by the colouring pullback.
4. Connect the actual Algorithm 5.4 envelope of the represented seed types to coverage of the corresponding G+ vertices. The already proved numerical level bound alone does not establish this representation step.
5. Prove finiteness of the palette of represented copies in the bounded type levels, and apply the existing finite shape Ramsey theorem to their finitely many colourings. Check the exact finite-approximation domain conventions at the boundary (level < b versus level <= b); do not silently shift indices or assume an action of an insufficiently long approximation.
6. Use K-universality for the ordered G-omega-to-K embedding, compose the concrete K-to-H and H-to-G maps with Phi_F, and prove the final ordered self-embedding and colour bound.

Do not abbreviate items 1--5 as an already checked final assembly.

## Existing proofs to reuse

- `NonedgePaddingSocleCap.lean`: genuine admissible capped nodes for finite partial structures.
- `M2TwoTypeImageCompatibility.lean`, `shapeMap_preserves_source_compatibility`: common source ordinary L+ socles yield common image ordinary L+ socles under any genuine ShapeMap.
- `M2ShapeMapCompatReflection.lean`, `shapeMap_reflects_source_compatibility`: reflect equality using the full retained source records.
- `ShapeMapFullRecovery.lean`, `shapeMap_recovers_complete_record`: recover every source atom at retained level-map coordinates.
- `M2CapRetainedAtoms.lean`: actual ordinary binary and singleton records in one capped image.

These are inputs, not a claim that Observation 6.42 has already been formalized. Reuse the existing results rather than restarting their M2 proofs.

## Order caution

The enumeration orders every smaller size before every larger size, with arbitrary choices within one size. Do not add an unnecessary claim that every induced shape action preserves that arbitrary tie order on all of G-omega. The final ordered K copy is supported on the strictly increasing-size prefix chain; establish its order there using the common strictly increasing level map.

## Editorial and scope constraints

Stay with the existing v10 finite unary/binary/diagonal representation, no higher arity and no relaxation of the successor axioms. Do not attach artificial E to L-only age witnesses. Keep review notes and accurately scoped validation markers in Git. The available PDF is a reviewed snapshot with historical validation notes, not permission to replace the author's current editable source. Theorem 6.26 remains open as a formalization endpoint until all the listed bridges and the final bound are checked.

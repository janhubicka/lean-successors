# Successor v10: the remaining G+ action and Ramsey transfer

15 October 2026. Review/tracking only; no author mathematical prose is changed.

## Current proof boundary

PR 463, exact head `de5913638fb72164432a8232cbde2c9f02fe5fc7`, has completed successful Lean/transitive-axiom run 38728699198 and V10 run 38728699434. This proves the actual canonical countable C+ to G+ prefix-code embedding, including the numerical H+ specialization. The merge tool call was blocked in this continuation; the PR has not been merged by an alternative mechanism.

PR 464 is stacked on that checked head. Its corrected proof head
`17cfed7cb173c52b0aa40582470277126ac32539` PASSED the complete
Lean/transitive-standard-axiom workflow 38737960940 and the V10 counting/axiom
workflow 38737960658. This now certifies the explicit exhaustive
size-nondecreasing G+ enumeration and ordered H-to-G-omega induced embedding.
The first two CI failures were respectively an ambiguous nested subtype
projection and an unapplied-lambda normalization; the corrections changed no
theorem statement. The review-only note is
`manuscript/v10-Gplus-enumeration-review.tex`. PR 464 remains open because
its predecessor PR 463 could not be merged by the connector in this session.

PR 465, candidate head `b77e3ee98e7e8208761e42cf8e519cd8960bc3e0`,
adds the genuine image-cut foundation of Observation 6.42. It defines the
cut lambda(|A|-1)+1, proves it is inside the image of the canonical neutral
cap, takes an actual admissible ancestor and constructs a genuine valid
G+ vertex by its finite ordinary socle. Its full Lean run 38738911691 passed;
the focused V10 run 38738911810 must be checked before marking GREEN.
The review note is `manuscript/v10-Gplus-shape-action-review.tex`.

PR 466, candidate head `9ca7377d4241e3baa1a1c0945b1fa53ff85616e6`,
introduces `GPlusOrdinaryCode.lean`: an intrinsic finite ordinary code for a
Kpt partial-type record, comparison with any chosen admissibility witness,
and equality of genuine G+ vertices under `SameOrdinaryAtCut`.
These bridge results are pending exact-head Lean and transitive-axiom CI.
Its review note is `manuscript/v10-Gplus-ordinary-code-review.tex`.
None of these certificates yet proves the full well-defined induced
ShapeMap action, envelope representation or final Ramsey transfer.

The enumeration is explicit: let the width of layer n be the number of valid codes of size n+1. The canonical prefix map provides an inhabitant of every layer. Rank a numbered vertex (n,i) by the sum of all earlier widths plus i. The rank is injective; the least cumulative upper endpoint supplies a preimage for every natural number. Thus the inverse rank is a bijection whose sizes do not decrease. Composing inverse-enumeration rank with the canonical prefix-code map is strictly increasing, because its code sizes are v+1.

## The next manuscript bridge is Observation 6.42

The available reviewed v10 text defines v(S,T) as the ordinary initial code of T of size level(S)+1, for S properly below T. The exact next obligations are:

1. Represent every valid G+ vertex by such a pair of actual admissible partial types. Use the existing neutral-cap construction and hereditary admissibility, not a new representation hypothesis.
2. Prove the displayed equivalence in Observation 6.42: equality of the represented G+ vertices holds if and only if equality holds after applying a genuine Kpt shape map to both pairs. Full ordinary L+ records, including E and absent atoms, matter.
3. Define the resulting well-defined injective action Phi_F on G+ and prove every induced unary, diagonal, directed-binary and E identity. Prove compatibility with identity, composition and finite restrictions as required by the colouring pullback.
4. Connect the actual Algorithm 5.4 envelope of the represented seed types to coverage of the corresponding G+ vertices. The already proved numerical level bound alone does not establish this representation step.
5. Prove finiteness of the palette of represented copies in the bounded type levels, and apply the existing finite shape Ramsey theorem to their finitely many colourings. Check the exact finite-approximation domain conventions at the boundary (level < b versus level <= b); do not silently shift indices or assume an action of an insufficiently long approximation.
6. Use K-universality for the ordered G-omega-to-K embedding, compose the concrete K-to-H and H-to-G maps with Phi_F, and prove the final ordered self-embedding and colour bound.

Do not abbreviate items 1--5 as an already checked final assembly.

## Concrete proof route for the G+ action — not yet Lean-checked

Let A be a valid finite code of positive size a. Let U_A be the level-a admissible neutral-cap type obtained from `NonedgePadding.socleCapNode`. Its ordinary code is A. Prove once that it depends only on A's finite tables, not on the raw witness's off-carrier values. Also prove that if A is the size-a prefix of B, then U_A is the level-a prefix of U_B: every ordinary atom is copied, the cap's singleton is neutral, and all ordinary-to-tip E atoms are prescribed identically.

For a genuine shape map F with common strictly increasing level map lambda, define Phi_F(A) to be the ordinary code of F(U_A) restricted to lambda(a-1)+1. This cut is inside F(U_A), since lambda(a-1)<lambda(a). Admissibility of F(U_A) and hereditary restriction give a genuine valid G+ vertex. Its last coordinate is lambda(a-1).

To identify this definition with any representative v(S,T)=A, put a=level(S)+1 and Q=T restricted to level a. Then Q and U_A have the same full ordinary L+ socle A. The existing `shapeMap_preserves_source_compatibility` gives equality of the full image ordinary socles of F(Q) and F(U_A), both of level lambda(a). Moreover F(Q) is a prefix of F(T). Restricting these equal image socles to lambda(a-1)+1 gives

    v(F(S),F(T)) = Phi_F(A).

Thus the forward implication of Observation 6.42 is independent of the chosen representative. For injectivity, equality Phi_F(A)=Phi_F(B) first forces a=b by strict increase of lambda. Every retained coordinate lambda(i), i<a, lies below lambda(a-1)+1. Reindexing all four finite atomic tables at those retained coordinates and applying `shapeMap_recovers_complete_record` recovers A=B. This supplies the reverse implication.

For A properly below B, cap-prefix coherence and prefix preservation by F show Phi_F(A) is properly below Phi_F(B). The converse follows by reindexing the retained finite tables. Hence incomparability is also reflected. On comparable pairs, the G+ relation definition reads the image atoms at lambda(a-1),lambda(b-1) inside the image cap of B. Full record recovery identifies them with the original two last-coordinate atoms in B, in both orientations and for both Boolean values. Unary and diagonal atoms use the same argument at one last coordinate. Incomparable pairs have no binary or E tuples on either side. This proves an induced L+ embedding, not just preservation of positive relations.

Composition and identity should then be proved through the representative identity above: applying G and then F to the pair (S,T) is the same as applying F composed with G. For finite approximations, explicitly ensure both types in the representative pair lie in the approximation domain before using this identity as a colouring definition.

The cap-code construction, its prefix coherence, its image-prefix validity and the exact retained-index identities still need formalization. The argument above is a proof plan using established lemmas, not a completed Observation 6.42 certificate.

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

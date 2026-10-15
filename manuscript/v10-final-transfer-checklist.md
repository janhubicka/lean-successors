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
G+ vertex by its finite ordinary socle. Its full Lean run 38738911691 AND focused V10 counting/axiom run
38738911810 both PASSED on this exact head. The local image-cut
foundation is GREEN; this does not make the full action GREEN.
The review note is `manuscript/v10-Gplus-shape-action-review.tex`.

PR 466, intrinsic Kpt ordinary finite codes:
exact head `2c0cc2315512f4d801e5f70a84787f5d4336f32e`,
full Lean 38741444447 and V10 standard-axiom/counting 38741444382
BOTH PASSED. This proves literal equality with the code extracted from
a genuine admissibility witness; representative choice cannot change
the ordinary finite tables.

PR 467, ordinary-code equality in both directions:
exact head `5dbe5a328fa29c4324a2d7e3f2cd10b794556216`,
full Lean 38741448941 and V10 38741449000 BOTH PASSED.
Equality of four induced finite atom tables is equivalent to
SameOrdinaryAtCut and remains compatible under genuine ShapeMaps.

PR 468, genuine Kpt representing pairs v(S,T):
exact head `8c6c11caa8278543ee01df70c2529e10a3fbb255`,
full Lean 38742947049 and V10 38742946967 BOTH PASSED.
Its scope is the actual pair/cut/image-size construction, not the
complete induced G+ action.

PR 469, canonical neutral-cap representative of every finite G+ code:
exact head `7a7f131b2afa2e3e7bdfa0823f5e4359a2da035a`,
full Lean 38745208463 and V10 38745208189 BOTH PASSED.
This verifies v(canonical(A))=A, including the literal full ordinary
neutral-cap code, and hence surjectivity of the representing-pair map.

PR 470, compatibility of Kpt prefix and G+ finite-code restriction:
exact corrected head `aaeddbe58f6b9b9041e7b92dd9749e238b681f7d`,
full Lean 38747112763 and V10 38747112704 BOTH PASSED.
The final correction replaced an invalid dependent rewrite with direct
restriction of all four atomic tables.

PR 471, shape-map transport of equal ordinary finite codes:
exact candidate head `8d0894f793491062c0a84d61fb14196d377742a9`.
Its full Lean run 38748924400 PASSED; V10 focused audit
38748924343 remained in progress at the last check.
The image-record cast is handled by an explicit equal-level helper.

PR 472, the image representing pair as a prefix of the full image
ordinary code: candidate head `fb8b26d262caa605bf5b15335175be7b2a81e1d7`.
The first proof error was only the orientation of a level-map equality;
it was corrected without changing the statement. CI is pending.
Review note: `manuscript/v10-Gplus-image-pair-restriction-review.tex`.

PR 473, independence of the induced G+ image from the representing
Kpt pair: candidate head `1638cb89d747c6969ae18910c1f656c8e1032454`.
It combines the common image cut, complete ordinary code compatibility,
and the two image-prefix identities to establish
v(F(S),F(T)) = gPlusShapeImage F (v(S,T)).
No new action interface is postulated. CI is pending.
Review note: `manuscript/v10-Gplus-representative-independence-review.tex`.

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

## Post-well-definedness verification route (15 October continuation)

PR 474, candidate `v10-Gplus-shapemap-action-laws-20261015`, extracts
identity and composition of the G+ image construction directly from
`ShapeMap.id`, `ShapeMap.comp`, canonical representing pairs and
PR 473's forward well-definedness lemma. A candidate review-only TeX note
is in `manuscript/v10-Gplus-shapemap-action-laws-review.tex`. Require
exact-head full Lean and transitive standard-axiom CI. This does not
certify injectivity or the induced relational action.

The remaining **reflection** part of Observation 6.42 should NOT use
`shapeMap_reflects_source_compatibility` directly on the full image
partial types: equality of two G+ output vertices supplies only equality
of the prefixes at cut d=lambda(n-1)+1, whereas the full image cap
has level lambda(n), which may be larger. The correct bridge is the
full **retained-coordinate recovery** lemma already verified in
`ShapeMapFullRecovery.lean`.

Concretely, for any genuine G+ vertex A of size n>0 and genuine
ShapeMap F, let lambda be the strictly increasing Kpt level map and
d=lambda(n-1)+1. The output vertex Phi_F(A) has size d and its full
finite code is the prefix of the image cap at d (PR 472).
For each old coordinate i<n, lambda(i) <= lambda(n-1)<d.
Thus the map
  rho_A : Fin n -> Fin d, i |-> lambda(i)
is well defined and strictly increasing.

Prove the retained-code identity, with literal equality of all four
finite atom tables:
  reindex(Phi_F(A), rho_A) = A.
It follows from `shapeMap_recovers_complete_record` on the genuine
canonical cap of A together with `canonicalCap_ordinaryCode` and
the image-prefix-code equality. The proof must compare both binary
directions and negative atoms, unary, diagonal and E; no weak
homomorphism suffices.

If Phi_F(A)=Phi_F(B), equality of output sizes first gives
lambda(|A|-1)=lambda(|B|-1), and strict monotonicity of lambda gives
|A|=|B|. The reindex functions rho_A and rho_B are then identical,
so applying the retained-code identity to their equal output tables
gives A=B. This proves injectivity and the reverse implication of
Observation 6.42 without any additional axioms.

To prove the induced relational identities for comparable A<B, use a
single genuine cap of B, recover its two last-coordinate atoms at
lambda(|A|-1),lambda(|B|-1), and use the prefix coherence/representation
lemmas to identify Phi_F(A) and Phi_F(B) with the corresponding
image vertices. For incomparable A,B, equality reflection of
prefix comparisons is needed to show their images remain incomparable,
so no new binary or E tuples arise. Record all absences as well as
positive facts.

This is a precise English proof route, not a completed Lean certificate.
After it is checked, continue with the envelope/finite-palette/colour
assembly of Theorem 6.26, reusing the already validated uniform
Algorithm 5.4 envelope bound.

## Exact-head validation progress: retained recovery and neutral caps (15 October 2026)

These stages extend Observation 6.42 but DO NOT by themselves certify its complete
induced relational action or Theorem 6.26.

- PR #475, exact head `4da64744c56fc3d359d37c07f901dae22fd22da4`:
  complete retained-coordinate index and four-table reindexing construction,
  GREEN full Lean and V10 counting/transitive-axiom workflows.
- PR #476, exact head `ff80754c9212951c6467f875c3a0486e7d193870`:
  `shapeMap_recovers_ordinaryCode` from the already checked
  `shapeMap_recovers_complete_record`, including after a short image
  prefix containing all retained coordinates. GREEN full Lean run
  38755792644 and V10 run 38755792740.
- PR #477, exact head `b197c26ff738890f05df5d08eb5607cf10dd121c`:
  canonical cap specialization, including literal
  `shapeImageRetainedCode F A = A.val`, GREEN full Lean run
  38756498434 and V10 run 38756497923.
- PR #478, exact head `20aad24d1d9d890ab061791d198f563367fbf0fa`:
  injective `gPlusShapeImage` and the full iff of equality of
  arbitrary genuine representing pairs under F. GREEN full Lean
  38756953609 and V10 counting/transitive-axiom 38756953677.
  This closes BOTH logical directions of equality in Observation 6.42,
  but NOT the induced L+ relation identities.

New candidates, pending exact-head full builds and axiom audits:

- PR #479, `GPlusNeutralCapType.lean`: an explicit complete neutral
  terminal Kpt type determined by the four ordinary source tables,
  commuting with initial prefix restriction. A first build detected only
  two socle-index arithmetic proof failures; their source bounds are now
  exposed explicitly in corrected branch head
  `86a6d9f8af899db194a02292beb3919145d043cb`.
- PR #480, `GPlusCanonicalCapPrefix.lean`: literal equality between
  the actual chosen-witness cap and the deterministic full neutral Kpt
  node of a finite G+ code, and preservation of genuine cap prefixes.
  Current branch integrates the neutral-cap bound repair.
- PR #481, `GPlusShapeImagePrefix.lean`: source code sizes determine
  image sizes strictly; prefix preservation from cap prefixes; reflection
  from same-length prefix uniqueness plus PR #478 injectivity.
  If checked, this also reflects incomparability, so no new binary or
  E relations can be created on unrelated G+ branches.

The next substantive theorem after the cap-prefix stages is exact
preservation of both directed binary and E atoms on comparable
G+ pairs. Use one genuine larger canonical cap, the already proved
shape-map retained-coordinate recovery, and the prefix coherence
above. Unary and diagonal atoms are similarly read at the retained
last coordinate. Only once these are checked does Observation 6.42
supply the induced action used by the finite-colouring pullback.

Keep review-only TeX notes in Git. Do not change author proof prose,
weaken axioms, add higher arity or manufacture E on L-only witnesses.

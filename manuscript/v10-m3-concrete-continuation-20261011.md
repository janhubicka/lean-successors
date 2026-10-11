# V10 M3 concrete duplication — cumulative proof continuation

Checkpoint: 11 October 2026. This is a **review/TODO file**. The author's
main TeX prose is frozen, and the corrected-B3 patch and four other
mathematical repairs must not be automatically reapplied.

## Previously verified

- PR #230: full Lean plus focused named-axiom audit verified the finite
  irreducible clone projection, including all directed Boolean atoms,
  unary/diagonal data and forbidden singletons.
- PRs #231–#233: checked clone-data implication for corrected finite
  L-age B3, and the upper terminal-letter/lower shortened-parameter
  atomic transport. The early fixed global free-cut hypothesis of
  PR #231 is only a conditional helper, **not** an M3 premise.
- The normalized prescribed one-gap boring extension (PRs #226–#228)
  is already checked by both focused and public root library builds.

## Actual finite M3 insertion track — ALL NEW ENDPOINTS PENDING CI

1. **#241** `M3MiddleInsert.lean`: insert the clone at ell>n in an
   actual enumerated L+ model A, with d=fl_A(n). Old-old atoms are
   preserved; both lower directed pairs with x<d are cloned, pairs
   to d<=x<ell are absent, and upper directed pairs are cloned only
   when ell<=fl_A(x) (the required E3 gate). Reuses generic
   `insertPartial` for E spacing/downward and linkage.
2. **#242** `M3LinkedProjection.lean`: weaken the finite irreducible
   projection theorem so that upper copying is required only for upper
   vertices genuinely L-linked to the inserted clone. In an
   irreducible forbidden copy through ell every other upper vertex
   has such a link. A restricted-carrier argument recovers the earlier
   strong finite projection theorem without an E-age witness.
3. **#243** `M3MiddleLinkedData.lean`: show the **actual** gated
   finite insertion satisfies precisely the linked-only clone data,
   deriving that the gate must be open whenever the new clone is
   linked to a given old upper vertex.
4. **#244** `M3MiddleAvoidance.lean`: forbidden copies away from ell
   pull back to A; copies containing ell project to a forbidden copy
   in the deletion. Therefore the literal inserted finite L-structure
   remains forbidden-free under the normalized irreducible family.
5. **#245** `M3MiddleFreeCut.lean`: exact `insertE` identity,
   freeLevel(new ell)=fl_A(n), old cut transport and level ell+1 for
   the shifted distinguished vertex.
6. **#246** `M3MiddleTarget.lean`: literal preservation of every
   old prefix through ell in the complete L+ type, admissibility of
   the shifted output node, and its restriction equality to the old
   source. This is the finite existence/B1 step.
7. **#247** `M3MiddleLetter.lean`: the complete terminal L+ Sigma
   letter at the new crossing (ell,shift(v)) agrees with the old
   n-th letter (n,v), including all four E pairs and present/absent
   directed L and singleton facts.
8. **#248** `M3MiddleParameter.lean`: the newly inserted ordinary
   vertex's entire L+ parameter type through d equals the old n-th
   parameter type through d, including E; the canonical
   empty/singleton parameter list is therefore identical.
9. **#249** `M3MiddleCanonicalStep.lean`: the actual forbidden-free
   inserted witness gives a genuine Kpt cover; the canonical step's
   parameter list and Sigma letter are the old n-th inputs, by
   exact input extraction and uniqueness.

**Verification status:** each is currently a draft proof candidate
with named-axiom audit scripts. The GitHub Lean/focused jobs for this
series have been queued; do not mark the above nine items GREEN based
on prose or on the successful unrelated default-root builds.
The independent bounded Python regression for the actual gated finite
model passed 78,742 insertions, 3,814,372 E3 atom checks and 110,676
irreducible-copy projections; this is useful negative testing only.

## Genuine global M3 proof obligations after the finite track

A. For every admissible level-ell source T, take the canonical
   empty/singleton parameter list and Sigma letter of its old n-th
   crossing T|_(n+1). Use the newly proved finite canonical step to
   establish that `canonicalKptSucc family T p_n(T) c_n(T)` is
   **defined and admissible**, independent of an arbitrary finite
   witness. Functional uniqueness of the successor should eliminate
   representation choices, not become a new axiom.

B. Assemble `PrescribedBoringData` on all relevant level-ell source
   records. B1 is full-record restriction, not merely L-reduct
   agreement. B2 says that compatible old ORDINARY L+ socles yield
   compatible output ordinary socles; old n's free cut is determined
   by ordinary E data, and output lower columns by the same old
   ordinary L/E data. This last coherence theorem is not yet formalized.

C. Use repeated canonical input records to derive corrected B3 in
   the **finite ordered L-only** formulation. The free cut is
   source-dependent; avoid importing the stronger fixed-d shortcut
   as a global M3 assumption.

D. Apply the verified prescribed boring extension to obtain the
   genuine shape-preserving one-level skip/duplication map, and verify
   the manuscript's M3 factorization and source-level clauses exactly.

The corrected-B3 necessity/decomposition for M2, the finite-L
I3/signature bridge, and the original-language adapter (including
nullary and diagonal symbols) remain independent OPEN items.

## Adversarial safeguards

* E3 upper gating is essential, and forbids unconditional copying
  to unlinked upper vertices in arbitrary inserted ambient models.
* Every irreducible forbidden copy through ell is linked to ell,
  which is the only setting requiring upper copy identities in PR #242.
* Do not impose E or a partial-structure completion on finite
  corrected-B3 L-age witnesses.
* No `sorry`, new `axiom`, or abstract successor law may be used
  to replace the remaining canonical Kpt graph proof.
* Keep the first eight managed V10 TODO groups and all author prose
  byte-identical; change the ninth only after decisive CI evidence.

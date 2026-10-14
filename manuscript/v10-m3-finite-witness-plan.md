# V10 M3: finish the actual finite witness, then the global duplication

Proof-development note, 11 October 2026. **The main V10 manuscript is frozen.**

## Already checked

- PR 230: finite L-only projection of an irreducible copy containing a
  middle-inserted clone into the structure without that clone.
- PRs 231–233: corrected-B3 implication under clone data and literal
  upper terminal-letter/lower parameter atomic comparisons.
- PRs 234–239: staged canonical input/step-graph reductions, checked
  status tracked separately. Do not conflate a stage or a successful
  default root build with exact-head focused axiom verification.

## Construction staged here (PR 241)

For a forbidden-free enumerated L+ partial structure A, an old ordinary
vertex n<ell and ell<=A.size, take d=fl_A(n). The new coordinate ell has
unary/diagonal/loop data copied from n, copies BOTH directed lower
binary values from n only for x<d, and has neither directed binary
relation to x in [d,ell). For old upper x>=ell the two values are copied
from n only when ell<=fl_A(x), otherwise both are false.

The gate is essential: it ensures the linked-pair E3 axiom in the inserted
partial structure. The generic `insertPartial` already handles transported
E cuts, spacing and downward closure; `M3MiddleInsert.lean` instantiates
its finite interface. The independent bounded regression
`scripts/check_v10_m3_middle.py` also tests E3 and induced-copy
projection, but is not a substitute for Lean.

## Next finite-age proof

1. Strengthen the existing projection interface so that **upper**
   copying is required only for a vertex which is L-linked to ell in
   either direction, while the lower no-link/copy laws remain exact.
   An irreducible forbidden copy containing ell is linked to ell at
   every other vertex. This is all the projection actually needs.
2. For the concrete gated insertion B, derive that linked upper
   vertices necessarily satisfy ell<=fl_A(u). On those vertices,
   copying of both directed atoms to n is exact. At ungated vertices
   the inserted clone has no link, so they cannot occur in a
   nontrivial irreducible copy containing ell.
3. Split a forbidden copy in B according to whether it uses ell.
   Away from ell, use `IsLInsertion.realizes_away_projects` to the old
   forbidden-free A. Through ell, apply the linked-upper clone
   projection into B without ell, then the same old-copy pullback.
   Forbidden singletons project to the old n because singleton
   fields are copied.
4. Derive B's old-vertex transported free levels and identify the
   complete new type at the shifted distinguished vertex v with
   the canonical successor of the source type at level ell whose
   parameter and terminal letter repeat those of its old n-th
   crossing. This requires equality of complete L+ records, not
   only the L-reduct.

## Global M3 consequence after the finite lemma

Use the S2 uniqueness of the actual `canonicalKptSucc` graph to make
the duplicate f(T) independent of the finite witness for T. Check
B1 (restriction to T), B2 (ordinary-socle compatibility, including
the copied free cut d(T)), admissible prescribed targets and corrected
B3. The latter should use the source-dependent-cut / repeated-step
theorem, never the globally fixed-cut shortcut.

Then apply the already verified prescribed boring-extension theorem
to obtain an M3 map in KptM with the required duplicated coordinate.
Neither M2 necessity/decomposition, I3 finite-L signature witnesses,
nor the language adapter follows automatically.

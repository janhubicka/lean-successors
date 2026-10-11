import SuccessorTree.V10.CommonSocleType
import SuccessorTree.V10.PartialTypeRestriction

/-!
# A first disagreement of complete partial types is a binary disagreement

This is the converse needed to turn a genuine nontrivial tree meet into the
positive-generation trace theorem.  Both types come from ONE enumerated
partial structure, not two arbitrarily chosen age witnesses.  As long as
both full L+ records exist through d+1 (d+1 is at most both free levels),
E and the old socle are identical; a first new difference must therefore
involve a directed binary atom joining the new position d to the type vertex.

The hypothesis of common singleton type is not introduced as an extra
axiom: equality of the complete predecessors through d implies equality
at level zero by the already proved restriction theorem.

This module still does not identify the actual Kpt ancestor operation
with the full extracted types. That will be the last structural interface
when applying the generic LevelTree meet theorem.
-/

namespace SuccessorTree.V10

/-- Full record equality at any cut includes equality at the root
(level zero). This uses the actual induced restriction of ALL L+ atoms. -/
theorem sameAmbient_root_of_prefix_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v w d : Nat)
    (hPrev : A.partialTypeAt d v = A.partialTypeAt d w) :
    A.partialTypeAt 0 v = A.partialTypeAt 0 w := by
  have h := congrArg
    (fun T : PartialTypeWithE d db du dd =>
      T.restrict (Nat.zero_le d)) hPrev
  simpa only [EnumeratedPartialStructure.partialTypeAt_restrict] using h

/-- If two extracted complete L+ predecessors agree through d but
disagree at d+1, with both cuts inside the E-socle, then a directed
binary atom involving the distinguished vertex first differs at d.

The E relation itself cannot be the cause: below both free levels
all socle-to-type E edges are present, reverse edges absent, and
E on the old socle is shared because the ambient structure is shared. -/
theorem sameAmbient_first_type_difference_has_binary_witness
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v w d : Nat)
    (hv : d + 1 ≤ A.freeLevel v)
    (hw : d + 1 ≤ A.freeLevel w)
    (hPrev : A.partialTypeAt d v = A.partialTypeAt d w)
    (hNext : A.partialTypeAt (d + 1) v ≠ A.partialTypeAt (d + 1) w) :
    (∃ r : Fin db, A.L.binary d v r ≠ A.L.binary d w r) ∨
    (∃ r : Fin db, A.L.binary v d r ≠ A.L.binary w d r) := by
  classical
  have hRoot := sameAmbient_root_of_prefix_eq A v w d hPrev
  have hBefore : SameAmbientCrossType A v w d :=
    sameAmbient_cross_of_partialType_eq A v w d hPrev
  by_contra hNoDiff
  have hForward : ∀ r : Fin db,
      A.L.binary d v r = A.L.binary d w r := by
    intro r
    by_contra hneq
    exact hNoDiff (Or.inl ⟨r, hneq⟩)
  have hBackward : ∀ r : Fin db,
      A.L.binary v d r = A.L.binary w d r := by
    intro r
    by_contra hneq
    exact hNoDiff (Or.inr ⟨r, hneq⟩)
  have hNextCross : SameAmbientCrossType A v w (d + 1) := by
    constructor
    · intro x r
      by_cases hx : x.val < d
      · exact hBefore.1 ⟨x.val, hx⟩ r
      · have heq : x.val = d := by omega
        simpa only [heq] using hForward r
    · intro x r
      by_cases hx : x.val < d
      · exact hBefore.2 ⟨x.val, hx⟩ r
      · have heq : x.val = d := by omega
        simpa only [heq] using hBackward r
  exact hNext ((sameAmbient_partialType_eq_iff_cross A v w
    (d + 1) hv hw hRoot).2 hNextCross)

/-- A first new binary mismatch is *equivalent* to a first new
complete-type mismatch once the previous complete prefixes agree
and the next cuts stay below both free levels. The result includes
both relation orientations and handles languages with no binary
symbols (then the asserted mismatch cannot occur). -/
theorem sameAmbient_first_type_difference_iff_binary
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v w d : Nat)
    (hv : d + 1 ≤ A.freeLevel v)
    (hw : d + 1 ≤ A.freeLevel w)
    (hPrev : A.partialTypeAt d v = A.partialTypeAt d w) :
    (A.partialTypeAt (d + 1) v ≠ A.partialTypeAt (d + 1) w) ↔
      ((∃ r : Fin db, A.L.binary d v r ≠ A.L.binary d w r) ∨
       (∃ r : Fin db, A.L.binary v d r ≠ A.L.binary w d r)) := by
  constructor
  · exact sameAmbient_first_type_difference_has_binary_witness
      A v w d hv hw hPrev
  · intro hDiff
    have hRoot := sameAmbient_root_of_prefix_eq A v w d hPrev
    have hBefore : SameAmbientCrossType A v w d :=
      sameAmbient_cross_of_partialType_eq A v w d hPrev
    exact (sameAmbient_first_fullType_difference A v w d
      hv hw hRoot hBefore hDiff).2

end SuccessorTree.V10

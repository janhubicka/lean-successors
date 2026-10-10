import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# Exact free levels after one-coordinate insertion

The one-coordinate partial structure from LocalAgePartialInsertion stores E
only through an explicit initial-segment cut. Hence its canonical free level
is not extra data: it is exactly insertedCut. This is the insertion analogue
of LevelRemovalFreeCut and is the bookkeeping needed to make the local-age
construction uniform on partial types.
-/

namespace SuccessorTree.V10

/-- The explicit transported cut is a genuine first missing E-coordinate. -/
theorem insertE_isFreeCut
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d v : Nat)
    (hv : v < A.size + 1) :
    IsFreeCut (insertE A ell d) v (insertedCut A ell d v) := by
  constructor
  · intro u hu
    exact (insertE_true_iff A ell d u v).2 ⟨hv, hu⟩
  · cases h : insertE A ell d (insertedCut A ell d v) v with
    | false => rfl
    | true =>
      have bad := (insertE_true_iff A ell d
        (insertedCut A ell d v) v).1 h
      exact False.elim ((Nat.lt_irrefl _) bad.2)

/-- The canonical free level of the actual inserted partial structure equals
the explicit transported cut, for every target coordinate in its carrier. -/
theorem insertPartial_freeLevel_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d : Nat) (D : InsertedLData db du dd)
    (hell : ell ≤ A.size) (hellPos : 0 < ell) (hd : d ≤ ell)
    (hdGate : d = 0 ∨ d < ell)
    (hBelow : ∀ x, x < ell →
      (∃ r : Fin db, D.incoming x r = true ∨ D.outgoing x r = true) →
      x < d)
    (hAbove : ∀ y, ell ≤ y → y < A.size →
      (∃ r : Fin db, D.outgoing y r = true ∨ D.incoming y r = true) →
      ell ≤ A.freeLevel y)
    (v : Nat) (hv : v < A.size + 1) :
    (insertPartial A ell d D hell hellPos hd hdGate hBelow hAbove).freeLevel v =
      insertedCut A ell d v := by
  let B := insertPartial A ell d D hell hellPos hd hdGate hBelow hAbove
  have hCut : IsFreeCut B.E v (insertedCut A ell d v) := by
    change IsFreeCut (insertE A ell d) v (insertedCut A ell d v)
    exact insertE_isFreeCut A ell d v hv
  exact freeCut_unique B.E v (B.freeLevel v) (insertedCut A ell d v)
    (canonicalFreeLevel_isFreeCut B.E B.spaced B.downward v) hCut

/-- At the inserted coordinate itself, its canonical free level is exactly d. -/
theorem insertPartial_freeLevel_at_inserted
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d : Nat) (D : InsertedLData db du dd)
    (hell : ell ≤ A.size) (hellPos : 0 < ell) (hd : d ≤ ell)
    (hdGate : d = 0 ∨ d < ell)
    (hBelow : ∀ x, x < ell →
      (∃ r : Fin db, D.incoming x r = true ∨ D.outgoing x r = true) →
      x < d)
    (hAbove : ∀ y, ell ≤ y → y < A.size →
      (∃ r : Fin db, D.outgoing y r = true ∨ D.incoming y r = true) →
      ell ≤ A.freeLevel y) :
    (insertPartial A ell d D hell hellPos hd hdGate hBelow hAbove).freeLevel ell = d := by
  rw [insertPartial_freeLevel_eq A ell d D hell hellPos hd hdGate hBelow hAbove ell (by omega)]
  exact insertedCut_at A ell d

/-- Every old vertex has precisely its old cut transported across the new
coordinate. In particular no arbitrary E-cut choices enter the insertion. -/
theorem insertPartial_freeLevel_old
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d : Nat) (D : InsertedLData db du dd)
    (hell : ell ≤ A.size) (hellPos : 0 < ell) (hd : d ≤ ell)
    (hdGate : d = 0 ∨ d < ell)
    (hBelow : ∀ x, x < ell →
      (∃ r : Fin db, D.incoming x r = true ∨ D.outgoing x r = true) →
      x < d)
    (hAbove : ∀ y, ell ≤ y → y < A.size →
      (∃ r : Fin db, D.outgoing y r = true ∨ D.incoming y r = true) →
      ell ≤ A.freeLevel y)
    (x : Nat) (hx : x < A.size) :
    (insertPartial A ell d D hell hellPos hd hdGate hBelow hAbove).freeLevel
        (insertAddress ell x) =
      if A.freeLevel x < ell then A.freeLevel x else A.freeLevel x + 1 := by
  rw [insertPartial_freeLevel_eq A ell d D hell hellPos hd hdGate hBelow hAbove
    (insertAddress ell x)]
  · exact insertedCut_insertAddress A ell d x
  · by_cases hxl : x < ell
    · rw [insertAddress_below ell x hxl]
      omega
    · rw [insertAddress_above ell x (by omega)]
      omega

end SuccessorTree.V10

import SuccessorTree.V10.M3MiddleAvoidance
import SuccessorTree.V10.LocalAgeFreeCut
import Mathlib.Tactic

/-!
# Exact E/free-cut transport in the literal finite M3 middle clone

This extracts the actual canonical free levels from the E predicate
of middleCloneInsertPartial. It does not assume that the new E column
is admissible; its spacing and downward closure follow from the
already constructed EnumeratedPartialStructure.

The new ordinary clone at ell has free level fl_A(n). The retained
old vertices have their free levels transported by the uniform
one-gap map. In particular a distinguished vertex v of old free level
ell has new free level ell+1, so its full target type is a genuine
one-step admissible candidate once forbidden avoidance is checked.
-/

namespace SuccessorTree.V10

/-- The E relation of the actual M3 constructor is the explicit
insertE with the unique old free cut fl_A(n). -/
theorem middleCloneInsertPartial_E_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell) :
    (middleCloneInsertPartial A ell n hell hn).E =
      insertE A ell (A.freeLevel n) := by
  rfl

/-- The new coordinate has precisely the copied earlier E-free cut. -/
theorem middleCloneInsertPartial_new_freeLevel
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell) :
    (middleCloneInsertPartial A ell n hell hn).freeLevel ell =
      A.freeLevel n := by
  let B := middleCloneInsertPartial A ell n hell hn
  have hCut : IsFreeCut B.E ell (A.freeLevel n) := by
    rw [middleCloneInsertPartial_E_eq A ell n hell hn]
    have hh := insertE_isFreeCut A ell (A.freeLevel n) ell (by omega)
    simpa only [insertedCut_at] using hh
  exact freeCut_unique B.E ell (B.freeLevel ell) (A.freeLevel n)
    (canonicalFreeLevel_isFreeCut B.E B.spaced B.downward ell)
    hCut

/-- Every old vertex has the exact old transported free cut,
including the case where its old cut is zero. -/
theorem middleCloneInsertPartial_old_freeLevel
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell)
    (v : Nat) (hv : v < A.size) :
    (middleCloneInsertPartial A ell n hell hn).freeLevel
        (insertAddress ell v) =
      if A.freeLevel v < ell then A.freeLevel v
      else A.freeLevel v + 1 := by
  let B := middleCloneInsertPartial A ell n hell hn
  have hV : insertAddress ell v < B.size := by
    have hIns := middleCloneInsertPartial_isLInsertion A ell n hell hn
    rw [hIns.size_eq]
    by_cases hlt : v < ell
    · rw [insertAddress_below ell v hlt]
      omega
    · rw [insertAddress_above ell v (by omega)]
      omega
  have hCut : IsFreeCut B.E (insertAddress ell v)
      (insertedCut A ell (A.freeLevel n) (insertAddress ell v)) := by
    rw [middleCloneInsertPartial_E_eq A ell n hell hn]
    have hh := insertE_isFreeCut A ell (A.freeLevel n)
      (insertAddress ell v) (by simpa only [B] using hV)
    exact hh
  have hCanonical :=
    freeCut_unique B.E (insertAddress ell v)
      (B.freeLevel (insertAddress ell v))
      (insertedCut A ell (A.freeLevel n) (insertAddress ell v))
      (canonicalFreeLevel_isFreeCut B.E B.spaced B.downward
        (insertAddress ell v)) hCut
  exact hCanonical.trans
    (insertedCut_insertAddress A ell (A.freeLevel n) v)

/-- At an admissible distinguished vertex with old cut ell, the
retained type vertex has cut ell+1 in the genuine inserted model. -/
theorem middleCloneInsertPartial_prescribed_vertex_freeLevel
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell)
    (v : Nat) (hv : v < A.size)
    (hOld : A.freeLevel v = ell) :
    (middleCloneInsertPartial A ell n hell hn).freeLevel
      (insertAddress ell v) = ell + 1 := by
  rw [middleCloneInsertPartial_old_freeLevel A ell n hell hn v hv,
    hOld]
  simp

end SuccessorTree.V10

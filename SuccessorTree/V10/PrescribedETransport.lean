import SuccessorTree.V10.PrescribedCorrectedB3
import SuccessorTree.V10.LocalAgeNeutralEColumn
import Mathlib.Tactic

/-!
# All E atoms under a genuinely non-neutral prescribed insertion

The E relation of the finite inserted partial structure depends ONLY on
its old E cuts, its insertion level ell and the prescribed new vertex's
canonical E-cut d. It does not depend on any L insertion bits.

The old/old E table is exactly preserved, including false atoms. The
inserted vertex has E-column x -> ell determined by x<d, whereas its
outgoing row to shifted old y is determined by ell <= freeLevel_A(y).
In particular, the E row is independent of d, the E-loop is false,
and the relevant condition at every old upper vertex is visible in the
FULL extracted L+ type record.

This is the non-neutral E interface needed for a uniform prescribed
Kpt type map, without an extra E-extension axiom.
-/

namespace SuccessorTree.V10

/-- The complete E relation on retained old vertices is exactly copied
for EVERY inserted cut d, even when the new ordinary vertex has genuine
nonzero E data. -/
theorem insertE_old_pair_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (x y : Nat) (hx : x < A.size) (hy : y < A.size) :
    insertE A ell d (insertAddress ell x) (insertAddress ell y) =
      A.E x y := by
  have hOld := neutralInsert_old_E_eq A ell hell hellPos x y hx hy
  change insertE A ell 0 (insertAddress ell x) (insertAddress ell y) =
    A.E x y at hOld
  calc
    insertE A ell d (insertAddress ell x) (insertAddress ell y) =
        insertE A ell 0 (insertAddress ell x) (insertAddress ell y) := by
          simp [insertE, insertedCut_insertAddress]
    _ = A.E x y := hOld

/-- The incoming E-column of the newly inserted ordinary vertex is
determined by precisely the first d old ordinary coordinates. -/
theorem insertE_new_column_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d : Nat) (hell : ell ≤ A.size)
    (hd : d ≤ ell) (x : Nat) :
    insertE A ell d (insertAddress ell x) ell =
      decide (x < d) := by
  have hEllSize : ell < A.size + 1 := by omega
  have hIff : insertAddress ell x < d ↔ x < d := by
    by_cases hxell : x < ell
    · rw [insertAddress_below ell x hxell]
    · rw [insertAddress_above ell x (by omega)]
      omega
  change decide (ell < A.size + 1 ∧
    insertAddress ell x < insertedCut A ell d ell) = decide (x < d)
  simp [hEllSize, insertedCut_at, hIff]

/-- The outgoing E-row to any retained old vertex y is obtained from
its original free level, independently of the inserted cut d. -/
theorem insertE_new_row_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d : Nat) (hell : ell ≤ A.size)
    (y : Nat) (hy : y < A.size) :
    insertE A ell d ell (insertAddress ell y) =
      decide (ell ≤ A.freeLevel y) := by
  have hyNew : insertAddress ell y < A.size+1 := by
    by_cases h : y < ell
    · rw [insertAddress_below ell y h]
      omega
    · rw [insertAddress_above ell y (by omega)]
      omega
  have hIff :
      ell < insertedCut A ell d (insertAddress ell y) ↔
        ell ≤ A.freeLevel y := by
    rw [insertedCut_insertAddress]
    by_cases h : A.freeLevel y < ell
    · simp [h] <;> omega
    · simp [h] <;> omega
  change decide (insertAddress ell y < A.size+1 ∧
    ell < insertedCut A ell d (insertAddress ell y)) =
    decide (ell ≤ A.freeLevel y)
  simp [hyNew, hIff]

/-- E has no self-pair at the inserted coordinate. The strict gate
d=0 or d<ell (already derived from admissibility) implies d<=ell. -/
theorem insertE_new_loop_false
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d : Nat) (hd : d ≤ ell) :
    insertE A ell d ell ell = false := by
  change decide (ell < A.size+1 ∧ ell < insertedCut A ell d ell) = false
  simp [insertedCut_at, Nat.not_lt.mpr hd]

/-- Every old upper vertex whose free cut reaches ell receives the
new socle coordinate's auxiliary E pair; no E compatibility with
its non-neutral L data needs to be imposed separately. -/
theorem insertE_new_upper_true
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d : Nat) (hell : ell ≤ A.size)
    (y : Nat) (hy : y < A.size)
    (hFree : ell ≤ A.freeLevel y) :
    insertE A ell d ell (insertAddress ell y) = true := by
  rw [insertE_new_row_eq A ell d hell y hy]
  simpa [hFree]

end SuccessorTree.V10

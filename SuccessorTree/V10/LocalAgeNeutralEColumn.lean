import SuccessorTree.V10.LocalAgeNeutralTransport
import Mathlib.Tactic

/-!
# The inserted E-coordinate is determined by the source type

After the old-atom transport lemma, the only genuinely NEW ordinary
coordinate in the neutral inserted type is ell. It has no L relations.
Its E-column is empty; its E-row at shifted old vertices is the source's
E-row at ell-1. This exact identity includes negative E facts and the
auxiliary E bit to the distinguished type vertex.

These equalities are the second piece of a representation-independent
uniform raw partial-type insertion. The source and target here are genuine
finite forbidden-free partial structures, not arbitrary imposed E tables.
-/

namespace SuccessorTree.V10

/-- The inserted ordinary vertex's E-row towards an old vertex is copied
from the immediately preceding source E-row. The positivity ell>0 is
essential: there is no source coordinate ell-1 at ell=0. -/
theorem neutralInsert_new_E_row
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (y : Nat) (hy : y < A.size) :
    (neutralInsert A ell hell hellPos).E ell (insertAddress ell y) =
      A.E (ell - 1) y := by
  have hyNew : insertAddress ell y < A.size + 1 := by
    by_cases hyell : y < ell
    · rw [insertAddress_below ell y hyell]
      omega
    · rw [insertAddress_above ell y (by omega)]
      omega
  have hCut :
      ell < insertedCut A ell 0 (insertAddress ell y) ↔
        ell - 1 < A.freeLevel y := by
    rw [insertedCut_insertAddress]
    by_cases hf : A.freeLevel y < ell
    · simp [hf] <;> omega
    · simp [hf] <;> omega
  have hIff :
      insertE A ell 0 ell (insertAddress ell y) = true ↔
        A.E (ell - 1) y = true := by
    constructor
    · intro h
      have ht := (insertE_true_iff A ell 0 _ _).1 h
      exact (A.E_iff_freeLevel (ell - 1) y).2 (hCut.mp ht.2)
    · intro h
      exact (insertE_true_iff A ell 0 _ _).2
        ⟨hyNew, hCut.mpr ((A.E_iff_freeLevel (ell - 1) y).1 h)⟩
  change insertE A ell 0 ell (insertAddress ell y) = A.E (ell-1) y
  cases hNew : insertE A ell 0 ell (insertAddress ell y) with
  | true =>
      exact (hIff.mp hNew).symm
  | false =>
      have hOld : A.E (ell - 1) y = false := by
        cases ho : A.E (ell - 1) y with
        | false => rfl
        | true =>
            have hcontra := hIff.mpr ho
            rw [hNew] at hcontra
            cases hcontra
      exact hOld.symm

/-- No old vertex has an E-pair TO the freshly inserted neutral vertex:
the latter's free cut is zero. -/
theorem neutralInsert_old_E_to_new_false
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (x : Nat) :
    (neutralInsert A ell hell hellPos).E (insertAddress ell x) ell =
      false := by
  change insertE A ell 0 (insertAddress ell x) ell = false
  simp [insertE, insertedCut]

/-- No auxiliary E-loop is added at the inserted vertex. -/
theorem neutralInsert_new_E_loop_false
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell) :
    (neutralInsert A ell hell hellPos).E ell ell = false := by
  change insertE A ell 0 ell ell = false
  simp [insertE, insertedCut]

/-- The new socle coordinate belongs to the E-socle of the shifted
distinguished vertex as soon as its original free cut reaches ell.
This is the auxiliary bit added in every type above the skipped level. -/
theorem neutralInsert_new_E_to_type
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (v : Nat) (hv : v < A.size)
    (hfree : ell ≤ A.freeLevel v) :
    (neutralInsert A ell hell hellPos).E ell (insertAddress ell v) =
      true := by
  rw [neutralInsert_new_E_row A ell hell hellPos v hv]
  exact (A.E_iff_freeLevel (ell - 1) v).2 (by omega)

/-- This last E bit is visible directly in the ACTUAL full partial type
over the shifted complete socle, with no abstract coding assumptions. -/
theorem neutralInsert_inserted_type_E
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (v : Nat) (hv : v < A.size)
    (hfree : ell ≤ A.freeLevel v) :
    ((neutralInsert A ell hell hellPos).partialTypeAt
        (A.freeLevel v + 1) (insertAddress ell v)).eRelation
      (some ⟨ell, by omega⟩) none = true := by
  change (neutralInsert A ell hell hellPos).E
    ell (insertAddress ell v) = true
  exact neutralInsert_new_E_to_type A ell hell hellPos v hv hfree

end SuccessorTree.V10

import SuccessorTree.V10.EndDuplicateL
import SuccessorTree.V10.PartialTypeRestriction
import Mathlib.Tactic

/-!
# The terminal end-duplicate satisfies all three partial-structure E axioms

Let A be an enumerated L+ partial structure of size N, and n<N.
Append a new vertex N with exactly the singleton L type of n
and the old/new directed L-tuples of n to its own E-socle
[0,fl_A(n)). No other old/new tuples are introduced.

Use the exact E predicate E(u,N) iff u<fl_A(n) and preserve all
other E tuples. Both old E and L are unchanged. The resulting
(N+1)-vertex object satisfies E spacing, downward closure, and E3.

The new vertex's complete partial L+ type over its E-socle is
exactly the original type of n. This is the local duplication
ingredient of M3, before checking that no irreducible forbidden
substructure was created.
-/

namespace SuccessorTree.V10

/-- Append one duplicate at the end of the existing enumeration. -/
noncomputable def duplicateEndPartial
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) (hn : n < A.size) :
    EnumeratedPartialStructure db du dd := by
  refine
    { size := A.size + 1
      L := duplicateEndL A n
      carrier_iff := ?_
      E := duplicateEndE A n
      E_inside := duplicateEndE_inside A n hn
      spaced := duplicateEndE_spaced A n hn
      downward := duplicateEndE_downward A n
      linked_E := ?_ }
  · intro x
    rfl
  · intro u w huw hu hw hlink
    by_cases hLast : w = A.size
    · subst w
      have huOld : u < A.size := by omega
      by_cases hBelow : u < A.freeLevel n
      · exact (duplicateEndE_new_iff A n u).2 hBelow
      · obtain ⟨r, hRel⟩ := hlink
        have hZero := duplicateEndL_cross_above A n u hn
          (by omega) huOld r
        rcases hRel with hRel | hRel
        · exfalso
          rw [hZero.1] at hRel
          contradiction
        · exfalso
          rw [hZero.2] at hRel
          contradiction
    · have hwOld : w < A.size := by omega
      have huOld : u < A.size := by omega
      have hOldRel :
          ∃ r : Fin db,
            A.L.binary u w r = true ∨
            A.L.binary w u r = true := by
        obtain ⟨r,hRel⟩ := hlink
        refine ⟨r, ?_⟩
        rcases hRel with hRel | hRel
        · left
          exact ((duplicateEndL_old A n u w huOld hwOld).1 r).symm.trans hRel
        · right
          exact ((duplicateEndL_old A n w u hwOld huOld).1 r).symm.trans hRel
      have hOldE := A.linked_E u w huw huOld hwOld hOldRel
      exact (duplicateEndE_old A n u w hwOld).trans hOldE

/-- The appended vertex has the source original's exact free level,
not a separately chosen cut. -/
theorem duplicateEndPartial_freeLevel
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) (hn : n < A.size) :
    (duplicateEndPartial A n hn).freeLevel A.size = A.freeLevel n :=
  duplicateEndE_new_freeLevel A n hn

/-- All old positive and negative L and E relations are retained
without modification by the full partial-structure extension. -/
theorem duplicateEndPartial_old_E
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) (hn : n < A.size)
    (u w : Nat) (hw : w < A.size) :
    (duplicateEndPartial A n hn).E u w = A.E u w :=
  duplicateEndE_old A n u w hw

/-- The appended type through its own E-socle is literally the
complete induced L+ partial type of its original vertex n. -/
theorem duplicateEndPartial_last_type_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) (hn : n < A.size) :
    (duplicateEndPartial A n hn).partialTypeAt
        (A.freeLevel n) A.size =
      A.partialTypeAt (A.freeLevel n) n := by
  let B := duplicateEndPartial A n hn
  have hBcut : A.freeLevel n ≤ B.freeLevel A.size := by
    have h := duplicateEndPartial_freeLevel A n hn
    change B.freeLevel A.size = A.freeLevel n at h
    omega
  apply PartialTypeWithE.eq_of_atoms
  · exact duplicateEndL_newType A n hn
  · intro x y
    cases x with
    | none =>
      cases y with
      | none =>
        exact (B.partialTypeAt_no_typeE_loop
            (A.freeLevel n) A.size).trans
          (A.partialTypeAt_no_typeE_loop (A.freeLevel n) n).symm
      | some j =>
        exact (B.partialTypeAt_no_reverseE
            (A.freeLevel n) A.size hBcut j).trans
          (A.partialTypeAt_no_reverseE
            (A.freeLevel n) n le_rfl j).symm
    | some i =>
      cases y with
      | none =>
        have hB : B.E i.val A.size = true :=
          (B.E_iff_freeLevel i.val A.size).2
            (lt_of_lt_of_le i.isLt hBcut)
        have hA : A.E i.val n = true :=
          (A.E_iff_freeLevel i.val n).2 i.isLt
        exact hB.trans hA.symm
      | some j =>
        have hj : j.val < A.size :=
          lt_trans (lt_of_lt_of_le j.isLt (A.freeLevel_le n)) hn
        exact duplicateEndE_old A n i.val j.val hj

end SuccessorTree.V10

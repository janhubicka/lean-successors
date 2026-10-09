import SuccessorTree.V10.AdmissibleSigmaSTree
import Mathlib.Tactic

/-!
# Duplication of an E column at a later enumeration level

For the concrete M3 duplication, fix a finite enumerated partial
structure A and two indices n<m ≤ A.size. The new ordinary vertex
at m must inherit EXACTLY the E-incidences of vertex n, while every
old E-column remains unchanged.

This file verifies that the resulting E relation on the enlarged
enumeration satisfies spacing, downward closure and boundedness,
and that the unique E-free level of m equals that of n. It is the
first structural component of the 'boring' extension used in the
proof of Proposition 6.39, not an instance of M3 or an
age-preserving construction by itself.

The duplicated L-reduct and its forbidden-age proof will be handled
in a separate module before forming an admissible partial structure.
-/

namespace SuccessorTree.V10

/-- Keep every E column with target < m; the new target m receives
precisely the E column of the earlier source n. -/
def duplicateLastE
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n m u w : Nat) : Bool :=
  if w < m then A.E u w
  else if w = m then A.E u n
  else false

theorem duplicateLastE_old
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n m u w : Nat) (hw : w < m) :
    duplicateLastE A n m u w = A.E u w := by
  simp [duplicateLastE, hw]

theorem duplicateLastE_new
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n m u : Nat) :
    duplicateLastE A n m u m = A.E u n := by
  have h : ¬ m < m := Nat.lt_irrefl m
  simp [duplicateLastE, h]

/-- Every E edge to the newly duplicated vertex has at least one
intervening ordinary coordinate because n<m and E was spaced at n. -/
theorem duplicateLastE_spaced
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n m : Nat) (hnm : n < m) :
    SpacedE (duplicateLastE A n m) := by
  intro u w h
  by_cases hOld : w < m
  · have he : A.E u w = true :=
      (duplicateLastE_old A n m u w hOld).symm.trans h
    exact A.spaced u w he
  · by_cases hNew : w = m
    · subst w
      have he : A.E u n = true :=
        (duplicateLastE_new A n m u).symm.trans h
      have hu := A.spaced u n he
      omega
    · simp [duplicateLastE, hOld, hNew] at h

/-- Every column, including the duplicated one, remains downward
closed in its lower E coordinates. -/
theorem duplicateLastE_downward
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n m : Nat) :
    DownwardE (duplicateLastE A n m) := by
  intro u w he z hz
  by_cases hOld : w < m
  · have heA : A.E u w = true :=
      (duplicateLastE_old A n m u w hOld).symm.trans he
    exact (duplicateLastE_old A n m z w hOld).symm.trans
      (A.downward u w heA z hz)
  · by_cases hNew : w = m
    · subst w
      have heA : A.E u n = true :=
        (duplicateLastE_new A n m u).symm.trans he
      exact (duplicateLastE_new A n m z).symm.trans
        (A.downward u n heA z hz)
    · simp [duplicateLastE, hOld, hNew] at he

/-- All duplicated E-incidences live on actual coordinates
0,...,m, with no new E-edges pointing outside this domain. -/
theorem duplicateLastE_inside
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n m : Nat) (hnm : n < m)
    (u w : Nat) (he : duplicateLastE A n m u w = true) :
    u < m + 1 ∧ w < m + 1 := by
  have hSpacing := (duplicateLastE_spaced A n m hnm) u w he
  by_cases hOld : w < m
  · constructor <;> omega
  · by_cases hNew : w = m
    · constructor <;> omega
    · simp [duplicateLastE, hOld, hNew] at he

/-- The chosen clone of n has precisely the same incoming E data
as the original n. This holds for all lower candidates, including
those at or above the original index n. -/
theorem duplicateLastE_clonedColumn
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n m u : Nat) (hnm : n < m) :
    duplicateLastE A n m u m =
      duplicateLastE A n m u n := by
  rw [duplicateLastE_new, duplicateLastE_old A n m u n hnm]

/-- The canonical first missing E-coordinate of the new vertex m
is *exactly* the canonical free level of n. No extra free-level
hypothesis is assumed for M3's one-coordinate E duplication. -/
theorem duplicateLastE_freeLevel
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n m : Nat) (hnm : n < m) :
    canonicalFreeLevel (duplicateLastE A n m)
        (duplicateLastE_spaced A n m hnm)
        (duplicateLastE_downward A n m) m =
      A.freeLevel n := by
  have hCut : IsFreeCut (duplicateLastE A n m) m
      (A.freeLevel n) := by
    constructor
    · intro u hu
      rw [duplicateLastE_new]
      exact (A.E_iff_freeLevel u n).2 hu
    · rw [duplicateLastE_new]
      exact A.freeLevel_firstMissing n
  exact freeCut_unique (duplicateLastE A n m) m
    (canonicalFreeLevel (duplicateLastE A n m)
      (duplicateLastE_spaced A n m hnm)
      (duplicateLastE_downward A n m) m)
    (A.freeLevel n)
    (canonicalFreeLevel_isFreeCut (duplicateLastE A n m)
      (duplicateLastE_spaced A n m hnm)
      (duplicateLastE_downward A n m) m)
    hCut

end SuccessorTree.V10

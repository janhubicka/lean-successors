import SuccessorTree.V10.ConcreteKptM1
import SuccessorTree.V10.PartialStructureE
import Mathlib.Tactic

/-!
# The exact E-socle of an end-duplicate for M3

The concrete duplication construction from Proposition 6.39 appends
one ordinary vertex at the end of an enumerated partial structure
A. It is a clone of a chosen earlier vertex n only with respect to
that vertex's own initial E-socle of length fl_A(n): all E-pairs
(u,new) are present exactly when u<fl_A(n).

The old E relation is unchanged, and no other E-pairs are introduced.
Here we verify this literal E construction satisfies spacing,
downward closure and inside-domain conditions. Its new vertex has
exactly the same free level as the duplicated earlier vertex.

The L-tuples of the clone are still to be defined. Their absence
above the free cut will make E3 automatic; forbidden-age
preservation will use irreducibility to replace any occurrence
of the clone by its earlier original.
-/

namespace SuccessorTree.V10

/-- Add one final E column, prescribed exactly by the source vertex's
free socle. The original E relation is not changed elsewhere. -/
noncomputable def duplicateEndE
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n u w : Nat) : Bool :=
  if w = A.size then decide (u < A.freeLevel n)
  else A.E u w

/-- Every old E-column is copied exactly, positive and negative bits. -/
theorem duplicateEndE_old
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n u w : Nat) (hw : w < A.size) :
    duplicateEndE A n u w = A.E u w := by
  have hneq : w ≠ A.size := Nat.ne_of_lt hw
  simp only [duplicateEndE, if_neg hneq]

/-- The exact new E column is the predecessor's canonical free cut. -/
theorem duplicateEndE_new_iff
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n u : Nat) :
    duplicateEndE A n u A.size = true ↔
      u < A.freeLevel n := by
  simp [duplicateEndE]

/-- The appended E-column still satisfies the spacing condition.
Here the sole new estimate is u+1<|A| whenever
u<fl_A(n)≤n<|A|. -/
theorem duplicateEndE_spaced
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) (hn : n < A.size) :
    SpacedE (duplicateEndE A n) := by
  intro u w h
  by_cases hnew : w = A.size
  · subst w
    have hu : u < A.freeLevel n :=
      (duplicateEndE_new_iff A n u).1 h
    have hf : A.freeLevel n ≤ n := A.freeLevel_le n
    omega
  · have hOld : A.E u w = true := by
      simpa only [duplicateEndE, if_neg hnew] using h
    exact A.spaced u w hOld

/-- Every column of the appended E relation is downward closed. -/
theorem duplicateEndE_downward
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) :
    DownwardE (duplicateEndE A n) := by
  intro u w h z hz
  by_cases hnew : w = A.size
  · subst w
    have hu : u < A.freeLevel n :=
      (duplicateEndE_new_iff A n u).1 h
    exact (duplicateEndE_new_iff A n z).2 (lt_trans hz hu)
  · have hOld : A.E u w = true := by
      simpa only [duplicateEndE, if_neg hnew] using h
    exact (by
      simpa only [duplicateEndE, if_neg hnew] using
        (A.downward u w hOld z hz))

/-- Every E incidence of the extended structure uses actual
vertices in 0,...,|A|, including its new terminal vertex. -/
theorem duplicateEndE_inside
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) (hn : n < A.size)
    (u w : Nat) (h : duplicateEndE A n u w = true) :
    u < A.size + 1 ∧ w < A.size + 1 := by
  by_cases hnew : w = A.size
  · subst w
    have hu : u < A.freeLevel n :=
      (duplicateEndE_new_iff A n u).1 h
    have hf := A.freeLevel_le n
    constructor <;> omega
  · have hOld : A.E u w = true := by
      simpa only [duplicateEndE, if_neg hnew] using h
    have ⟨hu, hw⟩ := A.E_inside u w hOld
    constructor <;> omega

/-- The first missing E coordinate of the newly appended clone
is exactly the original vertex's first missing E coordinate. -/
theorem duplicateEndE_new_freeCut
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) :
    IsFreeCut (duplicateEndE A n) A.size (A.freeLevel n) := by
  constructor
  · intro u hu
    exact (duplicateEndE_new_iff A n u).2 hu
  · have hnot : ¬ A.freeLevel n < A.freeLevel n :=
      Nat.lt_irrefl _
    have hb : duplicateEndE A n (A.freeLevel n) A.size ≠ true :=
      fun h => hnot ((duplicateEndE_new_iff A n (A.freeLevel n)).1 h)
    cases h : duplicateEndE A n (A.freeLevel n) A.size with
    | false => rfl
    | true => exact False.elim (hb h)

/-- Canonical free level of the last vertex of the enlarged partial
structure: it equals the cloned original's free level. -/
theorem duplicateEndE_new_freeLevel
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) (hn : n < A.size) :
    canonicalFreeLevel (duplicateEndE A n)
      (duplicateEndE_spaced A n hn)
      (duplicateEndE_downward A n)
      A.size = A.freeLevel n := by
  exact freeCut_unique (duplicateEndE A n) A.size
    (canonicalFreeLevel (duplicateEndE A n)
      (duplicateEndE_spaced A n hn)
      (duplicateEndE_downward A n)
      A.size)
    (A.freeLevel n)
    (canonicalFreeLevel_isFreeCut (duplicateEndE A n)
      (duplicateEndE_spaced A n hn)
      (duplicateEndE_downward A n) A.size)
    (duplicateEndE_new_freeCut A n)

end SuccessorTree.V10

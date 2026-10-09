import SuccessorTree.V10.PartialStructureE
import Mathlib.Tactic

/-!
# Preserving the E socle while realizing a shorter partial type

The Kpt prefix-closure issue is not settled by raw restriction alone:
a type over cut d must be represented as the full type of an ordinary
vertex of SOME partial structure whose free level is exactly d.

The elementary numerical repair is to retain the first d ordinary
vertices, add one neutral filler vertex at d, and realize the
distinguished type vertex at position d+1. Its E-socle contains exactly
the coordinates below d. The extra filler is essential: with the
type vertex inserted immediately at d, the E pair (d-1,d) would be
consecutive and violate Definition 6.28(1).

This module proves that the replicated E relation obeys the spacing
and downward-closure axioms, has the exact free cut d, and agrees with
the original induced partial type on every E bit. It does not yet
construct the L-reduct or prove forbidden-freeness; those are separate
interfaces for the next localized patch.
-/

namespace SuccessorTree.V10

/-- One-filler replica of the E relation on the old initial socle,
plus a new type vertex at d+1 whose E-socle has length d. -/
def prefixReplicaE
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (d u w : Nat) : Bool :=
  if w < d then A.E u w
  else if w = d + 1 then decide (u < d)
  else false

/-- Existing E-columns below d are copied exactly. -/
theorem prefixReplicaE_old
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (d u w : Nat) (hw : w < d) :
    prefixReplicaE A d u w = A.E u w := by
  simp [prefixReplicaE, hw]

/-- The newly inserted type vertex has exactly the first d
coordinates in its E-socle, including when d=0. -/
theorem prefixReplicaE_last_iff
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (d u : Nat) :
    prefixReplicaE A d u (d + 1) = true ↔ u < d := by
  have hd : ¬ d + 1 < d := by omega
  simp [prefixReplicaE, hd]

/-- The replica has the original partial-structure spacing condition.
In the new column u<d implies u+1<d+1; this is the reason for
the neutral filler at position d. -/
theorem prefixReplicaE_spaced
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd) (d : Nat) :
    SpacedE (prefixReplicaE A d) := by
  intro u w h
  by_cases hw : w < d
  · have hOld : A.E u w = true := by
      simpa [prefixReplicaE, hw] using h
    exact A.spaced u w hOld
  · by_cases hlast : w = d + 1
    · have hu : u < d := by
        simpa [prefixReplicaE, hw, hlast] using h
      omega
    · simp [prefixReplicaE, hw, hlast] at h

/-- Every column in the replica is downward closed, including the
new free socle. -/
theorem prefixReplicaE_downward
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd) (d : Nat) :
    DownwardE (prefixReplicaE A d) := by
  intro u w h z hz
  by_cases hw : w < d
  · have hOld : A.E u w = true := by
      simpa [prefixReplicaE, hw] using h
    have hzOld := A.downward u w hOld z hz
    simpa [prefixReplicaE, hw] using hzOld
  · by_cases hlast : w = d + 1
    · have hu : u < d := by
        simpa [prefixReplicaE, hw, hlast] using h
      have hz' : z < d := by omega
      rw [hlast]
      exact (prefixReplicaE_last_iff A d z).2 hz'
    · simp [prefixReplicaE, hw, hlast] at h

/-- The first missing E coordinate at the new type vertex is d.
There is no E pair to its immediately preceding neutral filler. -/
theorem prefixReplicaE_last_freeCut
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd) (d : Nat) :
    IsFreeCut (prefixReplicaE A d) (d + 1) d := by
  constructor
  · intro u hu
    exact (prefixReplicaE_last_iff A d u).2 hu
  · have hnot : ¬ d < d := by omega
    have hb : prefixReplicaE A d d (d + 1) ≠ true := by
      intro h
      exact hnot ((prefixReplicaE_last_iff A d d).1 h)
    cases h : prefixReplicaE A d d (d + 1) with
    | false => rfl
    | true => exact False.elim (hb h)

/-- Its canonical E free level is exactly d, proved from the
general unique-first-gap theorem rather than assumed. -/
theorem prefixReplicaE_last_freeLevel
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd) (d : Nat) :
    canonicalFreeLevel (prefixReplicaE A d)
      (prefixReplicaE_spaced A d)
      (prefixReplicaE_downward A d)
      (d + 1) = d := by
  exact freeCut_unique (prefixReplicaE A d) (d + 1)
    (canonicalFreeLevel (prefixReplicaE A d)
      (prefixReplicaE_spaced A d)
      (prefixReplicaE_downward A d) (d + 1))
    d
    (canonicalFreeLevel_isFreeCut (prefixReplicaE A d)
      (prefixReplicaE_spaced A d)
      (prefixReplicaE_downward A d) (d + 1))
    (prefixReplicaE_last_freeCut A d)

/-- The new E column agrees with the original type's E-socle
whenever d is at most its original free level. -/
theorem prefixReplicaE_preserves_type_socle
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v d : Nat) (hd : d ≤ A.freeLevel v)
    (i : Fin d) :
    prefixReplicaE A d i.val (d + 1) = A.E i.val v := by
  have hi : i.val < d := i.isLt
  have hOld : A.E i.val v = true :=
    (A.E_iff_freeLevel i.val v).2 (lt_of_lt_of_le hi hd)
  have hNew : prefixReplicaE A d i.val (d + 1) = true :=
    (prefixReplicaE_last_iff A d i.val).2 hi
  exact hNew.trans hOld.symm

/-- The old socle's E-incidences are preserved at every pair of
coordinates, including E-negative facts and diagonal pairs. -/
theorem prefixReplicaE_preserves_old_socle
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (d : Nat) (i j : Fin d) :
    prefixReplicaE A d i.val j.val = A.E i.val j.val :=
  prefixReplicaE_old A d i.val j.val j.isLt

end SuccessorTree.V10

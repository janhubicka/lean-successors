import SuccessorTree.V10.LevelRemovalAllLevelsAdmissible
import Mathlib.Tactic

/-!
# The intrinsic total Kpt function underlying the M2 level-removal map

The preceding theorem shows that for any genuine gap between the images of
two successive source levels the SAME deleted complete raw record is
admissible at every source level at or above the gap. Therefore we can
define a total function on the admissible Kpt forest without selecting a
value from an arbitrary source successor or finite witness.

Below the gap the function is F. At and above the gap it deletes the
fixed ordinary coordinate m = lev(F a0)-1 from the complete raw record
of F(x), using the checked all-level admissibility proof solely as the
Subtype certificate.

We verify its two level properties and root extension directly. This
is *not* yet a ShapeMap: the proof of the weak successor condition,
strict level order, and injectivity must still be supplied. In particular
no M2 or finite L-only corrected B3 necessity is postulated.
-/

namespace SuccessorTree.V10

/-- Intrinsic piecewise candidate for the first factor of the M2
level-removal construction. It does not depend on a chosen successor
or chosen finite witness, only on F and the two source IMAGE levels. -/
noncomputable def uniformGapDeletedKpt
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : AdmissibleKptNode family) :
    AdmissibleKptNode family := by
  classical
  by_cases hx : LevelTree.lev a₀ ≤ LevelTree.lev x
  · let hExists :=
      admissible_deleted_image_at_all_upper_source_levels
        family F q₀ a₀ hprev hgap x hx
    let hm := Classical.choose hExists
    have hAd := Classical.choose_spec hExists
    exact ⟨⟨(F x).1.1 - 1,
      (F x).1.2.deleteOrdinary
        (LevelTree.lev (F a₀) - 1) hm⟩,hAd⟩
  · exact F x

/-- All source levels strictly below the gap keep their complete
admissible Kpt image, not merely the raw L reduct. -/
theorem uniformGapDeletedKpt_below
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : AdmissibleKptNode family)
    (hLow : LevelTree.lev x < LevelTree.lev a₀) :
    uniformGapDeletedKpt family F q₀ a₀ hprev hgap x = F x := by
  classical
  simp [uniformGapDeletedKpt, Nat.not_le.mpr hLow]

/-- At and above the boundary the output level is one smaller than
the level of F(x): exactly one ordinary coordinate was deleted. -/
theorem uniformGapDeletedKpt_above_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : AdmissibleKptNode family)
    (hHigh : LevelTree.lev a₀ ≤ LevelTree.lev x) :
    LevelTree.lev (uniformGapDeletedKpt family F q₀ a₀ hprev hgap x) =
      LevelTree.lev (F x) - 1 := by
  classical
  simp [uniformGapDeletedKpt, hHigh]

/-- The candidate's level function is precisely the old image
level function minus one from the boundary onward. -/
theorem uniformGapDeletedKpt_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : AdmissibleKptNode family) :
    LevelTree.lev (uniformGapDeletedKpt family F q₀ a₀ hprev hgap x) =
      if LevelTree.lev x < LevelTree.lev a₀ then
        LevelTree.lev (F x) else LevelTree.lev (F x) - 1 := by
  by_cases hLow : LevelTree.lev x < LevelTree.lev a₀
  · rw [if_pos hLow, uniformGapDeletedKpt_below family F q₀ a₀
      hprev hgap x hLow]
  · rw [if_neg hLow]
    exact uniformGapDeletedKpt_above_level family F q₀ a₀
      hprev hgap x (Nat.le_of_not_gt hLow)

/-- The intrinsic deleted-image function preserves equality of source
levels, so it satisfies the level-preservation field needed later. -/
theorem uniformGapDeletedKpt_level_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    {x y : AdmissibleKptNode family}
    (hxy : LevelTree.lev x = LevelTree.lev y) :
    LevelTree.lev (uniformGapDeletedKpt family F q₀ a₀ hprev hgap x) =
      LevelTree.lev (uniformGapDeletedKpt family F q₀ a₀ hprev hgap y) := by
  rw [uniformGapDeletedKpt_level, uniformGapDeletedKpt_level]
  rw [hxy, F.level_eq_of_level_eq hxy]

/-- Because the boundary source level is positive, every source
root is unchanged by the delete operation and hence remains below
its image. This is the root-extension ShapeMap field. -/
theorem uniformGapDeletedKpt_root_le
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : AdmissibleKptNode family)
    (hRoot : LevelTree.lev x = 0) :
    x ≤ uniformGapDeletedKpt family F q₀ a₀ hprev hgap x := by
  have hLow : LevelTree.lev x < LevelTree.lev a₀ := by
    omega
  rw [uniformGapDeletedKpt_below family F q₀ a₀ hprev hgap x hLow]
  exact F.root_le' hRoot

end SuccessorTree.V10

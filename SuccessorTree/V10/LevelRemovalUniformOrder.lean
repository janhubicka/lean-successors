import SuccessorTree.V10.LevelRemovalUniformLevel
import SuccessorTree.V10.LevelRemovalCrossGapPrefix
import Mathlib.Tactic

/-!
# The intrinsic M2 deletion candidate preserves full Kpt prefix order

For comparable source nodes x≤y there are three cases:
- both levels below the gap: the map is F;
- both levels at/above the gap: delete the SAME coordinate from F(x),F(y)
  and use rawPartialTypeDeleteAt_prefix;
- a lower level below and an upper level at/above the gap: the complete
  lower raw image ends strictly before the deleted coordinate, so the
  checked cross-gap prefix lemma applies.

The theorem is for the actual admissible Kpt nodes, with every directed
L and E bit represented. It verifies order preservation only, NOT the
weak-successor condition, injection or the factorization axiom M2.
-/

namespace SuccessorTree.V10

/-- On the upper branch the intrinsic candidate is exactly the
coordinate-deleted RAW image record. The required admissibility
witness only certifies membership; it cannot influence the value. -/
theorem uniformGapDeletedKpt_above_raw
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : AdmissibleKptNode family)
    (hHigh : LevelTree.lev a₀ ≤ LevelTree.lev x) :
    let m := LevelTree.lev (F a₀) - 1
    ∃ hm : m < (F x).1.1,
      (uniformGapDeletedKpt family F q₀ a₀ hprev hgap x).1 =
        rawPartialTypeDeleteAt (F x).1 m hm := by
  classical
  obtain ⟨hm,hAd⟩ :=
    admissible_deleted_image_at_all_upper_source_levels
      family F q₀ a₀ hprev hgap x hHigh
  refine ⟨hm, ?_⟩
  simp [uniformGapDeletedKpt, hHigh, rawPartialTypeDeleteAt]

/-- Full prefix-order preservation for the candidate gap-deletion
function. No M2, successor law for the candidate, or artificial age
hypothesis is assumed. -/
theorem uniformGapDeletedKpt_map_le
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    {x y : AdmissibleKptNode family}
    (hxy : x ≤ y) :
    uniformGapDeletedKpt family F q₀ a₀ hprev hgap x ≤
      uniformGapDeletedKpt family F q₀ a₀ hprev hgap y := by
  let D := uniformGapDeletedKpt family F q₀ a₀ hprev hgap
  let m := LevelTree.lev (F a₀) - 1
  have hSourceLe : LevelTree.lev x ≤ LevelTree.lev y :=
    LevelTree.level_le_of_le hxy
  have hFxy : (F x).1 ≤ (F y).1 := F.map_le_of_le hxy
  by_cases hHighX : LevelTree.lev a₀ ≤ LevelTree.lev x
  · have hHighY : LevelTree.lev a₀ ≤ LevelTree.lev y := by omega
    obtain ⟨hmx,hDx⟩ :=
      uniformGapDeletedKpt_above_raw family F q₀ a₀ hprev hgap x hHighX
    obtain ⟨hmy,hDy⟩ :=
      uniformGapDeletedKpt_above_raw family F q₀ a₀ hprev hgap y hHighY
    have hRaw : rawPartialTypeDeleteAt (F x).1 m hmx ≤
        rawPartialTypeDeleteAt (F y).1 m hmy := by
      exact rawPartialTypeDeleteAt_prefix hFxy m hmx
    change (D x).1 ≤ (D y).1
    rw [hDx, hDy]
    exact hRaw
  · have hLowX : LevelTree.lev x < LevelTree.lev a₀ := by omega
    by_cases hLowY : LevelTree.lev y < LevelTree.lev a₀
    · rw [uniformGapDeletedKpt_below family F q₀ a₀
          hprev hgap x hLowX,
          uniformGapDeletedKpt_below family F q₀ a₀
          hprev hgap y hLowY]
      exact F.map_le_of_le hxy
    · have hHighY : LevelTree.lev a₀ ≤ LevelTree.lev y := by omega
      obtain ⟨hmy,hDy⟩ :=
        uniformGapDeletedKpt_above_raw family F q₀ a₀ hprev hgap y hHighY
      have hXQ : LevelTree.lev x ≤ LevelTree.lev q₀ := by omega
      have hFXQ : LevelTree.lev (F x) ≤ LevelTree.lev (F q₀) :=
        shapeMap_level_le_of_level_le family F hXQ
      have hLowFx : (F x).1.1 ≤ m := by
        change LevelTree.lev (F x) ≤ m
        dsimp [m]
        omega
      have hRaw : (F x).1 ≤ rawPartialTypeDeleteAt (F y).1 m hmy :=
        rawPartialTypePrefix_delete_above_cut hFxy m hLowFx hmy
      change (uniformGapDeletedKpt family F q₀ a₀ hprev hgap x).1 ≤
        (uniformGapDeletedKpt family F q₀ a₀ hprev hgap y).1
      rw [uniformGapDeletedKpt_below family F q₀ a₀
        hprev hgap x hLowX, hDy]
      exact hRaw

end SuccessorTree.V10

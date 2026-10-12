import SuccessorTree.V10.LevelRemovalUniformFunction
import Mathlib.Tactic

/-!
# Strict source-level order for the intrinsic M2 deletion candidate

The candidate D is F below a source-level boundary and deletes the
last omitted target level m from every image at/above the boundary.
The successor-tree M2 hypothesis says the images of consecutive
boundary levels are separated by at least one missing target level.

This is precisely the arithmetic needed to show that the new
piecewise level function is still STRICTLY increasing; it is NOT
enough to infer injectivity of the raw deleted records without the
genuine weak successor property. We isolate this dependency so no
claim about injectivity or M2 is smuggled into the definition.
-/

namespace SuccessorTree.V10

/-- A shape-preserving map is monotone on source LEVELS, including
nodes in distinct tree components. No M2 assumption is used. -/
theorem shapeMap_level_le_of_level_le
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    {x y : AdmissibleKptNode family}
    (hxy : LevelTree.lev x ≤ LevelTree.lev y) :
    LevelTree.lev (F x) ≤ LevelTree.lev (F y) := by
  rcases hxy.eq_or_lt with hEq | hLt
  · exact Nat.le_of_eq (F.level_eq_of_level_eq hEq)
  · exact Nat.le_of_lt (F.level_lt_of_level_lt hLt)

/-- The intrinsic piecewise deleted-image function is strictly
increasing on source levels. In the cross-boundary case we consume
exactly one of the ≥2 target-level steps in the original image gap.
At and above the boundary, the old image levels are at least two,
so subtraction of one preserves strict inequalities. -/
theorem uniformGapDeletedKpt_level_strictMono
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    {x y : AdmissibleKptNode family}
    (hxy : LevelTree.lev x < LevelTree.lev y) :
    LevelTree.lev (uniformGapDeletedKpt family F q₀ a₀ hprev hgap x) <
      LevelTree.lev (uniformGapDeletedKpt family F q₀ a₀ hprev hgap y) := by
  rw [uniformGapDeletedKpt_level family F q₀ a₀ hprev hgap x,
      uniformGapDeletedKpt_level family F q₀ a₀ hprev hgap y]
  have hFxy : LevelTree.lev (F x) < LevelTree.lev (F y) :=
    F.level_lt_of_level_lt hxy
  by_cases hxLow : LevelTree.lev x < LevelTree.lev a₀
  · by_cases hyLow : LevelTree.lev y < LevelTree.lev a₀
    · simp only [if_pos hxLow, if_pos hyLow]
      exact hFxy
    · have hXQ : LevelTree.lev x ≤ LevelTree.lev q₀ := by omega
      have hAY : LevelTree.lev a₀ ≤ LevelTree.lev y := by omega
      have hFxFq := shapeMap_level_le_of_level_le family F hXQ
      have hFaFy := shapeMap_level_le_of_level_le family F hAY
      simp only [if_pos hxLow, if_neg hyLow]
      omega
  · have hyLow : ¬ LevelTree.lev y < LevelTree.lev a₀ := by omega
    have hAX : LevelTree.lev a₀ ≤ LevelTree.lev x := by omega
    have hFaFx := shapeMap_level_le_of_level_le family F hAX
    simp only [if_neg hxLow, if_neg hyLow]
    omega

end SuccessorTree.V10

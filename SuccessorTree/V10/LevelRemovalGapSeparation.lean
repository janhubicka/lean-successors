import SuccessorTree.V10.M3LiteralDuplication
import SuccessorTree.Monoid
import Mathlib.Tactic

/-!
# A gap between consecutive source image levels omits its target coordinate

The intended M2 level-removal operation deletes the last target level
strictly below the image of a source level n. Before constructing any
new map, the target coordinate must be shown to be absent from the
range of the original shape-preserving map F.

This follows directly from strict level monotonicity: every source
node below n maps below the gap, and every source node at or above
n maps above it. The argument uses neither M2 nor an abstract SMTree
instance and does not require the two original nodes to be comparable.
-/

namespace SuccessorTree.V10

/-- Shape-preserving maps are monotone on the *levels* of arbitrary
nodes, including nodes lying in different root components. -/
theorem shapeMap_level_le_of_level_le
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    {x y : AdmissibleKptNode family}
    (h : LevelTree.lev x ≤ LevelTree.lev y) :
    LevelTree.lev (F x) ≤ LevelTree.lev (F y) := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact (F.level_lt_of_level_lt hlt).le
  · exact (F.level_eq_of_level_eq heq).le

/-- Every level strictly below a is sent strictly below the last
missing target level when q is at the preceding source level. -/
theorem shapeMap_image_below_target_gap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q a x : AdmissibleKptNode family)
    (hPrev : LevelTree.lev q + 1 = LevelTree.lev a)
    (hGap : LevelTree.lev (F q) + 1 < LevelTree.lev (F a))
    (hx : LevelTree.lev x < LevelTree.lev a) :
    LevelTree.lev (F x) < LevelTree.lev (F a) - 1 := by
  have hxq : LevelTree.lev x ≤ LevelTree.lev q := by omega
  have hmap := shapeMap_level_le_of_level_le family F hxq
  omega

/-- The target level just below F(a) lies below the image of
every source node at level at least lev(a). -/
theorem shapeMap_image_above_target_gap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q a x : AdmissibleKptNode family)
    (hGap : LevelTree.lev (F q) + 1 < LevelTree.lev (F a))
    (hx : LevelTree.lev a ≤ LevelTree.lev x) :
    LevelTree.lev (F a) - 1 < LevelTree.lev (F x) := by
  have hmap := shapeMap_level_le_of_level_le family F hx
  omega

/-- The strict gap between images of consecutive source levels
implies that the final missing target level is skipped by F
globally. No M2 factorization or new deletion map is assumed. -/
theorem shapeMap_skips_last_target_gap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q a : AdmissibleKptNode family)
    (hPrev : LevelTree.lev q + 1 = LevelTree.lev a)
    (hGap : LevelTree.lev (F q) + 1 < LevelTree.lev (F a)) :
    F.Skips (LevelTree.lev (F a) - 1) := by
  intro hRange
  obtain ⟨x,hx⟩ := hRange
  by_cases hlow : LevelTree.lev x < LevelTree.lev a
  · have hlt :=
      shapeMap_image_below_target_gap family F q a x hPrev hGap hlow
    omega
  · have hhigh :=
      shapeMap_image_above_target_gap family F q a x hGap
        (Nat.le_of_not_gt hlow)
    omega

end SuccessorTree.V10

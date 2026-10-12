import SuccessorTree.V10.LevelRemovalBoundaryRestoration
import Mathlib.Tactic

/-!
# The deletion factor has a canonical partial inverse on its whole range

The global intrinsic deletion D is already a genuine injective Kpt
ShapeMap. Hence the equation R(D(x))=F(x) determines a unique partial
restoration R on the ENTIRE image of D, not only source level n.

This partial map has precisely the level function of a one-gap
insertion: it fixes all target levels below the omitted m and raises
those at or above m by one. Neither a forbidden-age extension
property nor an M2 axiom is assumed.

Extending R from its image domain to all Kpt nodes while preserving
genuine weak successors is still open.
-/

namespace SuccessorTree.V10

/-- The full image of the intrinsic deletion factor, including all
root components and all source levels. -/
def uniformDeletedFullImage
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀)) :
    Set (AdmissibleKptNode family) :=
  Set.range (uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap)

/-- Unique pointwise restoration on the entire deletion range,
defined using injectivity and no auxiliary finite witness. -/
noncomputable def uniformDeletedFullRestoration
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (y : {y : AdmissibleKptNode family //
      y ∈ uniformDeletedFullImage family F q₀ a₀ hprev hgap}) :
    AdmissibleKptNode family :=
  F (Classical.choose y.2)

/-- Literal restoration of F on ALL source types, not just one
selected finite representative or the first affected level. -/
theorem uniformDeletedFullRestoration_spec
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : AdmissibleKptNode family) :
    uniformDeletedFullRestoration family F q₀ a₀ hprev hgap
      ⟨uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x,
        ⟨x,rfl⟩⟩ = F x := by
  classical
  let D := uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap
  let y : {y : AdmissibleKptNode family //
    y ∈ uniformDeletedFullImage family F q₀ a₀ hprev hgap} :=
      ⟨D x,⟨x,rfl⟩⟩
  change F (Classical.choose y.2) = F x
  have hChosen : D (Classical.choose y.2) = D x :=
    Classical.choose_spec y.2
  exact congrArg (fun z : AdmissibleKptNode family => F z)
    (D.injective' hChosen)

/-- The restoration on the image of D has the EXACT one-gap
level function, not just monotonicity or preservation of equal levels.

This formula is independent of the corrected finite L-age B3 test
and is meaningful even before the complementary map is constructed. -/
theorem uniformDeletedFullRestoration_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (y : {y : AdmissibleKptNode family //
      y ∈ uniformDeletedFullImage family F q₀ a₀ hprev hgap}) :
    LevelTree.lev (uniformDeletedFullRestoration
      family F q₀ a₀ hprev hgap y) =
      if LevelTree.lev y.1 < LevelTree.lev (F a₀) - 1
      then LevelTree.lev y.1 else LevelTree.lev y.1 + 1 := by
  classical
  let D := uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap
  let x := Classical.choose y.2
  have hx : D x = y.1 := Classical.choose_spec y.2
  change LevelTree.lev (F x) = _
  rw [←hx, uniformGapDeletedShapeMap_level family F q₀ a₀ hprev hgap x]
  by_cases hLow : LevelTree.lev x < LevelTree.lev a₀
  · have hXQ : LevelTree.lev x ≤ LevelTree.lev q₀ := by omega
    have hBound := shapeMap_level_le_of_level_le family F hXQ
    have hFBelow :
        LevelTree.lev (F x) < LevelTree.lev (F a₀) - 1 := by
      omega
    simp only [if_pos hLow, if_pos hFBelow]
  · have hHigh : LevelTree.lev a₀ ≤ LevelTree.lev x :=
      Nat.le_of_not_gt hLow
    have hBound := shapeMap_level_le_of_level_le family F hHigh
    have hFAbove :
        LevelTree.lev (F a₀) - 1 ≤ LevelTree.lev (F x) - 1 := by
      omega
    simp only [if_neg hLow, if_neg (Nat.not_lt.mpr hFAbove)]
    have hFPos : 0 < LevelTree.lev (F x) := by omega
    omega

end SuccessorTree.V10

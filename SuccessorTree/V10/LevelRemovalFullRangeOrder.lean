import SuccessorTree.V10.LevelRemovalFullRangeRestoration
import SuccessorTree.ShapeOrderReflection
import Mathlib.Tactic

/-!
# The partial M2 restoration is an order embedding

On the entire range of the intrinsic deletion factor D, the
canonical inverse prescription R(D(x))=F(x) is not just an
injective function with the right level map. It preserves AND
reflects the genuine Kpt prefix order.

This is a partial order-embedding theorem, not an assertion
that R extends to the whole Kpt tree.
-/

namespace SuccessorTree.V10

/-- The partial restoration on D's range preserves and reflects the
complete Kpt prefix order, because both D and F are ShapeMaps. -/
theorem uniformDeletedFullRestoration_le_iff
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (y z : {y : AdmissibleKptNode family //
      y ∈ uniformDeletedFullImage family F q₀ a₀ hprev hgap}) :
    y.1 ≤ z.1 ↔
      uniformDeletedFullRestoration family F q₀ a₀ hprev hgap y ≤
      uniformDeletedFullRestoration family F q₀ a₀ hprev hgap z := by
  classical
  let D := uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap
  let x := Classical.choose y.2
  let x' := Classical.choose z.2
  have hy : D x = y.1 := Classical.choose_spec y.2
  have hz : D x' = z.1 := Classical.choose_spec z.2
  change y.1 ≤ z.1 ↔ F x ≤ F x'
  constructor
  · intro h
    have hDx : D x ≤ D x' := by
      calc
        D x = y.1 := hy
        _ ≤ z.1 := h
        _ = D x' := hz.symm
    exact F.map_le_of_le (D.reflects_le hDx)
  · intro h
    have hxx : x ≤ x' := F.reflects_le h
    calc
      y.1 = D x := hy.symm
      _ ≤ D x' := D.map_le_of_le hxx
      _ = z.1 := hz

/-- The partial restoration is injective on the entire image of D. -/
theorem uniformDeletedFullRestoration_injective
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀)) :
    Function.Injective
      (uniformDeletedFullRestoration family F q₀ a₀ hprev hgap) := by
  intro y z h
  have hle : y.1 ≤ z.1 :=
    (uniformDeletedFullRestoration_le_iff
      family F q₀ a₀ hprev hgap y z).2 (le_of_eq h)
  have hge : z.1 ≤ y.1 :=
    (uniformDeletedFullRestoration_le_iff
      family F q₀ a₀ hprev hgap z y).2 (le_of_eq h.symm)
  exact Subtype.ext (le_antisymm hle hge)

end SuccessorTree.V10

import SuccessorTree.V10.LevelRemovalM2ExactExtension
import Mathlib.Tactic

/-!
# The intrinsic deleted-image range carries an unambiguous partial inverse

Fix a genuine source-level gap for a shape map F and let D be its
already certified uniform coordinate-deletion ShapeMap.

On images D(x) of source nodes at the first affected level n, the
prescription D(x) -> F(x) is a genuine FUNCTION. This requires the
proved injectivity of D, not just agreement of numerical levels.
Every such image lies at the one target level m omitted by F.

This defines a canonical partial restoration graph without imposing
B2 ordinary-socle compatibility or the strengthened finite L-only B3
condition. Extending it as a one-gap Kpt ShapeMap is the remaining M2
obligation. No such global extension is asserted here.
-/

namespace SuccessorTree.V10

/-- The image under the intrinsic deleted map of the entire source
boundary level, not of a chosen finite model or component. -/
def uniformDeletedBoundaryImage
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀)) :
    Set (AdmissibleKptNode family) :=
  {y | ∃ x : AdmissibleKptNode family,
    LevelTree.lev x = LevelTree.lev a₀ ∧
    uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x = y}

/-- The entire boundary range occupies exactly one level, namely
m = lev(F(a₀))-1. This is the level at which the complementary
one-gap map must reconstruct the deleted coordinate. -/
theorem uniformDeletedBoundaryImage_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (y : AdmissibleKptNode family)
    (hy : y ∈ uniformDeletedBoundaryImage family F q₀ a₀ hprev hgap) :
    LevelTree.lev y = LevelTree.lev (F a₀) - 1 := by
  obtain ⟨x,hx,hxy⟩ := hy
  rw [←hxy, uniformGapDeletedShapeMap_level family F q₀ a₀
    hprev hgap x]
  have hNotLow : ¬ LevelTree.lev x < LevelTree.lev a₀ := by omega
  rw [if_neg hNotLow]
  exact congrArg (fun k : Nat => k - 1)
    (F.level_eq_of_level_eq hx)

/-- On the actual boundary range, there is exactly one possible
restoration: find the unique source x with D(x)=y and return F(x).
The choice is independent of the witness by ShapeMap.injective'. -/
noncomputable def uniformDeletedBoundaryRestoration
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (y : {y : AdmissibleKptNode family //
        y ∈ uniformDeletedBoundaryImage family F q₀ a₀ hprev hgap}) :
    AdmissibleKptNode family :=
  F (Classical.choose y.2)

/-- The canonical partial restoration is exactly F on EVERY source
node of the chosen boundary level, rather than merely on one selected
finite set of types. -/
theorem uniformDeletedBoundaryRestoration_spec
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : AdmissibleKptNode family)
    (hx : LevelTree.lev x = LevelTree.lev a₀) :
    uniformDeletedBoundaryRestoration family F q₀ a₀ hprev hgap
      ⟨uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x,
        ⟨x,hx,rfl⟩⟩ = F x := by
  classical
  let D := uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap
  let y : {y : AdmissibleKptNode family //
      y ∈ uniformDeletedBoundaryImage family F q₀ a₀ hprev hgap} :=
    ⟨D x, ⟨x,hx,rfl⟩⟩
  change F (Classical.choose y.2) = F x
  have hChosen : D (Classical.choose y.2) = D x :=
    (Classical.choose_spec y.2).2
  exact congrArg (fun z : AdmissibleKptNode family => F z)
    (D.injective' hChosen)

/-- The range of the partial restoration is on the original boundary
image level m+1, even when boundary node inputs are incomparable. -/
theorem uniformDeletedBoundaryRestoration_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (y : {y : AdmissibleKptNode family //
        y ∈ uniformDeletedBoundaryImage family F q₀ a₀ hprev hgap}) :
    LevelTree.lev (uniformDeletedBoundaryRestoration
      family F q₀ a₀ hprev hgap y) = LevelTree.lev (F a₀) := by
  change LevelTree.lev (F (Classical.choose y.2)) =
    LevelTree.lev (F a₀)
  exact F.level_eq_of_level_eq (Classical.choose_spec y.2).1

end SuccessorTree.V10

import SuccessorTree.FatTree.ShapeEllentuckOne
import SuccessorTree.ShapeFiniteInduction

/-!
# Finite-dimensional shape Ramsey theorem from fat-tree Ellentuck

The one-dimensional input is obtained from the topological Ramsey theorem
for fat trees. The relative reduction and finite-dimensional induction are
shared with the direct proof in `ShapeFiniteInduction`; the direct
one-dimensional Ramsey theorem is not used.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Relative one-moving-level homogeneity from fat-tree Ellentuck. -/
theorem shapeRamsey_one_relative_viaFatEllentuck
    {κ : Type w} [Fintype κ]
    (H : SMTree S) (n : Nat)
    (B : ShapeSubspace H n)
    (colour : RamseyApprox H (n + 1) → κ) :
    ∃ W : ShapeSubspace H n,
      RamseyReduction H W.1 B.1 ∧
      ∀ K L : ShapeSubspace H n,
        colour (ramseyApprox H (n + 1) (MMap.comp H W.1 K.1)) =
          colour (ramseyApprox H (n + 1) (MMap.comp H W.1 L.1)) := by
  classical
  exact H.shapeRamsey_one_relative_of_oneDimensional
    n (FatTree.shapeOneDimensionalRamsey_viaFatEllentuck H n) B colour

/-- One backward product step whose local pigeonhole input comes from
fat-tree Ellentuck. -/
noncomputable def buildShapeProductStep_viaFatEllentuck
    [Fintype κ]
    (H : SMTree S)
    (default : κ)
    {n m : Nat} (hnm : n < m)
    (B : ShapeSubspace H n)
    (nextColour : RamseyApprox H (m + 1) → κ) :
    ShapeProductStep H n m B nextColour :=
  H.buildShapeProductStep_of_localPigeonhole
    default hnm B nextColour
    (FatTree.shapeLocalPigeonhole_viaFatEllentuck H
      (H.singleLevelStepColour default m nextColour))

/-- Relative finite-dimensional homogeneity, with all pigeonhole input supplied
by fat-tree Ellentuck. -/
theorem shapeRamsey_approximations_viaFatEllentuck
    {κ : Type w} [Fintype κ]
    (H : SMTree S) (n : Nat) :
    ∀ (k : Nat) (B : ShapeSubspace H n)
      (colour : RamseyApprox H (n + k) → κ),
      ∃ W : ShapeSubspace H n,
        RamseyReduction H W.1 B.1 ∧
        ∀ K L : ShapeSubspace H n,
          colour (ramseyApprox H (n + k) (MMap.comp H W.1 K.1)) =
            colour (ramseyApprox H (n + k) (MMap.comp H W.1 L.1)) := by
  classical
  exact H.shapeRamsey_approximations_of_oneDimensional
    n (fun m c => FatTree.shapeOneDimensionalRamsey_viaFatEllentuck H m c)

/-- Alternative proof of the paper's finite-dimensional shape-preserving
Ramsey theorem, derived from fat-tree Ellentuck. -/
theorem shapePreservingRamsey_viaFatEllentuck
    {κ : Type w} [Fintype κ]
    (H : SMTree S) (n k : Nat)
    (colour : AM H n k → κ) :
    ∃ W : ShapeSubspace H n,
      ∀ a b : AM H n k,
        colour (H.shapeActK n k W a) =
          colour (H.shapeActK n k W b) := by
  classical
  exact H.shapePreservingRamsey_of_oneDimensional
    (fun m c => FatTree.shapeOneDimensionalRamsey_viaFatEllentuck H m c)
    n k colour

end SMTree
end SuccessorTree

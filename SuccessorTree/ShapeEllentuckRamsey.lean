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

import SuccessorTree.ShapeFiniteInduction

/-!
# The finite-dimensional Ramsey theorem for shape-preserving functions

The one-moving-level case comes from the two large-set fusions. The relative
reduction and finite-dimensional induction are shared with the alternative
fat-tree Ellentuck proof in `ShapeFiniteInduction`.

No Ellentuck amalgamation hypothesis or fat-tree projection is used.
The shared relative theorem supports prescribed subspaces and width zero.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- The paper's finite-dimensional Ramsey theorem: for every finite colouring
of AM^n_k, some F in M^n makes all Fg, g in AM^n_k, the same colour. -/
theorem shapePreservingRamsey
    {κ : Type w} [Fintype κ]
    (H : SMTree S) (n k : Nat)
    (colour : AM H n k → κ) :
    ∃ W : ShapeSubspace H n,
      ∀ a b : AM H n k,
        colour (H.shapeActK n k W a) =
          colour (H.shapeActK n k W b) := by
  classical
  exact H.shapePreservingRamsey_of_oneDimensional
    (fun m c => H.shapeOneDimensionalRamsey m c) n k colour

end SMTree
end SuccessorTree

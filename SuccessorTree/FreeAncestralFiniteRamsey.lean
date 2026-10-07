import SuccessorTree.FreeAncestralSMTree
import SuccessorTree.ShapeFiniteRamsey

/-!
# Finite Ramsey theorem for free ancestral history shapes

This is the first application of the generic finite-dimensional successor-tree
theorem to the concrete history tree used in the girth-five forest project.
It has no additional pigeonhole or duplication hypotheses: M1--M3 are
provided by `freeSMTree`.
-/

namespace SuccessorTree
namespace FreeAncestral

universe u w

variable {Label : Type u} [Fintype Label] [Nonempty Label]

theorem finiteShapeRamsey
    (arity n k : Nat) {κ : Type w} [Fintype κ]
    (colour :
      SMTree.AM (freeSMTree (Label := Label) (arity := arity)) n k → κ) :
    ∃ W :
        SMTree.ShapeSubspace
          (freeSMTree (Label := Label) (arity := arity)) n,
      ∀ a b :
          SMTree.AM
            (freeSMTree (Label := Label) (arity := arity)) n k,
        colour
          ((freeSMTree (Label := Label) (arity := arity)).shapeActK
            n k W a) =
        colour
          ((freeSMTree (Label := Label) (arity := arity)).shapeActK
            n k W b) := by
  exact
    (freeSMTree (Label := Label) (arity := arity)).shapePreservingRamsey
      n k colour

end FreeAncestral
end SuccessorTree

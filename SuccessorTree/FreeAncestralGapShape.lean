import SuccessorTree.FreeAncestralGapMap
import SuccessorTree.ShapePreserving

/-! # One-gap shape maps on the free ancestral tree -/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat} [Fintype Label]

/-- The raw one-gap map packaged as a shape-preserving map. -/
noncomputable def oneGapShapeMap
    (m : Nat)
    (choose : History Label arity m → Code Label arity m) :
    ShapeMap (freeSTree (Label := Label) (arity := arity)) where
  toFun := gapNode m choose
  injective' := gapNode_injective m choose
  level_preserving' := by
    intro a b hab
    exact gapNode_level_eq_of_level_eq m choose hab
  weak_succ' := by
    intro a b p c h
    exact gapNode_weak_succ m choose h
  root_le' := by
    intro a ha
    exact root_le_gapNode m choose ha

@[simp] theorem oneGapShapeMap_apply
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (x : Node Label arity) :
    oneGapShapeMap m choose x = gapNode m choose x := rfl

end FreeAncestral
end SuccessorTree

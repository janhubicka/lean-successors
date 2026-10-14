import SuccessorTree.ShapeFiniteInduction

/-!
# The finite-dimensional Ramsey theorem for shape-preserving functions

The one-moving-level case comes from the two large-set fusions. The relative
reduction and finite-dimensional induction are shared with the alternative
fat-tree Ellentuck proof in `ShapeFiniteInduction`.

No Ellentuck amalgamation hypothesis or fat-tree projection is used.
The relative theorem includes an arbitrary prescribed subspace and width zero.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- One-moving-level homogeneity inside a prescribed subspace. -/
theorem shapeRamsey_one_relative
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
    n (H.shapeOneDimensionalRamsey n) B colour

/-- Relative finite-dimensional homogeneity in absolute approximation
coordinates. The right factors preserve exactly the requested frozen prefix. -/
theorem shapeRamsey_approximations
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
    n (fun m c => H.shapeOneDimensionalRamsey m c)

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

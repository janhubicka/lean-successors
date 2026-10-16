import SuccessorTree.FatTree.ProjectionTransfer
import SuccessorTree.FatTree.Amalgamation

/-!
# An exact obstruction criterion for the Section 4 projection

This file contains *theorems*, not axioms. They describe what a
family of arbitrarily late bad geometric refinements implies about
the canonical projection `associatedMap : FatTree H → MMap H`.

The originally proposed equality
`π[[x,U]] = [F_x,F_U]` would force a geometric reduction
`V ≤fat U` to project to a right-composition factor of `F_U`.
It is enough to find one image outside `range(F_U)` to disprove
that implication. An arbitrarily late family of such reductions
then shows that the preimage of the monoid cone `[∅,F_U]`
is not open at `U`, using exactly the basis of fat-tree
neighbourhoods, not an ad hoc topology.

The purely combinatorial `BadProjectedDepthCones` hypothesis
is *not* installed as a class assumption. The concrete
free-ancestral counterexample remains a separate formalization
task; its all-level construction and finite regressions are
documented in the wiki.

This module is independent of V10 and does not weaken or change
M1--M3 or the verified fat-tree Ellentuck theorem.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

/-- An image of V outside the range of the associated map of U
rules out every possible right-composition factor, even one
that is not shape preserving. -/
theorem not_projectedReduction_of_missing_image
    (H : SMTree S) (U V : FatTree H) (a : T)
    (hOutside :
      ∀ b : T, associatedMap H V a ≠ associatedMap H U b) :
    ¬ RamseyReduction H (associatedMap H V) (associatedMap H U) := by
  rintro ⟨G, hG⟩
  exact hOutside (G a) (hG a)

/-- A bad fat-tree refinement exists while preserving every finite
initial segment of U. This is a *property* to be disproved or
witnessed in a particular SMTree instance, never an extra axiom
imposed on SMTree. -/
def BadProjectedDepthCones (H : SMTree S) (U : FatTree H) : Prop :=
  ∀ n : Nat, ∃ V : FatTree H,
    InDepthCone H n U V ∧
    ¬ RamseyReduction H (associatedMap H V) (associatedMap H U)

/-- Every fat-tree basic neighbourhood containing U then
contains a projected map which is not a right-composition
factor of F_U. This follows just from transitivity of the
geometric fat reduction and literal preservation of the stem. -/
theorem badProjectedDepthCones_meet_every_fat_neighborhood
    (H : SMTree S) (U : FatTree H)
    (hBad : BadProjectedDepthCones H U)
    (x : FiniteFatTree H) (W : FatTree H)
    (hUW : InNeighborhood H x W U) :
    ∃ V : FatTree H,
      InNeighborhood H x W V ∧
      ¬ RamseyReduction H (associatedMap H V) (associatedMap H U) := by
  obtain ⟨V, hVU, hVnot⟩ := hBad x.height
  refine ⟨V, ⟨FatTree.reduces_trans H hVU.1 hUW.1, ?_⟩, hVnot⟩
  exact extendsStem_of_depthCone H hUW.2 hVU le_rfl

/-- The preimage of the right-composition cone below F_U
fails to contain *any* fat-tree basic neighbourhood of U,
provided U has bad projected refinements at every depth.

This is the exact basis-level failure of continuity claimed
in the manuscript. It does not assert that the monoid
Ellentuck theorem itself is false. -/
theorem projected_rightFactorCone_not_neighborhood
    (H : SMTree S) (U : FatTree H)
    (hBad : BadProjectedDepthCones H U)
    (x : FiniteFatTree H) (W : FatTree H)
    (hUW : InNeighborhood H x W U) :
    ¬ (∀ V : FatTree H,
        InNeighborhood H x W V →
        RamseyReduction H (associatedMap H V) (associatedMap H U)) := by
  intro hIncluded
  obtain ⟨V, hV, hVnot⟩ :=
    badProjectedDepthCones_meet_every_fat_neighborhood H U hBad x W hUW
  exact hVnot (hIncluded V hV)

end SuccessorTree.SMTree.FatTree

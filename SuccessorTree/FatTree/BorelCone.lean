import SuccessorTree.FatTree.PointwiseBorel
import SuccessorTree.FatTree.RelativeEA
import Mathlib.Topology.Constructions
import Mathlib.Topology.Baire.BaireMeasurable

/-!
# Pointwise-Borel EA1 colouring of complete algebraic cones

The corrected manuscript uses rho_F(U) = F ∘ associatedMap(U), not the
uncomposed fat-tree projection. Left composition is pointwise continuous
because each evaluation at x is F(associatedMap(U)(x)) and the tree is
discrete. Hence every pointwise-Borel colouring pulls back to fat-tree
Ellentuck Baire colour fibres.

EA1 covers a whole algebraic cone by a homogeneous fat image. EA2 is
not assumed. No full monoid Ellentuck theorem or concrete EA instance
is asserted.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v w
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable (H : SMTree S)

section Pointwise
local instance : TopologicalSpace T := ⊥
local instance : DiscreteTopology T := ⟨rfl⟩

/-- The actual relative Section 4 projection rho_F remains pointwise
continuous after postcomposing by an arbitrary fixed monoid map. -/
theorem relativeAssociatedMap_pointwiseContinuous (F : MMap H) :
    @Continuous (FatTree H) (MMap H)
      (approximationSystem H).ellentuckTopology
      (pointwiseTopology H)
      (fun U => MMap.comp H F (associatedMap H U)) := by
  letI : TopologicalSpace (FatTree H) :=
    (approximationSystem H).ellentuckTopology
  change @Continuous (FatTree H) (MMap H)
    (approximationSystem H).ellentuckTopology
    (TopologicalSpace.induced
      (fun G : MMap H => (fun x : T => G x))
      (inferInstance : TopologicalSpace (T → T)))
    (fun U => MMap.comp H F (associatedMap H U))
  rw [continuous_induced_rng]
  apply continuous_pi
  intro x
  change Continuous (fun U : FatTree H => F (associatedMap H U x))
  exact (continuous_of_discreteTopology :
    Continuous (fun y : T => F y)).comp
      (continuous_associatedMap_eval H x)

end Pointwise

/-- A pointwise-Borel finite colouring is constant on a *whole*
algebraic right-composition cone whenever the local EA1 covering
hypothesis holds. This strengthens the unconditional fat-image
conclusion exactly as in Section 4, and does not invoke EA2. -/
theorem coneHomogeneous_of_pointwiseBorel_and_EA1
    {κ : Type w} [Fintype κ]
    {n : Nat} (a : (approximationSystem H).Approx n)
    (U : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a U d)
    (hne : ((approximationSystem H).neighborhood a U).Nonempty)
    (F : MMap H)
    (pure : Set (MMap H))
    (cone : MMap H → Set (MMap H))
    (hLift : ∀ V,
      V ∈ (approximationSystem H).levelNeighborhood d U →
      ∃ F' : MMap H, F' ∈ pure ∧ (cone F').Nonempty ∧
        cone F' ⊆
          (fun W => MMap.comp H F (associatedMap H W)) ''
            ((approximationSystem H).neighborhood a V))
    (colour : MMap H → κ)
    (hBorel : ∀ c : κ,
      @MeasurableSet (MMap H) (pointwiseBorel H)
        {G | colour G = c}) :
    ∃ F' : MMap H, F' ∈ pure ∧ (cone F').Nonempty ∧
      ∃ c : κ, ∀ G ∈ cone F', colour G = c := by
  let rho : FatTree H → MMap H :=
    fun W => MMap.comp H F (associatedMap H W)
  have hBaire : ∀ c : κ,
      @BaireMeasurableSet (FatTree H)
        (approximationSystem H).ellentuckTopology
        {W | colour (rho W) = c} := by
    intro c
    letI : TopologicalSpace (FatTree H) :=
      (approximationSystem H).ellentuckTopology
    letI : TopologicalSpace (MMap H) := pointwiseTopology H
    letI : MeasurableSpace (FatTree H) := borel (FatTree H)
    letI : MeasurableSpace (MMap H) := pointwiseBorel H
    letI : BorelSpace (FatTree H) := ⟨rfl⟩
    letI : BorelSpace (MMap H) := ⟨rfl⟩
    have hcont : Continuous rho :=
      relativeAssociatedMap_pointwiseContinuous H F
    have hpre :
        MeasurableSet {W : FatTree H | colour (rho W) = c} :=
      (hBorel c).preimage hcont.measurable
    exact hpre.baireMeasurableSet
  exact coneHomogeneous_of_BairePullback_and_lifting H a U hd hne
    rho pure cone hLift colour hBaire

end SuccessorTree.SMTree.FatTree

import SuccessorTree.FatTree.SourceTheorems

/-!
# Product continuity of the actual fat-tree projection

The topology on fat trees is induced by their sequences of discrete finite
approximations. This is the product topology used in the manuscript's
continuity lemma, before passage to the finer fat Ellentuck topology.
The proof factors each source-node evaluation through one finite stem.
No finiteness of the set of nodes on a level is required for this step.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable (H : SMTree S)

section Product

local instance fatApproxTopology (n : Nat) :
    TopologicalSpace ((approximationSystem H).Approx n) := ⊥
local instance fatApproxDiscreteTopology (n : Nat) :
    DiscreteTopology ((approximationSystem H).Approx n) := ⟨rfl⟩

/-- Product topology of the discrete finite-approximation coordinates. -/
noncomputable def approximationProductTopology : TopologicalSpace (FatTree H) :=
  TopologicalSpace.induced
    (fun U : FatTree H => fun n : Nat => (approximationSystem H).approx n U)
    (inferInstance : TopologicalSpace
      (∀ n : Nat, (approximationSystem H).Approx n))

theorem continuous_fatApprox_product (n : Nat) :
    @Continuous (FatTree H) ((approximationSystem H).Approx n)
      (approximationProductTopology H) ⊥
      ((approximationSystem H).approx n) := by
  letI : TopologicalSpace (FatTree H) := approximationProductTopology H
  have hcode : Continuous
      (fun U : FatTree H => fun k : Nat => (approximationSystem H).approx k U) :=
    continuous_induced_dom
  exact (continuous_apply n).comp hcode

local instance : TopologicalSpace T := ⊥
local instance : DiscreteTopology T := ⟨rfl⟩

/-- A node on level n sees only the discrete approximation of length n+1. -/
theorem associatedMap_eval_productContinuous (x : T) :
    @Continuous (FatTree H) T (approximationProductTopology H) ⊥
      (fun U => associatedMap H U x) := by
  letI : TopologicalSpace (FatTree H) := approximationProductTopology H
  let read : (approximationSystem H).Approx (LevelTree.lev x + 1) → T :=
    fun a => (carriedApprox H a).1 ⟨x, le_rfl⟩
  have heq :
      (fun U : FatTree H => associatedMap H U x) =
      (fun U : FatTree H =>
        read ((approximationSystem H).approx (LevelTree.lev x + 1) U)) := by
    funext U
    have h := associatedMap_approx_eq_carriedApprox H
      ((approximationSystem H).approx (LevelTree.lev x + 1) U) U rfl
    exact congrFun (congrArg Subtype.val h) ⟨x, le_rfl⟩
  rw [heq]
  exact (continuous_of_discreteTopology : Continuous read).comp
    (continuous_fatApprox_product H (LevelTree.lev x + 1))

/-- The manuscript's continuity assertion for pi, in the product source
topology and the actual pointwise target topology. -/
theorem associatedMap_productContinuous :
    @Continuous (FatTree H) (MMap H)
      (approximationProductTopology H) (pointwiseTopology H)
      (associatedMap H) := by
  letI : TopologicalSpace (FatTree H) := approximationProductTopology H
  change @Continuous (FatTree H) (MMap H)
    (approximationProductTopology H)
    (TopologicalSpace.induced
      (fun F : MMap H => (fun x : T => F x))
      (inferInstance : TopologicalSpace (T → T)))
    (associatedMap H)
  apply continuous_induced_rng.mpr
  exact continuous_pi (fun x => associatedMap_eval_productContinuous H x)

/-- The same product-source continuity for rho_F(U)=F∘pi(U). -/
theorem relativeAssociatedMap_productContinuous (F : MMap H) :
    @Continuous (FatTree H) (MMap H)
      (approximationProductTopology H) (pointwiseTopology H)
      (fun U => MMap.comp H F (associatedMap H U)) := by
  letI : TopologicalSpace (FatTree H) := approximationProductTopology H
  change @Continuous (FatTree H) (MMap H)
    (approximationProductTopology H)
    (TopologicalSpace.induced
      (fun G : MMap H => (fun x : T => G x))
      (inferInstance : TopologicalSpace (T → T)))
    (fun U => MMap.comp H F (associatedMap H U))
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  change Continuous (fun U : FatTree H => F (associatedMap H U x))
  exact (continuous_of_discreteTopology :
    Continuous (fun y : T => F y)).comp
      (associatedMap_eval_productContinuous H x)

end Product

end SuccessorTree.SMTree.FatTree

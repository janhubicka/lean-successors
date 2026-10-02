import SuccessorTree.ShapeFrontPigeonhole
import SuccessorTree.ShapeFusion
import Mathlib.Tactic

/-!
# Direct fusion by simultaneous finite-front replay

At stage e we process the whole finite front of depth e+1 with one product
colouring and one common M3 replay block.  The chosen block fixes everything
below e+1, so these stages form an ordinary M1 fusion sequence.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- The finite set of all approximations having exactly depth d in B. -/
noncomputable def depthFrontFinset
    (H : SMTree S) (B : MMap H) (d : Nat) :
    Finset (ramseyApproximationSystem H).FiniteApprox :=
  ((ramseyFinitization H).depthApproximations_finite B d).toFinset

theorem mem_depthFrontFinset
    (H : SMTree S) (B : MMap H) (d : Nat)
    (p : (ramseyApproximationSystem H).FiniteApprox) :
    p ∈ H.depthFrontFinset B d ↔
      (ramseyFinitization H).HasDepth p.2 B d := by
  classical
  rcases p with ⟨n, a⟩
  simpa [depthFrontFinset] using
    (Finitization.mem_depthApproximations
      (F := ramseyFinitization H) (n := n) (d := d) (a := a) (B := B))

/-- Common replay block selected for the full depth-(e+1) front. -/
noncomputable def depthFrontReplayBlock
    [Fintype κ]
    (H : SMTree S)
    (colour : (n : Nat) → RamseyApprox H (n + 1) → κ)
    (B : MMap H) (e : Nat) :
    ReplayBlock H (e + 1) := by
  let P := H.depthFrontFinset B (e + 1)
  have hdepth :
      ∀ p ∈ P, (ramseyFinitization H).HasDepth p.2 B (e + 1) := by
    intro p hp
    exact (H.mem_depthFrontFinset B (e + 1) p).1 hp
  exact Classical.choose
    (H.finiteDepthFront_replay_pigeonhole colour B e P hdepth)

theorem depthFrontReplayBlock_spec
    [Fintype κ]
    (H : SMTree S)
    (colour : (n : Nat) → RamseyApprox H (n + 1) → κ)
    (B : MMap H) (e : Nat) :
    let P := H.depthFrontFinset B (e + 1)
    let R := H.depthFrontReplayBlock colour B e
    ∀ p : {p // p ∈ P},
      ∀ x : LineInput (OneLevelLetter H (e + 1)),
        colour p.1.1
            (H.frontReplayApply B e p.1
              ((H.mem_depthFrontFinset B (e + 1) p.1).1 p.2) R x) =
          colour p.1.1
            (H.frontReplayApply B e p.1
              ((H.mem_depthFrontFinset B (e + 1) p.1).1 p.2)
              R LineInput.base) := by
  classical
  dsimp only
  let P := H.depthFrontFinset B (e + 1)
  have hdepth :
      ∀ p ∈ P, (ramseyFinitization H).HasDepth p.2 B (e + 1) := by
    intro p hp
    exact (H.mem_depthFrontFinset B (e + 1) p).1 hp
  have hs := Classical.choose_spec
    (H.finiteDepthFront_replay_pigeonhole colour B e P hdepth)
  intro p x
  exact hs p x

/-- One whole-front replay refinement. -/
noncomputable def depthFrontReplayNext
    [Fintype κ]
    (H : SMTree S)
    (colour : (n : Nat) → RamseyApprox H (n + 1) → κ)
    (B : MMap H) (e : Nat) : MMap H :=
  MMap.comp H B
    (H.depthFrontReplayBlock colour B e).toMMap

/-- A whole-front replay refinement is exactly a fusion step at stage e. -/
theorem depthFrontReplayNext_step
    [Fintype κ]
    (H : SMTree S)
    (colour : (n : Nat) → RamseyApprox H (n + 1) → κ)
    (B : MMap H) (e : Nat) :
    FusionStep H e B (H.depthFrontReplayNext colour B e) := by
  refine ⟨(H.depthFrontReplayBlock colour B e).toMMap, ?_, rfl⟩
  exact (H.depthFrontReplayBlock colour B e).fixesBelow

/-- Recursive stages which process depth 1, depth 2, ... in order. -/
noncomputable def replayFrontStage
    [Fintype κ]
    (H : SMTree S)
    (colour : (n : Nat) → RamseyApprox H (n + 1) → κ)
    (B : MMap H) : Nat → MMap H
  | 0 => B
  | e + 1 =>
      H.depthFrontReplayNext colour
        (H.replayFrontStage colour B e) e

@[simp] theorem replayFrontStage_zero
    [Fintype κ]
    (H : SMTree S)
    (colour : (n : Nat) → RamseyApprox H (n + 1) → κ)
    (B : MMap H) :
    H.replayFrontStage colour B 0 = B := rfl

@[simp] theorem replayFrontStage_succ
    [Fintype κ]
    (H : SMTree S)
    (colour : (n : Nat) → RamseyApprox H (n + 1) → κ)
    (B : MMap H) (e : Nat) :
    H.replayFrontStage colour B (e + 1) =
      H.depthFrontReplayNext colour
        (H.replayFrontStage colour B e) e := rfl

theorem replayFrontStage_step
    [Fintype κ]
    (H : SMTree S)
    (colour : (n : Nat) → RamseyApprox H (n + 1) → κ)
    (B : MMap H) (e : Nat) :
    FusionStep H e
      (H.replayFrontStage colour B e)
      (H.replayFrontStage colour B (e + 1)) := by
  exact H.depthFrontReplayNext_step colour
    (H.replayFrontStage colour B e) e

/-- The M1 diagonal limit of the simultaneous-front replay construction. -/
noncomputable def replayFrontFusion
    [Fintype κ]
    (H : SMTree S)
    (colour : (n : Nat) → RamseyApprox H (n + 1) → κ)
    (B : MMap H) : MMap H :=
  H.fusionOfSteps
    (H.replayFrontStage colour B)
    (H.replayFrontStage_step colour B)

/-- The final replay-front fusion refines every finite stage. -/
theorem replayFrontFusion_reduction_stage
    [Fintype κ]
    (H : SMTree S)
    (colour : (n : Nat) → RamseyApprox H (n + 1) → κ)
    (B : MMap H) (e : Nat) :
    RamseyReduction H
      (H.replayFrontFusion colour B)
      (H.replayFrontStage colour B e) := by
  exact H.fusionOfSteps_reduction_stage
    (H.replayFrontStage colour B)
    (H.replayFrontStage_step colour B) e

/-- At stage e+1 the common chosen block makes every canonical local line on
the entire depth-(e+1) front monochromatic. -/
theorem replayFrontStage_depth_lines_mono
    [Fintype κ]
    (H : SMTree S)
    (colour : (n : Nat) → RamseyApprox H (n + 1) → κ)
    (B : MMap H) (e : Nat) :
    let F := H.replayFrontStage colour B e
    let P := H.depthFrontFinset F (e + 1)
    let R := H.depthFrontReplayBlock colour F e
    ∀ p : {p // p ∈ P},
      ∀ x : LineInput (OneLevelLetter H (e + 1)),
        colour p.1.1
            (H.frontReplayApply F e p.1
              ((H.mem_depthFrontFinset F (e + 1) p.1).1 p.2) R x) =
          colour p.1.1
            (H.frontReplayApply F e p.1
              ((H.mem_depthFrontFinset F (e + 1) p.1).1 p.2)
              R LineInput.base) := by
  exact H.depthFrontReplayBlock_spec colour
    (H.replayFrontStage colour B e) e

end SMTree
end SuccessorTree

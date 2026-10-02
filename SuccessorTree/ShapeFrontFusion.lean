import SuccessorTree.ShapeFusion
import SuccessorTree.RamseySpace.Nonempty

/-!
# Front-by-front finite fusion

This is the ordinary Milliken/Nash-Williams fusion engine.  It uses only

* A2 finiteness of each depth front;
* nonemptiness of finite neighborhoods (the finite factorization A3(1));
* a one-step pigeonhole principle;
* the M1 pointwise fusion limit.

No A3(2)/EA, fat trees, or abstract Ellentuck theorem is used here.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- A family of finite colourings of one-step approximations, one colouring
for each approximation level. -/
abbrev StepColouring (H : SMTree S) (κ : Type w) :=
  (n : Nat) → RamseyApprox H (n + 1) → κ

/-- All one-step extensions of a finite approximation below B have one
colour. -/
def OneStepHomogeneous
    (H : SMTree S) {κ : Type w}
    (colour : StepColouring H κ)
    (p : (ramseyApproximationSystem H).FiniteApprox)
    (B : MMap H) : Prop :=
  ∃ c : κ, ∀ b,
    b ∈ (ramseyApproximationSystem H).oneStepApproximations p.2 B →
      colour p.1 b = c

/-- The local pigeonhole principle needed by ordinary fusion. -/
def LocalPigeonhole
    (H : SMTree S) {κ : Type w}
    (colour : StepColouring H κ) : Prop :=
  ∀ (p : (ramseyApproximationSystem H).FiniteApprox)
    (B : MMap H) (d : Nat),
    0 < d →
    (ramseyFinitization H).HasDepth p.2 B d →
    ∃ A : MMap H,
      A ∈ (ramseyApproximationSystem H).levelNeighborhood d B ∧
      OneStepHomogeneous H colour p A

theorem oneStepHomogeneous_mono
    (H : SMTree S) {κ : Type w}
    {colour : StepColouring H κ}
    {p : (ramseyApproximationSystem H).FiniteApprox}
    {A B : MMap H}
    (hAB : RamseyReduction H A B)
    (hB : OneStepHomogeneous H colour p B) :
    OneStepHomogeneous H colour p A := by
  rcases hB with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro b hb
  exact hc b
    ((ramseyApproximationSystem H).oneStepApproximations_mono hAB hb)

/-- Process a finite list of depth-d approximations one by one, preserving
all decisions already made. -/
private theorem refineFiniteFront
    [Fintype κ]
    (H : SMTree S)
    (colour : StepColouring H κ)
    (hpig : LocalPigeonhole H colour)
    (B : MMap H) (d : Nat)
    (hdpos : 0 < d)
    (P : Finset (ramseyApproximationSystem H).FiniteApprox)
    (hdepth :
      ∀ p ∈ P, (ramseyFinitization H).HasDepth p.2 B d) :
    ∃ A : MMap H,
      A ∈ (ramseyApproximationSystem H).levelNeighborhood d B ∧
      ∀ p ∈ P, OneStepHomogeneous H colour p A := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      refine ⟨B,
        (ramseyApproximationSystem H).self_mem_levelNeighborhood d B, ?_⟩
      simp
  | @insert p P hp ih =>
      have hdepthP :
          ∀ q ∈ P, (ramseyFinitization H).HasDepth q.2 B d := by
        intro q hq
        exact hdepth q (by simp [hq])
      obtain ⟨A, hAB, hhomP⟩ := ih hdepthP
      have hpB : (ramseyFinitization H).HasDepth p.2 B d :=
        hdepth p (by simp)
      have hpA : (ramseyFinitization H).HasDepth p.2 A d := by
        exact ((ramseyFinitization H).hasDepth_iff_of_mem_levelNeighborhood
          hAB).2 hpB
      obtain ⟨A', hA'A, hpHom⟩ := hpig p A d hdpos hpA
      have hA'B :
          A' ∈ (ramseyApproximationSystem H).levelNeighborhood d B :=
        (ramseyApproximationSystem H).levelNeighborhood_mono hAB hA'A
      refine ⟨A', hA'B, ?_⟩
      intro q hq
      have hcases : q = p ∨ q ∈ P := by
        simpa [hp] using hq
      rcases hcases with rfl | hqP
      · exact hpHom
      · exact H.oneStepHomogeneous_mono hA'A.1 (hhomP q hqP)

/-- At one depth, finitely many A2-front approximations can all be made
one-step homogeneous simultaneously. -/
theorem exists_depthFront_refinement
    [Fintype κ]
    (H : SMTree S)
    (colour : StepColouring H κ)
    (hpig : LocalPigeonhole H colour)
    (B : MMap H) (d : Nat)
    (hdpos : 0 < d) :
    ∃ A : MMap H,
      A ∈ (ramseyApproximationSystem H).levelNeighborhood d B ∧
      ∀ p,
        p ∈ (ramseyFinitization H).depthApproximations B d →
          OneStepHomogeneous H colour p A := by
  classical
  let P : Finset (ramseyApproximationSystem H).FiniteApprox :=
    ((ramseyFinitization H).depthApproximations_finite B d).toFinset
  have hdepth :
      ∀ p ∈ P, (ramseyFinitization H).HasDepth p.2 B d := by
    intro p hp
    have hp' :
        p ∈ (ramseyFinitization H).depthApproximations B d := by
      simpa [P] using hp
    exact hp'
  obtain ⟨A, hAB, hhom⟩ :=
    refineFiniteFront H colour hpig B d hdpos P hdepth
  refine ⟨A, hAB, ?_⟩
  intro p hp
  apply hhom p
  simpa [P] using hp

/-- Front-fusion stages.  Before the requested starting depth N we do
nothing. At step i we process the whole front of depth i+1 and then freeze
that depth forever. -/
noncomputable def frontFusionStage
    [Fintype κ]
    (H : SMTree S)
    (colour : StepColouring H κ)
    (hpig : LocalPigeonhole H colour)
    (N : Nat) (B : MMap H) : Nat → MMap H
  | 0 => B
  | i + 1 =>
      if h : N ≤ i + 1 then
        Classical.choose
          (H.exists_depthFront_refinement colour hpig
            (frontFusionStage H colour hpig N B i) (i + 1) (by omega))
      else
        frontFusionStage H colour hpig N B i

theorem frontFusionStage_succ_mem
    [Fintype κ]
    (H : SMTree S)
    (colour : StepColouring H κ)
    (hpig : LocalPigeonhole H colour)
    (N : Nat) (B : MMap H) (i : Nat) :
    frontFusionStage H colour hpig N B (i + 1) ∈
      (ramseyApproximationSystem H).levelNeighborhood (i + 1)
        (frontFusionStage H colour hpig N B i) := by
  classical
  rw [frontFusionStage]
  by_cases h : N ≤ i + 1
  · simp only [h, dif_pos]
    exact (Classical.choose_spec
      (H.exists_depthFront_refinement colour hpig
        (frontFusionStage H colour hpig N B i) (i + 1) (by omega))).1
  · simp only [h, dif_neg]
    exact (ramseyApproximationSystem H).self_mem_levelNeighborhood
      (i + 1) (frontFusionStage H colour hpig N B i)

theorem frontFusionStage_step
    [Fintype κ]
    (H : SMTree S)
    (colour : StepColouring H κ)
    (hpig : LocalPigeonhole H colour)
    (N : Nat) (B : MMap H) (i : Nat) :
    FusionStep H i
      (frontFusionStage H colour hpig N B i)
      (frontFusionStage H colour hpig N B (i + 1)) := by
  exact H.fusionStep_of_mem_levelNeighborhood
    (H.frontFusionStage_succ_mem colour hpig N B i)

/-- The ordinary diagonal limit which has decided every finite depth front
from N onward. -/
noncomputable def frontFusion
    [Fintype κ]
    (H : SMTree S)
    (colour : StepColouring H κ)
    (hpig : LocalPigeonhole H colour)
    (N : Nat) (B : MMap H) : MMap H :=
  H.fusionOfSteps
    (frontFusionStage H colour hpig N B)
    (H.frontFusionStage_step colour hpig N B)

/-- Once a depth d >= N has been processed, every approximation of depth d in
that stage is one-step homogeneous in the next stage. -/
theorem frontFusionStage_depth_homogeneous
    [Fintype κ]
    (H : SMTree S)
    (colour : StepColouring H κ)
    (hpig : LocalPigeonhole H colour)
    (N : Nat) (B : MMap H)
    {d : Nat} (hd : 0 < d) (hNd : N ≤ d)
    (p : (ramseyApproximationSystem H).FiniteApprox)
    (hp :
      p ∈ (ramseyFinitization H).depthApproximations
        (frontFusionStage H colour hpig N B (d - 1)) d) :
    OneStepHomogeneous H colour p
      (frontFusionStage H colour hpig N B d) := by
  classical
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  rw [frontFusionStage]
  simp only [show N ≤ i + 1 by exact hNd, dif_pos]
  exact (Classical.choose_spec
    (H.exists_depthFront_refinement colour hpig
      (frontFusionStage H colour hpig N B i) (i + 1) (by omega))).2 p hp

/-- Every finite approximation whose depth is at least N is one-step
homogeneous in the final fusion. -/
theorem frontFusion_homogeneous
    [Fintype κ]
    (H : SMTree S)
    (colour : StepColouring H κ)
    (hpig : LocalPigeonhole H colour)
    (N : Nat) (B : MMap H)
    (p : (ramseyApproximationSystem H).FiniteApprox)
    {d : Nat}
    (hd : (ramseyFinitization H).HasDepth p.2
      (H.frontFusion colour hpig N B) d)
    (hdpos : 0 < d) (hNd : N ≤ d) :
    OneStepHomogeneous H colour p
      (H.frontFusion colour hpig N B) := by
  let F : Nat → MMap H := frontFusionStage H colour hpig N B
  let hstep : ∀ i : Nat, FusionStep H i (F i) (F (i + 1)) :=
    H.frontFusionStage_step colour hpig N B
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
  have hlim :
      H.frontFusion colour hpig N B ∈
        (ramseyApproximationSystem H).levelNeighborhood d (F i) := by
    subst d
    simpa [frontFusion, F, hstep] using
      H.fusionOfSteps_mem_levelNeighborhood F hstep i
  have hpStage :
      (ramseyFinitization H).HasDepth p.2 (F i) d := by
    exact ((ramseyFinitization H).hasDepth_iff_of_mem_levelNeighborhood
      hlim).1 hd
  have hpMem :
      p ∈ (ramseyFinitization H).depthApproximations (F i) d :=
    hpStage
  have hhomNext :
      OneStepHomogeneous H colour p (F (i + 1)) := by
    subst d
    exact H.frontFusionStage_depth_homogeneous colour hpig N B
      (by omega) hNd p hpMem
  have hred :
      RamseyReduction H (H.frontFusion colour hpig N B) (F (i + 1)) := by
    dsimp [frontFusion, F, hstep]
    exact H.fusionOfSteps_reduction_stage
      (frontFusionStage H colour hpig N B)
      (H.frontFusionStage_step colour hpig N B)
      (i + 1)
  exact H.oneStepHomogeneous_mono hred hhomNext

end SMTree
end SuccessorTree

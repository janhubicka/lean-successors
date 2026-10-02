import SuccessorTree.ShapeReplayFusion
import SuccessorTree.RamseySpace.Nonempty
import Mathlib.Tactic

/-!
# Large sets of one-step shape approximations

This file isolates the Nash-Williams/Milliken largeness notion needed to
upgrade the verified M3 replay line to a full local one-step pigeonhole
principle.  It is deliberately phrased directly in the M-map Ramsey space;
no fat-tree projection or A.3(2)/EA is used.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- A genuine one-step extension has strictly larger finite depth. -/
theorem oneStep_hasDepth_strict
    (H : SMTree S)
    {n d e : Nat}
    {a : RamseyApprox H (n + 1)}
    {b : RamseyApprox H (n + 2)}
    {B : MMap H}
    (ha : (ramseyFinitization H).HasDepth (n := n + 1) a B (d + 1))
    (hbmem :
      b ∈ (ramseyApproximationSystem H).oneStepApproximations
        (n := n + 1) a B)
    (hb : (ramseyFinitization H).HasDepth (n := n + 2) b B e) :
    d + 1 < e := by
  have hab :
      (ramseyApproximationSystem H).IsInitial (n := n + 1) (m := n + 2) a b :=
    (ramseyApproximationSystem H).isInitial_oneStep hbmem
  have hle : d + 1 ≤ e :=
    (ramseyFinitization H).hasDepth_le_of_initial hab ha hb
  by_contra hnot
  have heq : e = d + 1 := by omega
  subst e
  have hfacB :
      Nonempty
        (RamseyFiniteFactor H b (ramseyApprox H (d + 1) B)) := by
    exact hb.1
  let facB : RamseyFiniteFactor H b (ramseyApprox H (d + 1) B) :=
    Classical.choice hfacB
  let facA : RamseyFiniteFactor H a (ramseyApprox H (d + 1) B) := {
    map := facB.map
    bound := by
      intro x
      exact facB.bound
        (⟨x.1, x.2.trans (Nat.le_succ n)⟩ : InitialNode T (n + 1))
    agrees := by
      intro x
      let y : InitialNode T (n + 1) :=
        ⟨x.1, x.2.trans (Nat.le_succ n)⟩
      calc
        a.1 x = b.1 y :=
          H.ramseyApprox_apply_of_initial hab x
        _ = (ramseyApprox H (d + 1) B).1
              ⟨facB.map y.1, facB.bound y⟩ :=
          facB.agrees y
        _ = (ramseyApprox H (d + 1) B).1
              ⟨facB.map x.1,
                facB.bound
                  (⟨x.1, x.2.trans (Nat.le_succ n)⟩ :
                    InitialNode T (n + 1))⟩ := by
          rfl
  }
  have htop :
      H.levelMap facB.map.map n = d := by
    simpa [facA] using
      H.ramseyFiniteFactor_topLevel_of_depth ha facA
  have hstrict :
      H.levelMap facB.map.map n <
        H.levelMap facB.map.map (n + 1) :=
    H.levelMap_strictMono facB.map.map (Nat.lt_succ_self n)
  obtain ⟨x, hx⟩ := H.level_nonempty (n + 1)
  let xx : InitialNode T (n + 1) := ⟨x, by simpa [hx]⟩
  have hupper :
      H.levelMap facB.map.map (n + 1) ≤ d := by
    calc
      H.levelMap facB.map.map (n + 1) =
          LevelTree.lev (facB.map x) := by
        simpa [hx] using H.levelMap_eq facB.map.map (a := x)
      _ ≤ d := facB.bound xx
  omega

/-- A set of one-step approximations is large below a finite prefix when
every same-depth refinement still realizes a member of the set. -/
def OneStepLarge
    (H : SMTree S)
    {n d : Nat}
    (a : RamseyApprox H (n + 1))
    (B : MMap H)
    (O : Set (RamseyApprox H (n + 2))) : Prop :=
  ∀ A : MMap H,
    A ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B →
      ∃ b : RamseyApprox H (n + 2),
        b ∈ (ramseyApproximationSystem H).oneStepApproximations
          (n := n + 1) a A ∧
        b ∈ O

/-- The full one-step set is large whenever the prefix has the indicated
positive depth. -/
theorem oneStepLarge_univ
    (H : SMTree S)
    {n d : Nat}
    (a : RamseyApprox H (n + 1))
    (B : MMap H)
    (ha : (ramseyFinitization H).HasDepth a B (d + 1)) :
    OneStepLarge H (d := d) a B Set.univ := by
  intro A hAB
  have haA :
      (ramseyFinitization H).HasDepth (n := n + 1) a A (d + 1) :=
    ((ramseyFinitization H).hasDepth_iff_of_mem_levelNeighborhood
      hAB).2 ha
  rcases H.fusionNeighborhood_nonempty a A haA
      ((ramseyApproximationSystem H).self_mem_levelNeighborhood
        (d + 1) A) with
    ⟨X, hX⟩
  let b : RamseyApprox H (n + 2) :=
    ramseyApprox H (n + 2) X
  refine ⟨b, ?_, Set.mem_univ b⟩
  exact ⟨X, hX, rfl⟩

/-- Largeness is inherited by same-depth refinements. -/
theorem oneStepLarge_mono
    (H : SMTree S)
    {n d : Nat}
    {a : RamseyApprox H (n + 1)}
    {A B : MMap H}
    {O : Set (RamseyApprox H (n + 2))}
    (hAB :
      A ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B)
    (hlarge : OneStepLarge H (d := d) a B O) :
    OneStepLarge H (d := d) a A O := by
  intro C hCA
  have hCB :
      C ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B :=
    (ramseyApproximationSystem H).levelNeighborhood_mono hAB hCA
  exact hlarge C hCB

/-- Finite-partition step for large sets: after a same-depth refinement, one
of two cells remains large. -/
theorem oneStepLarge_partition
    (H : SMTree S)
    {n d : Nat}
    {a : RamseyApprox H (n + 1)}
    {B : MMap H}
    {O O₀ O₁ : Set (RamseyApprox H (n + 2))}
    (hlarge : OneStepLarge H (d := d) a B O)
    (hcover : O ⊆ O₀ ∪ O₁) :
    ∃ A : MMap H,
      A ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B ∧
      (OneStepLarge H (d := d) a A O₀ ∨
        OneStepLarge H (d := d) a A O₁) := by
  classical
  by_cases h₀ : OneStepLarge H (d := d) a B O₀
  · exact ⟨B,
      (ramseyApproximationSystem H).self_mem_levelNeighborhood (d + 1) B,
      Or.inl h₀⟩
  · have hex :
        ∃ A : MMap H,
          A ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B ∧
          ¬ ∃ b : RamseyApprox H (n + 2),
              b ∈ (ramseyApproximationSystem H).oneStepApproximations
                (n := n + 1) a A ∧
              b ∈ O₀ := by
      by_contra hnone
      apply h₀
      intro A hAB
      by_contra hfail
      exact hnone ⟨A, hAB, hfail⟩
    rcases hex with ⟨A, hAB, havoid⟩
    refine ⟨A, hAB, Or.inr ?_⟩
    intro C hCA
    have hCB :
        C ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B :=
      (ramseyApproximationSystem H).levelNeighborhood_mono hAB hCA
    rcases hlarge C hCB with ⟨b, hbC, hbO⟩
    have hbA :
        b ∈ (ramseyApproximationSystem H).oneStepApproximations
          (n := n + 1) a A :=
      (ramseyApproximationSystem H).oneStepApproximations_mono hCA.1 hbC
    have hbnot₀ : b ∉ O₀ := by
      intro hb₀
      exact havoid ⟨b, hbA, hb₀⟩
    have hbcover : b ∈ O₀ ∪ O₁ := hcover hbO
    rcases hbcover with hb₀ | hb₁
    · exact False.elim (hbnot₀ hb₀)
    · exact ⟨b, hbC, hb₁⟩

end SMTree
end SuccessorTree

import SuccessorTree.ShapeLarge
import Mathlib.Tactic

/-!
# Exact-depth stabilization for large one-step sets

This is the direct M-map version of the usual Milliken/Nash-Williams
large-set diagonal argument. It avoids fat-tree projection entirely.

Starting with a large set of one-step extensions of a fixed prefix, either
some future depth is already persistent, or at each depth we can choose a
same-depth refinement avoiding all witnesses whose depth is the next one.
M1 fusion of those avoiding refinements would then avoid the large set
altogether, a contradiction.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

def OneStepExactPersistent
    (H : SMTree S)
    {n : Nat}
    (a : RamseyApprox H (n + 1))
    (A : MMap H)
    (O : Set (RamseyApprox H (n + 2)))
    (q : Nat) : Prop :=
  ∀ C : MMap H,
    C ∈ (ramseyApproximationSystem H).levelNeighborhood q A →
      ∃ b : RamseyApprox H (n + 2),
        b ∈ (ramseyApproximationSystem H).oneStepApproximations
          (n := n + 1) a C ∧
        b ∈ O ∧
        (ramseyFinitization H).HasDepth (n := n + 2) b C (q + 1)

theorem exists_exact_avoidance
    (H : SMTree S)
    {n q : Nat}
    {a : RamseyApprox H (n + 1)}
    {A : MMap H}
    {O : Set (RamseyApprox H (n + 2))}
    (hnot : ¬ OneStepExactPersistent H a A O q) :
    ∃ C : MMap H,
      C ∈ (ramseyApproximationSystem H).levelNeighborhood q A ∧
      ¬ ∃ b : RamseyApprox H (n + 2),
        b ∈ (ramseyApproximationSystem H).oneStepApproximations
          (n := n + 1) a C ∧
        b ∈ O ∧
        (ramseyFinitization H).HasDepth (n := n + 2) b C (q + 1) := by
  classical
  by_contra hnone
  apply hnot
  intro C hCA
  by_contra hb
  exact hnone ⟨C, hCA, hb⟩

theorem mem_levelNeighborhood_of_le
    (H : SMTree S)
    {A B : MMap H} {d e : Nat}
    (hde : d ≤ e)
    (hA :
      A ∈ (ramseyApproximationSystem H).levelNeighborhood e B) :
    A ∈ (ramseyApproximationSystem H).levelNeighborhood d B := by
  exact ⟨hA.1,
    (ramseyApproximationSystem H).approx_eq_of_mem_levelNeighborhood
      hA hde⟩

abbrev OneStepBaseRefinement
    (H : SMTree S) (B : MMap H) (d : Nat) :=
  {A : MMap H //
    A ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B}

noncomputable def oneStepAvoidNext
    (H : SMTree S)
    {n d : Nat}
    (a : RamseyApprox H (n + 1))
    (B : MMap H)
    (O : Set (RamseyApprox H (n + 2)))
    (hbad :
      ∀ A : MMap H,
        A ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B →
        ∀ q : Nat, d + 1 ≤ q →
          ¬ OneStepExactPersistent H a A O q)
    (i : Nat)
    (A : OneStepBaseRefinement H B d) :
    OneStepBaseRefinement H B d := by
  classical
  by_cases hi : d ≤ i
  · have hnot :
        ¬ OneStepExactPersistent H a A.1 O (i + 1) :=
      hbad A.1 A.2 (i + 1) (by omega)
    let C : MMap H :=
      Classical.choose (H.exists_exact_avoidance hnot)
    have hC :
        C ∈ (ramseyApproximationSystem H).levelNeighborhood (i + 1) A.1 :=
      (Classical.choose_spec (H.exists_exact_avoidance hnot)).1
    have hCbaseA :
        C ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) A.1 :=
      H.mem_levelNeighborhood_of_le (by omega) hC
    exact ⟨C,
      (ramseyApproximationSystem H).levelNeighborhood_mono A.2 hCbaseA⟩
  · exact A

theorem oneStepAvoidNext_mem
    (H : SMTree S)
    {n d : Nat}
    (a : RamseyApprox H (n + 1))
    (B : MMap H)
    (O : Set (RamseyApprox H (n + 2)))
    (hbad :
      ∀ A : MMap H,
        A ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B →
        ∀ q : Nat, d + 1 ≤ q →
          ¬ OneStepExactPersistent H a A O q)
    (i : Nat)
    (A : OneStepBaseRefinement H B d) :
    (H.oneStepAvoidNext a B O hbad i A).1 ∈
      (ramseyApproximationSystem H).levelNeighborhood (i + 1) A.1 := by
  classical
  by_cases hi : d ≤ i
  · simp only [oneStepAvoidNext, hi, dite_true]
    let hnot :
        ¬ OneStepExactPersistent H a A.1 O (i + 1) :=
      hbad A.1 A.2 (i + 1) (by omega)
    exact (Classical.choose_spec (H.exists_exact_avoidance hnot)).1
  · simp only [oneStepAvoidNext, hi, dite_false]
    exact (ramseyApproximationSystem H).self_mem_levelNeighborhood
      (i + 1) A.1

theorem oneStepAvoidNext_avoids
    (H : SMTree S)
    {n d : Nat}
    (a : RamseyApprox H (n + 1))
    (B : MMap H)
    (O : Set (RamseyApprox H (n + 2)))
    (hbad :
      ∀ A : MMap H,
        A ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B →
        ∀ q : Nat, d + 1 ≤ q →
          ¬ OneStepExactPersistent H a A O q)
    {i : Nat} (hi : d ≤ i)
    (A : OneStepBaseRefinement H B d) :
    ¬ ∃ b : RamseyApprox H (n + 2),
      b ∈ (ramseyApproximationSystem H).oneStepApproximations
        (n := n + 1) a (H.oneStepAvoidNext a B O hbad i A).1 ∧
      b ∈ O ∧
      (ramseyFinitization H).HasDepth (n := n + 2) b
        (H.oneStepAvoidNext a B O hbad i A).1 (i + 2) := by
  classical
  simp only [oneStepAvoidNext, hi, dite_true]
  let hnot :
      ¬ OneStepExactPersistent H a A.1 O (i + 1) :=
    hbad A.1 A.2 (i + 1) (by omega)
  simpa [Nat.add_assoc] using
    (Classical.choose_spec (H.exists_exact_avoidance hnot)).2

noncomputable def oneStepAvoidStage
    (H : SMTree S)
    {n d : Nat}
    (a : RamseyApprox H (n + 1))
    (B : MMap H)
    (O : Set (RamseyApprox H (n + 2)))
    (hbad :
      ∀ A : MMap H,
        A ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B →
        ∀ q : Nat, d + 1 ≤ q →
          ¬ OneStepExactPersistent H a A O q) :
    Nat → OneStepBaseRefinement H B d
  | 0 => ⟨B,
      (ramseyApproximationSystem H).self_mem_levelNeighborhood (d + 1) B⟩
  | i + 1 =>
      H.oneStepAvoidNext a B O hbad i
        (H.oneStepAvoidStage a B O hbad i)

theorem oneStepAvoidStage_step
    (H : SMTree S)
    {n d : Nat}
    (a : RamseyApprox H (n + 1))
    (B : MMap H)
    (O : Set (RamseyApprox H (n + 2)))
    (hbad :
      ∀ A : MMap H,
        A ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B →
        ∀ q : Nat, d + 1 ≤ q →
          ¬ OneStepExactPersistent H a A O q)
    (i : Nat) :
    FusionStep H i
      (H.oneStepAvoidStage a B O hbad i).1
      (H.oneStepAvoidStage a B O hbad (i + 1)).1 := by
  apply H.fusionStep_of_mem_levelNeighborhood
  change
    (H.oneStepAvoidNext a B O hbad i
      (H.oneStepAvoidStage a B O hbad i)).1 ∈
        (ramseyApproximationSystem H).levelNeighborhood (i + 1)
          (H.oneStepAvoidStage a B O hbad i).1
  exact H.oneStepAvoidNext_mem a B O hbad i
    (H.oneStepAvoidStage a B O hbad i)

theorem oneStepAvoidStage_avoids
    (H : SMTree S)
    {n d : Nat}
    (a : RamseyApprox H (n + 1))
    (B : MMap H)
    (O : Set (RamseyApprox H (n + 2)))
    (hbad :
      ∀ A : MMap H,
        A ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B →
        ∀ q : Nat, d + 1 ≤ q →
          ¬ OneStepExactPersistent H a A O q)
    {i : Nat} (hi : d ≤ i) :
    ¬ ∃ b : RamseyApprox H (n + 2),
      b ∈ (ramseyApproximationSystem H).oneStepApproximations
        (n := n + 1) a (H.oneStepAvoidStage a B O hbad (i + 1)).1 ∧
      b ∈ O ∧
      (ramseyFinitization H).HasDepth (n := n + 2) b
        (H.oneStepAvoidStage a B O hbad (i + 1)).1 (i + 2) := by
  change
    ¬ ∃ b : RamseyApprox H (n + 2),
      b ∈ (ramseyApproximationSystem H).oneStepApproximations
        (n := n + 1) a
          (H.oneStepAvoidNext a B O hbad i
            (H.oneStepAvoidStage a B O hbad i)).1 ∧
      b ∈ O ∧
      (ramseyFinitization H).HasDepth (n := n + 2) b
        (H.oneStepAvoidNext a B O hbad i
          (H.oneStepAvoidStage a B O hbad i)).1 (i + 2)
  exact H.oneStepAvoidNext_avoids a B O hbad hi
    (H.oneStepAvoidStage a B O hbad i)

theorem oneStepLarge_exact_persistent
    (H : SMTree S)
    {n d : Nat}
    (a : RamseyApprox H (n + 1))
    (B : MMap H)
    (ha : (ramseyFinitization H).HasDepth (n := n + 1) a B (d + 1))
    (O : Set (RamseyApprox H (n + 2)))
    (hlarge : OneStepLarge H (d := d) a B O) :
    ∃ A : MMap H,
      A ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B ∧
      ∃ q : Nat, d + 1 ≤ q ∧
        OneStepExactPersistent H a A O q := by
  classical
  by_contra hnone
  have hbad :
      ∀ A : MMap H,
        A ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B →
        ∀ q : Nat, d + 1 ≤ q →
          ¬ OneStepExactPersistent H a A O q := by
    intro A hAB q hq hpersist
    exact hnone ⟨A, hAB, q, hq, hpersist⟩
  let F : Nat → MMap H :=
    fun i => (H.oneStepAvoidStage a B O hbad i).1
  let hstep : ∀ i : Nat, FusionStep H i (F i) (F (i + 1)) :=
    H.oneStepAvoidStage_step a B O hbad
  let L : MMap H := H.fusionOfSteps F hstep
  have hLd :
      L ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) (F d) := by
    simpa [L, F, hstep] using
      H.fusionOfSteps_mem_levelNeighborhood F hstep d
  have hFd :
      F d ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B := by
    exact (H.oneStepAvoidStage a B O hbad d).2
  have hLB :
      L ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B :=
    (ramseyApproximationSystem H).levelNeighborhood_mono hFd hLd
  obtain ⟨b, hbL, hbO⟩ := hlarge L hLB
  rcases hbL with ⟨X, hXaL, hXb⟩
  have hXbL :
      X ∈ (ramseyApproximationSystem H).neighborhood (n := n + 2) b L :=
    ⟨hXaL.1, hXb⟩
  obtain ⟨e, hbe⟩ :=
    (ramseyFinitization H).exists_hasDepth_of_mem_neighborhood hXbL
  have haL :
      (ramseyFinitization H).HasDepth (n := n + 1) a L (d + 1) :=
    ((ramseyFinitization H).hasDepth_iff_of_mem_levelNeighborhood hLB).2 ha
  have hbL' :
      b ∈ (ramseyApproximationSystem H).oneStepApproximations
        (n := n + 1) a L :=
    ⟨X, hXaL, hXb⟩
  have hstrict : d + 1 < e :=
    H.oneStep_hasDepth_strict haL hbL' hbe
  let i : Nat := e - 2
  have hi : d ≤ i := by
    dsimp [i]
    omega
  have hie : i + 2 = e := by
    dsimp [i]
    omega
  have havoid :=
    H.oneStepAvoidStage_avoids a B O hbad hi
  have hred :
      RamseyReduction H L (F (i + 1)) := by
    simpa [L, F, hstep] using
      H.fusionOfSteps_reduction_stage F hstep (i + 1)
  have hbStage :
      b ∈ (ramseyApproximationSystem H).oneStepApproximations
        (n := n + 1) a (F (i + 1)) :=
    (ramseyApproximationSystem H).oneStepApproximations_mono hred hbL'
  have hLStage :
      L ∈ (ramseyApproximationSystem H).levelNeighborhood
        (i + 2) (F (i + 1)) := by
    simpa [L, F, hstep] using
      H.fusionOfSteps_mem_levelNeighborhood F hstep (i + 1)
  have hbeL :
      (ramseyFinitization H).HasDepth (n := n + 2) b L (i + 2) := by
    simpa [hie] using hbe
  have hbeStage :
      (ramseyFinitization H).HasDepth (n := n + 2) b (F (i + 1)) (i + 2) :=
    ((ramseyFinitization H).hasDepth_iff_of_mem_levelNeighborhood
      hLStage).1 hbeL
  exact havoid ⟨b, hbStage, hbO, hbeStage⟩

end SMTree
end SuccessorTree

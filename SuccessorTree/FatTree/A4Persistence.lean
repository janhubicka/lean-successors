import SuccessorTree.FatTree.A4Large
import SuccessorTree.FatTree.Closed
import RamseySpace.Fusion

/-!
# Exact-depth persistence for large fat-tree one-block sets

This is the fat-tree analogue of the exact-depth stabilization argument
already used for shape maps. It uses only A1--A3, the elementary one-block
largeness calculus, and a fusion-completeness parameter. Metric closedness
supplies that parameter later.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

def OneBlockExactPersistent
    (x : FiniteFatTree H) (A : FatTree H)
    (O : Set (AM H x.terminalCut 1))
    (q : Nat) : Prop :=
  ∀ C : FatTree H,
    InDepthCone H q A C →
      ∃ g : AM H x.terminalCut 1,
        g ∈ O ∧
        StemAt H (FiniteFatTree.appendRow H x g) C (q + 1)

theorem exists_exact_avoidance
    {x : FiniteFatTree H} {A : FatTree H}
    {O : Set (AM H x.terminalCut 1)} {q : Nat}
    (hnot : ¬ OneBlockExactPersistent H x A O q) :
    ∃ C : FatTree H,
      InDepthCone H q A C ∧
      ∀ g : AM H x.terminalCut 1,
        g ∈ O →
        ¬ StemAt H (FiniteFatTree.appendRow H x g) C (q + 1) := by
  classical
  unfold OneBlockExactPersistent at hnot
  push_neg at hnot
  rcases hnot with ⟨C, hCA, havoid⟩
  exact ⟨C, hCA, fun g hg => havoid g hg⟩

abbrev StemRefinement
    (x : FiniteFatTree H) (U : FatTree H) :=
  {A : FatTree H //
    FatTree.Reduces H A U ∧ ExtendsStem H x A}

noncomputable def exactAvoidNext
    {x : FiniteFatTree H} {U : FatTree H}
    {O : Set (AM H x.terminalCut 1)}
    (hbad :
      ∀ A : FatTree H,
        FatTree.Reduces H A U →
        ExtendsStem H x A →
        ∀ q : Nat, x.height ≤ q →
          ¬ OneBlockExactPersistent H x A O q)
    (i : Nat) (A : StemRefinement H x U) :
    StemRefinement H x U := by
  classical
  let q := x.height + i
  have hnot :
      ¬ OneBlockExactPersistent H x A.1 O q :=
    hbad A.1 A.2.1 A.2.2 q (by omega)
  let C : FatTree H :=
    Classical.choose (exists_exact_avoidance H hnot)
  have hC :
      InDepthCone H q A.1 C :=
    (Classical.choose_spec (exists_exact_avoidance H hnot)).1
  refine ⟨C, ?_, ?_⟩
  · exact FatTree.reduces_trans H hC.1 A.2.1
  · exact extendsStem_of_depthCone H A.2.2 hC (by
      dsimp [q]
      omega)

theorem exactAvoidNext_depth
    {x : FiniteFatTree H} {U : FatTree H}
    {O : Set (AM H x.terminalCut 1)}
    (hbad :
      ∀ A : FatTree H,
        FatTree.Reduces H A U →
        ExtendsStem H x A →
        ∀ q : Nat, x.height ≤ q →
          ¬ OneBlockExactPersistent H x A O q)
    (i : Nat) (A : StemRefinement H x U) :
    InDepthCone H (x.height + i) A.1
      (exactAvoidNext H hbad i A).1 := by
  classical
  let q := x.height + i
  have hnot :
      ¬ OneBlockExactPersistent H x A.1 O q :=
    hbad A.1 A.2.1 A.2.2 q (by omega)
  exact (Classical.choose_spec (exists_exact_avoidance H hnot)).1

theorem exactAvoidNext_avoids
    {x : FiniteFatTree H} {U : FatTree H}
    {O : Set (AM H x.terminalCut 1)}
    (hbad :
      ∀ A : FatTree H,
        FatTree.Reduces H A U →
        ExtendsStem H x A →
        ∀ q : Nat, x.height ≤ q →
          ¬ OneBlockExactPersistent H x A O q)
    (i : Nat) (A : StemRefinement H x U) :
    ∀ g : AM H x.terminalCut 1,
      g ∈ O →
      ¬ StemAt H (FiniteFatTree.appendRow H x g)
        (exactAvoidNext H hbad i A).1
        (x.height + i + 1) := by
  classical
  let q := x.height + i
  have hnot :
      ¬ OneBlockExactPersistent H x A.1 O q :=
    hbad A.1 A.2.1 A.2.2 q (by omega)
  intro g hg
  have hav :=
    (Classical.choose_spec (exists_exact_avoidance H hnot)).2 g hg
  have hidx : q + 1 = x.height + i + 1 := by
    dsimp [q]
    omega
  change
    ¬ StemAt H (FiniteFatTree.appendRow H x g)
      (exactAvoidNext H hbad i A).1
      (x.height + i + 1)
  unfold exactAvoidNext
  dsimp only
  rw [← hidx]
  exact hav

noncomputable def exactAvoidStage
    {x : FiniteFatTree H} {U : FatTree H}
    {O : Set (AM H x.terminalCut 1)}
    (hxU : ExtendsStem H x U)
    (hbad :
      ∀ A : FatTree H,
        FatTree.Reduces H A U →
        ExtendsStem H x A →
        ∀ q : Nat, x.height ≤ q →
          ¬ OneBlockExactPersistent H x A O q) :
    Nat → StemRefinement H x U
  | 0 => ⟨U, FatTree.reduces_refl H U, hxU⟩
  | i + 1 =>
      exactAvoidNext H hbad i
        (exactAvoidStage hxU hbad i)

theorem exactAvoidStage_step
    {x : FiniteFatTree H} {U : FatTree H}
    {O : Set (AM H x.terminalCut 1)}
    (hxU : ExtendsStem H x U)
    (hbad :
      ∀ A : FatTree H,
        FatTree.Reduces H A U →
        ExtendsStem H x A →
        ∀ q : Nat, x.height ≤ q →
          ¬ OneBlockExactPersistent H x A O q)
    (i : Nat) :
    (exactAvoidStage H hxU hbad (i + 1)).1 ∈
      (approximationSystem H).levelNeighborhood
        (x.height + i)
        (exactAvoidStage H hxU hbad i).1 := by
  apply (mem_levelNeighborhood_iff_depthCone H
    (x.height + i)
    (exactAvoidStage H hxU hbad i).1
    (exactAvoidStage H hxU hbad (i + 1)).1).2
  exact exactAvoidNext_depth H hbad i
    (exactAvoidStage H hxU hbad i)

theorem exactAvoidStage_avoids
    {x : FiniteFatTree H} {U : FatTree H}
    {O : Set (AM H x.terminalCut 1)}
    (hxU : ExtendsStem H x U)
    (hbad :
      ∀ A : FatTree H,
        FatTree.Reduces H A U →
        ExtendsStem H x A →
        ∀ q : Nat, x.height ≤ q →
          ¬ OneBlockExactPersistent H x A O q)
    (i : Nat) :
    ∀ g : AM H x.terminalCut 1,
      g ∈ O →
      ¬ StemAt H (FiniteFatTree.appendRow H x g)
        (exactAvoidStage H hxU hbad (i + 1)).1
        (x.height + i + 1) := by
  exact exactAvoidNext_avoids H hbad i
    (exactAvoidStage H hxU hbad i)

theorem oneBlockLarge_exact_persistent
    (C : RamseySpace.FusionComplete (approximationSystem H))
    {x : FiniteFatTree H} {U : FatTree H}
    {O : Set (AM H x.terminalCut 1)}
    (hxU : ExtendsStem H x U)
    (hlarge : OneBlockLarge H x U O) :
    ∃ A : FatTree H, ∃ q : Nat,
      FatTree.Reduces H A U ∧
      ExtendsStem H x A ∧
      x.height ≤ q ∧
      OneBlockExactPersistent H x A O q := by
  classical
  by_contra hnone
  have hbad :
      ∀ A : FatTree H,
        FatTree.Reduces H A U →
        ExtendsStem H x A →
        ∀ q : Nat, x.height ≤ q →
          ¬ OneBlockExactPersistent H x A O q := by
    intro A hAU hxA q hq hp
    exact hnone ⟨A, q, hAU, hxA, hq, hp⟩
  let Y : Nat → FatTree H :=
    fun i => (exactAvoidStage H hxU hbad i).1
  have hfusion :
      (approximationSystem H).IsFusionFrom x.height Y := by
    intro i
    change
      (exactAvoidStage H hxU hbad (i + 1)).1 ∈
        (approximationSystem H).levelNeighborhood
          (x.height + i)
          (exactAvoidStage H hxU hbad i).1
    exact exactAvoidStage_step H hxU hbad i
  rcases C.exists_limit hfusion with ⟨L, hL⟩
  have hL0 :
      L ∈ (approximationSystem H).levelNeighborhood x.height U := by
    have h0 := hL 0
    change
      L ∈ (approximationSystem H).levelNeighborhood
        x.height (exactAvoidStage H hxU hbad 0).1 at h0
    exact h0
  have hLU : FatTree.Reduces H L U := hL0.1
  have hxL : ExtendsStem H x L := by
    have hdepth :
        InDepthCone H x.height U L :=
      (mem_levelNeighborhood_iff_depthCone H x.height U L).1 hL0
    exact extendsStem_of_depthCone H hxU hdepth le_rfl
  rcases hlarge L hLU hxL with ⟨g, hgO, ⟨m, hgm⟩⟩
  have hheight :
      x.height + 1 ≤ m := by
    have hred : FiniteFatTree.Reduces H
        (FiniteFatTree.appendRow H x g)
        (L.initialSegment H m) :=
      FiniteFatTree.reduces_of_leFin H hgm
    have hh :=
      FiniteFatTree.ReductionWitness.height_le_of_reduces H hred
    change
      (FiniteFatTree.appendRow H x g).height ≤
        (L.initialSegment H m).height at hh
    change x.height + 1 ≤ m at hh
    exact hh
  let i : Nat := m - (x.height + 1)
  have him : x.height + i + 1 = m := by
    dsimp [i]
    omega
  have hLstage :
      L ∈ (approximationSystem H).levelNeighborhood
        (x.height + (i + 1))
        (exactAvoidStage H hxU hbad (i + 1)).1 := by
    simpa [Y, Nat.add_assoc] using hL (i + 1)
  have hprefix :
      L.initialSegment H m =
        (exactAvoidStage H hxU hbad (i + 1)).1.initialSegment H m := by
    have heq := congrArg Subtype.val hLstage.2
    change
      L.initialSegment H (x.height + (i + 1)) =
        (exactAvoidStage H hxU hbad (i + 1)).1.initialSegment H
          (x.height + (i + 1)) at heq
    have hd : x.height + (i + 1) = m := by
      omega
    rw [hd] at heq
    exact heq
  have hgmStage :
      StemAt H (FiniteFatTree.appendRow H x g)
        (exactAvoidStage H hxU hbad (i + 1)).1 m := by
    unfold StemAt at hgm ⊢
    rw [← hprefix]
    exact hgm
  apply (exactAvoidStage_avoids H hxU hbad i g hgO)
  have hidx : x.height + i + 1 = m := him
  rw [hidx]
  exact hgmStage

/-- Closed fat-tree spaces therefore satisfy the exact-persistence
conclusion for every large one-block set, without assuming A4. -/
theorem oneBlockLarge_exact_persistent_closed
    {x : FiniteFatTree H} {U : FatTree H}
    {O : Set (AM H x.terminalCut 1)}
    (hxU : ExtendsStem H x U)
    (hlarge : OneBlockLarge H x U O) :
    ∃ A : FatTree H, ∃ q : Nat,
      FatTree.Reduces H A U ∧
      ExtendsStem H x A ∧
      x.height ≤ q ∧
      OneBlockExactPersistent H x A O q :=
  oneBlockLarge_exact_persistent H
    (fusionComplete H) hxU hlarge


end FatTree
end SMTree
end SuccessorTree

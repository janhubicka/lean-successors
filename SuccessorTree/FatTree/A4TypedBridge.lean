import SuccessorTree.FatTree.A3Typed
import SuccessorTree.FatTree.A4Large

/-!
# One-step approximations versus appended fat-tree rows

This file identifies the abstract one-step front used by Todorcevic A4 with
the manuscript's concrete operation of appending one row to a finite fat-tree
stem.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

private noncomputable def S0 := approximationSystem H

/-- Every abstract one-step approximation is literally obtained by appending
one concrete row to the underlying finite fat-tree stem, and that appended row
occurs in the ambient tree. -/
theorem oneStep_exists_appendedRow
    {n : Nat}
    (a : (S0 H).Approx n)
    (B : FatTree H)
    {b : (S0 H).Approx (n + 1)}
    (hb : b ∈ (S0 H).oneStepApproximations a B) :
    ∃ g : AM H a.1.terminalCut 1,
      OneBlockOccurs H a.1 B g ∧
      b.1 = FiniteFatTree.appendRow H a.1 g := by
  rcases hb with ⟨X, hXaB, hXb⟩
  have hXa : X.initialSegment H n = a.1 := by
    have h := congrArg Subtype.val hXaB.2
    change X.initialSegment H n = a.1 at h
    exact h
  have hXaStem : ExtendsStem H a.1 X :=
    extendsStem_of_initialSegment_eq H hXa
  let g : AM H a.1.terminalCut 1 :=
    ambientNextRow H a.1 X hXaStem
  have happ :
      FiniteFatTree.appendRow H a.1 g =
        X.initialSegment H (n + 1) := by
    have haHeight : a.1.height = n := a.2
    simpa [haHeight] using
      appendRow_ambientNextRow H a.1 X hXaStem
  have hbTree :
      X.initialSegment H (n + 1) = b.1 := by
    exact congrArg Subtype.val hXb
  refine ⟨g, ?_, ?_⟩
  · unfold OneBlockOccurs
    have hstemX :
        StemAt H (FiniteFatTree.appendRow H a.1 g) X (n + 1) := by
      unfold StemAt
      rw [happ]
      exact FiniteFatTree.leFin_refl H (X.initialSegment H (n + 1))
    rcases exists_stemAt_of_reduces H hstemX hXaB.1 with
      ⟨m, hm⟩
    exact ⟨m, hm⟩
  · rw [← hbTree, ← happ]

/-- Conversely, every concrete appended row which occurs in the ambient
fat tree gives an abstract one-step approximation. -/
theorem appendedRow_mem_oneStep
    {n : Nat}
    (a : (S0 H).Approx n)
    (B : FatTree H)
    (g : AM H a.1.terminalCut 1)
    (hg : OneBlockOccurs H a.1 B g) :
    (⟨FiniteFatTree.appendRow H a.1 g,
        by
          rw [FiniteFatTree.appendRow_height, a.2]⟩ :
      (S0 H).Approx (n + 1)) ∈
        (S0 H).oneStepApproximations a B := by
  rcases hg with ⟨m, hstem⟩
  have hcone : InDepthCone H m B B := by
    refine ⟨FatTree.reduces_refl H B, ?_⟩
    exact initialSegment_extendsStem H B m
  obtain ⟨X, hX⟩ :=
    a3_one_nonempty H hstem hcone
  refine ⟨X, ?_, ?_⟩
  · have hred : FatTree.Reduces H X B := hX.1
    have happStem : ExtendsStem H
        (FiniteFatTree.appendRow H a.1 g) X := hX.2
    have hprefix :
        X.initialSegment H (n + 1) =
          FiniteFatTree.appendRow H a.1 g := by
      have hheight :
          (FiniteFatTree.appendRow H a.1 g).height = n + 1 := by
        rw [FiniteFatTree.appendRow_height, a.2]
      have h0 :=
        initialSegment_eq_of_extendsStem H happStem
      simpa [hheight] using h0
    have haPrefix :
        X.initialSegment H n = a.1 := by
      have hseg :
          (X.initialSegment H (n + 1)).initialSegment H n (by omega) =
            X.initialSegment H n :=
        X.initialSegment_initialSegment H (n + 1) n (by omega)
      have happOld :=
        FiniteFatTree.appendRow_initialSegment H a.1 g
      calc
        X.initialSegment H n =
            (X.initialSegment H (n + 1)).initialSegment H n (by omega) :=
          hseg.symm
        _ =
            (FiniteFatTree.appendRow H a.1 g).initialSegment H n
              (by
                rw [FiniteFatTree.appendRow_height, a.2]
                omega) := by rw [hprefix]
        _ = a.1 := by
          have haHeight : a.1.height = n := a.2
          simpa [haHeight] using happOld
    refine ⟨hred, ?_⟩
    apply Subtype.ext
    exact haPrefix
  · apply Subtype.ext
    have hheight :
        (FiniteFatTree.appendRow H a.1 g).height = n + 1 := by
      rw [FiniteFatTree.appendRow_height, a.2]
    have happStem : ExtendsStem H
        (FiniteFatTree.appendRow H a.1 g) X := hX.2
    have hprefix :=
      initialSegment_eq_of_extendsStem H happStem
    simpa [hheight] using hprefix

/-- Membership in the abstract one-step front is therefore equivalent to
being an appended occurring row. -/
theorem mem_oneStep_iff_exists_appendedRow
    {n : Nat}
    (a : (S0 H).Approx n)
    (B : FatTree H)
    (b : (S0 H).Approx (n + 1)) :
    b ∈ (S0 H).oneStepApproximations a B ↔
      ∃ g : AM H a.1.terminalCut 1,
        OneBlockOccurs H a.1 B g ∧
        b.1 = FiniteFatTree.appendRow H a.1 g := by
  constructor
  · exact oneStep_exists_appendedRow H a B
  · rintro ⟨g, hg, hbg⟩
    have hb0 :=
      appendedRow_mem_oneStep H a B g hg
    have htyped :
        b =
          (⟨FiniteFatTree.appendRow H a.1 g,
              by
                rw [FiniteFatTree.appendRow_height, a.2]⟩ :
            (S0 H).Approx (n + 1)) := by
      apply Subtype.ext
      exact hbg
    simpa [htyped] using hb0

end FatTree
end SMTree
end SuccessorTree

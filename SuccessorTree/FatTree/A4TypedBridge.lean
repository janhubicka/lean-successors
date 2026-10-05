import SuccessorTree.FatTree.A3Typed
import SuccessorTree.FatTree.A4Large

/-!
# One-step approximations versus appended fat-tree rows

The typed one-step front is exactly the set of concrete appended rows which
occur geometrically in the ambient tree. Both directions use only A1--A3;
no pigeonhole or Ellentuck conclusion is assumed.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- Typed version of appending one row. -/
noncomputable def appendApprox {n : Nat} (a : (approximationSystem H).Approx n)
    (g : AM H a.1.terminalCut 1) :
    (approximationSystem H).Approx (n + 1) :=
  ⟨FiniteFatTree.appendRow H a.1 g, by
    rw [FiniteFatTree.appendRow_height, a.2]⟩

/-- Exact agreement with an appended stem implies agreement with the old stem.
The proof uses the row and cut data directly, avoiding dependent truncation. -/
theorem extendsStem_of_appendRow
    {x : FiniteFatTree H} {g : AM H x.terminalCut 1} {X : FatTree H}
    (hx : ExtendsStem H (FiniteFatTree.appendRow H x g) X) :
    ExtendsStem H x X := by
  constructor
  · intro i
    exact (hx.1 i.castSucc).trans
      (FiniteFatTree.appendRow_cut_old H x g i)
  · intro i
    exact (hx.2 i.castSucc).trans
      (FiniteFatTree.appendRow_row_old H x g i)

/-- Every member of the typed one-step front is an appended occurring row. -/
theorem oneStep_exists_appendedRow
    {n : Nat} (a : (approximationSystem H).Approx n) (B : FatTree H)
    {b : (approximationSystem H).Approx (n + 1)}
    (hb : b ∈ (approximationSystem H).oneStepApproximations a B) :
    ∃ g : AM H a.1.terminalCut 1,
      OneBlockOccurs H a.1 B g ∧
      b.1 = FiniteFatTree.appendRow H a.1 g := by
  rcases hb with ⟨X, hXaB, hXb⟩
  have hXaStem : ExtendsStem H a.1 X :=
    ((mem_neighborhood_iff_inNeighborhood H a B X).1 hXaB).2
  let g := ambientNextRow H a.1 X hXaStem
  have happ : FiniteFatTree.appendRow H a.1 g =
      X.initialSegment H (n + 1) := by
    have h := appendRow_ambientNextRow H a.1 X hXaStem
    rw [a.2] at h
    exact h
  have hbTree : X.initialSegment H (n + 1) = b.1 :=
    congrArg Subtype.val hXb
  refine ⟨g, ?_, hbTree.symm.trans happ.symm⟩
  have hstemX : StemAt H (FiniteFatTree.appendRow H a.1 g) X (n + 1) := by
    unfold StemAt
    rw [happ]
    exact FiniteFatTree.leFin_refl H (X.initialSegment H (n + 1))
  exact exists_stemAt_of_reduces H hstemX hXaB.1

/-- An occurring appended row belongs to the typed one-step front. -/
theorem appendedRow_mem_oneStep
    {n : Nat} (a : (approximationSystem H).Approx n) (B : FatTree H)
    (g : AM H a.1.terminalCut 1) (hg : OneBlockOccurs H a.1 B g) :
    appendApprox H a g ∈ (approximationSystem H).oneStepApproximations a B := by
  rcases hg with ⟨m, hstem⟩
  have hcone : InDepthCone H m B B :=
    ⟨reduces_refl H B, extendsStem_of_initialSegment_eq H rfl⟩
  obtain ⟨X, hX⟩ := a3_one_nonempty H hstem hcone
  have hOld : ExtendsStem H a.1 X := extendsStem_of_appendRow H hX.2
  refine ⟨X, (mem_neighborhood_iff_inNeighborhood H a B X).2
    ⟨hX.1, hOld⟩, ?_⟩
  apply Subtype.ext
  change X.initialSegment H (n + 1) = FiniteFatTree.appendRow H a.1 g
  have h := initialSegment_eq_of_extendsStem H hX.2
  rw [FiniteFatTree.appendRow_height, a.2] at h
  exact h

/-- Exact identification of the typed front and the concrete geometric front. -/
theorem mem_oneStep_iff_exists_appendedRow
    {n : Nat} (a : (approximationSystem H).Approx n) (B : FatTree H)
    (b : (approximationSystem H).Approx (n + 1)) :
    b ∈ (approximationSystem H).oneStepApproximations a B ↔
      ∃ g : AM H a.1.terminalCut 1,
        OneBlockOccurs H a.1 B g ∧
        b.1 = FiniteFatTree.appendRow H a.1 g := by
  constructor
  · exact oneStep_exists_appendedRow H a B
  · rintro ⟨g, hg, hbg⟩
    have htyped : b = appendApprox H a g := Subtype.ext hbg
    rw [htyped]
    exact appendedRow_mem_oneStep H a B g hg

end FatTree
end SMTree
end SuccessorTree

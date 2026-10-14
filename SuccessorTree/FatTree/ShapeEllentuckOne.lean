import SuccessorTree.FatTree.ShapeRealization
import SuccessorTree.ShapeLocalPigeonhole

/-!
# One-dimensional shape Ramsey theorem from fat-tree Ellentuck

This is the alternative proof route through the topological Ramsey space of
fat trees.  Only the forward realization of an algebraic coordinate as a
geometric fat-tree row is used; no quotient or openness statement for the map
from fat trees to shape maps is assumed.
-/

namespace SuccessorTree
namespace SMTree
namespace FatTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable (H : SMTree S)

/-- Colour an exact fat-tree approximation by the appended row when it extends
a fixed stem, and by a harmless default otherwise. -/
noncomputable def appendedApproxColour
    {κ : Type w} {n : Nat}
    (a : (approximationSystem H).Approx n)
    (hcut : a.1.terminalCut = n)
    (colour : AM H n 1 → κ) (default : κ)
    (b : (approximationSystem H).Approx (n + 1)) : κ := by
  classical
  exact if h :
      ∃ g : AM H a.1.terminalCut 1, appendApprox H a g = b then
    colour (FatTree.castRow H hcut (Classical.choose h))
  else default

theorem appendedApproxColour_append
    {κ : Type w} {n : Nat}
    (a : (approximationSystem H).Approx n)
    (hcut : a.1.terminalCut = n)
    (colour : AM H n 1 → κ) (default : κ)
    (g : AM H a.1.terminalCut 1) :
    appendedApproxColour H a hcut colour default (appendApprox H a g) =
      colour (FatTree.castRow H hcut g) := by
  classical
  let hex :
      ∃ q : AM H a.1.terminalCut 1,
        appendApprox H a q = appendApprox H a g :=
    ⟨g, rfl⟩
  unfold appendedApproxColour
  rw [dif_pos hex]
  have hchosen :
      Classical.choose hex = g := by
    apply appendApprox_injective H a
    exact Classical.choose_spec hex
  rw [hchosen]

/-- The one-moving-level shape Ramsey theorem, derived from the fat-tree
Ellentuck theorem. -/
theorem shapeOneDimensionalRamsey_viaFatEllentuck
    {κ : Type w} [Fintype κ]
    (n : Nat) (colour : AM H n 1 → κ) :
    ∃ W : ShapeSubspace H n,
      (H.shapeSubspaceAction n).Homogeneous colour W := by
  classical

  let I : FatTree H := identityFatTree H
  let a : (approximationSystem H).Approx n := exactApprox H n I
  have haCut : a.1.terminalCut = n := by
    change I.cut n = n
    rfl

  let default : κ := colour (AM.id1 H n)
  let fatColour : (approximationSystem H).Approx (n + 1) → κ :=
    appendedApproxColour H a haCut colour default

  have hne : ((approximationSystem H).neighborhood a I).Nonempty :=
    ⟨I, reduces_refl H I, rfl⟩
  obtain ⟨B, hBaI, hhom⟩ :=
    RamseySpace.finiteApproximationColouring
      (fatTreeEllentuck H) a I hne fatColour

  have hseg : B.initialSegment H n = a.1 :=
    congrArg Subtype.val hBaI.2
  have hterm :
      (B.initialSegment H n).terminalCut = a.1.terminalCut :=
    congrArg FiniteFatTree.terminalCut hseg
  have hBcut : B.cut n = n := by
    exact hterm.trans haCut

  let W : ShapeSubspace H n :=
    ⟨tailMap H B n, by
      intro x hx
      exact tailMap_fixesBelow H B n x (by
        rw [hBcut]
        exact hx)⟩

  have realize (g : AM H n 1) :
      ∃ X : FatTree H,
        X ∈ (approximationSystem H).neighborhood a B ∧
        fatColour ((approximationSystem H).approx (n + 1) X) =
          colour (H.shapeAct n W g) := by
    let rowB : AM H (B.cut n) 1 :=
      FatTree.castRow H hBcut.symm (H.shapeAct n W g)
    have hrowB :
        OneBlockOccurs H (B.initialSegment H n) B rowB := by
      exact shapeAct_tail_oneBlockOccurs H B n n hBcut g

    let rowA : AM H a.1.terminalCut 1 :=
      FatTree.castRow H hterm rowB
    have hrowA : OneBlockOccurs H a.1 B rowA := by
      simpa [rowA] using
        oneBlockOccurs_transport_stem H hseg rowB hrowB

    have hstep :
        appendApprox H a rowA ∈
          (approximationSystem H).oneStepApproximations a B :=
      appendedRow_mem_oneStep H a B rowA hrowA
    rcases hstep with ⟨X, hXaB, hXapp⟩
    refine ⟨X, hXaB, ?_⟩

    calc
      fatColour ((approximationSystem H).approx (n + 1) X) =
          fatColour (appendApprox H a rowA) := by
            rw [hXapp]
      _ = colour (FatTree.castRow H haCut rowA) := by
            exact appendedApproxColour_append
              H a haCut colour default rowA
      _ = colour (H.shapeAct n W g) := by
            apply congrArg colour
            dsimp [rowA, rowB]
            exact castRow_cancel_chain H hterm haCut
              (H.shapeAct n W g)

  refine ⟨W, ?_⟩
  intro g h
  obtain ⟨Xg, hXg, hcg⟩ := realize g
  obtain ⟨Xh, hXh, hch⟩ := realize h
  exact hcg.symm.trans ((hhom Xg hXg Xh hXh).trans hch)


/-- The local one-step pigeonhole principle obtained from fat-tree Ellentuck. -/
theorem shapeLocalPigeonhole_viaFatEllentuck
    {κ : Type w} [Fintype κ]
    (colour : StepColouring H κ) :
    LocalPigeonhole H colour :=
  H.shapeLocalPigeonhole_of_oneDimensional colour
    (fun m c => shapeOneDimensionalRamsey_viaFatEllentuck H m c)

end FatTree
end SMTree
end SuccessorTree

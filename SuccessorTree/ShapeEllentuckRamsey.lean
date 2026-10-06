import SuccessorTree.FatTree.ShapeEllentuckOne
import SuccessorTree.ShapeFiniteProduct

/-!
# Finite-dimensional shape Ramsey theorem from fat-tree Ellentuck

This is an alternative proof of the finite-dimensional theorem.  Its Ramsey
input is the topological Ramsey theorem for fat trees.  The remaining
finite-front fusion and product induction are shared structural machinery.
The direct Hales--Jewett/large-set one-dimensional theorem is not used.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Relative one-moving-level homogeneity from fat-tree Ellentuck. -/
theorem shapeRamsey_one_relative_viaFatEllentuck
    {κ : Type w} [Fintype κ]
    (H : SMTree S) (n : Nat)
    (B : ShapeSubspace H n)
    (colour : RamseyApprox H (n + 1) → κ) :
    ∃ W : ShapeSubspace H n,
      RamseyReduction H W.1 B.1 ∧
      ∀ K L : ShapeSubspace H n,
        colour (ramseyApprox H (n + 1) (MMap.comp H W.1 K.1)) =
          colour (ramseyApprox H (n + 1) (MMap.comp H W.1 L.1)) := by
  classical
  let c : AM H n 1 → κ := fun a => colour (H.shapeAct n B a).1
  obtain ⟨U, hU⟩ :=
    FatTree.shapeOneDimensionalRamsey_viaFatEllentuck H n c
  let W : ShapeSubspace H n := ShapeSubspace.comp H B U
  have hval (K : ShapeSubspace H n) :
      (H.shapeAct n B
        (H.shapeAct n U (K.1.toAM H n 1 K.2))).1 =
        ramseyApprox H (n + 1) (MMap.comp H W.1 K.1) := by
    rw [← H.shapeAct_comp n B U]
    have h := H.shapeActK_toAM_val n 1 W K
    rw [H.shapeActK_one n W] at h
    exact h
  refine ⟨W, ⟨U.1, ?_⟩, ?_⟩
  · intro x
    rfl
  · intro K L
    have h := hU (K.1.toAM H n 1 K.2) (L.1.toAM H n 1 L.2)
    change
      colour (H.shapeAct n B
        (H.shapeAct n U (K.1.toAM H n 1 K.2))).1 =
      colour (H.shapeAct n B
        (H.shapeAct n U (L.1.toAM H n 1 L.2))).1 at h
    rw [hval K, hval L] at h
    exact h

/-- One backward product step whose local pigeonhole input comes from
fat-tree Ellentuck. -/
noncomputable def buildShapeProductStep_viaFatEllentuck
    [Fintype κ]
    (H : SMTree S)
    (default : κ)
    {n m : Nat} (hnm : n < m)
    (B : ShapeSubspace H n)
    (nextColour : RamseyApprox H (m + 1) → κ) :
    ShapeProductStep H n m B nextColour :=
  H.buildShapeProductStep_of_localPigeonhole
    default hnm B nextColour
    (FatTree.shapeLocalPigeonhole_viaFatEllentuck H
      (H.singleLevelStepColour default m nextColour))

/-- Relative finite-dimensional homogeneity, with all pigeonhole input supplied
by fat-tree Ellentuck. -/
theorem shapeRamsey_approximations_viaFatEllentuck
    {κ : Type w} [Fintype κ]
    (H : SMTree S) (n : Nat) :
    ∀ (k : Nat) (B : ShapeSubspace H n)
      (colour : RamseyApprox H (n + k) → κ),
      ∃ W : ShapeSubspace H n,
        RamseyReduction H W.1 B.1 ∧
        ∀ K L : ShapeSubspace H n,
          colour (ramseyApprox H (n + k) (MMap.comp H W.1 K.1)) =
            colour (ramseyApprox H (n + k) (MMap.comp H W.1 L.1)) := by
  intro k
  induction k with
  | zero =>
      intro B colour
      refine ⟨B, H.ramseyReduction_refl B.1, ?_⟩
      intro K L
      have hK := MMap.ramseyApprox_eq_id_of_fixesBelow H
        (MMap.comp H B.1 K.1) n
        (MMap.comp_fixesBelow H B.1 K.1 n B.2 K.2)
      have hL := MMap.ramseyApprox_eq_id_of_fixesBelow H
        (MMap.comp H B.1 L.1) n
        (MMap.comp_fixesBelow H B.1 L.1 n B.2 L.2)
      exact congrArg colour (hK.trans hL.symm)
  | succ k ih =>
      intro B colour
      cases k with
      | zero =>
          exact H.shapeRamsey_one_relative_viaFatEllentuck n B colour
      | succ k =>
          let m : Nat := n + (k + 1)
          have hnm : n < m := by
            dsimp [m]
            omega
          let default : κ := colour (ramseyApprox H (m + 1) (MMap.id H))
          let P : ShapeProductStep H n m B colour :=
            H.buildShapeProductStep_viaFatEllentuck default hnm B colour
          obtain ⟨W, hWP, hW⟩ := ih P.space P.colour
          obtain ⟨R, hRfix, hR⟩ :=
            H.exists_frozen_rightFactor W.2 P.space.2 hWP
          let RR : ShapeSubspace H n := ⟨R, hRfix⟩
          have hcomp (K : ShapeSubspace H n) :
              MMap.comp H W.1 K.1 =
                MMap.comp H P.space.1 (ShapeSubspace.comp H RR K).1 := by
            apply MMap.ext_apply
            intro x
            exact congrArg (fun F : MMap H => F (K.1 x)) hR
          have hchild (K : ShapeSubspace H n) :
              colour (ramseyApprox H (m + 1) (MMap.comp H W.1 K.1)) =
                P.colour (ramseyApprox H m (MMap.comp H W.1 K.1)) := by
            rw [hcomp K]
            exact P.child_colour (ShapeSubspace.comp H RR K)
          refine ⟨W, H.ramseyReduction_trans hWP P.reduction, ?_⟩
          intro K L
          exact (hchild K).trans ((hW K L).trans (hchild L).symm)

/-- Alternative proof of the paper's finite-dimensional shape-preserving
Ramsey theorem, derived from fat-tree Ellentuck. -/
theorem shapePreservingRamsey_viaFatEllentuck
    {κ : Type w} [Fintype κ]
    (H : SMTree S) (n k : Nat)
    (colour : AM H n k → κ) :
    ∃ W : ShapeSubspace H n,
      ∀ a b : AM H n k,
        colour (H.shapeActK n k W a) =
          colour (H.shapeActK n k W b) := by
  classical
  let default : κ := colour
    ((MMap.id H).toAM H n k (MMap.id_fixesBelow H n))
  let extended : RamseyApprox H (n + k) → κ := fun p =>
    if hp : (ramseyApproximationSystem H).IsInitial
        (ramseyApprox H n (MMap.id H)) p then
      colour ⟨p, hp⟩
    else default
  have hext (a : AM H n k) : extended a.1 = colour a := by
    dsimp only [extended]
    rw [dif_pos a.2]
    exact congrArg colour (Subtype.ext rfl)
  obtain ⟨W, _, hW⟩ :=
    H.shapeRamsey_approximations_viaFatEllentuck
      n k (ShapeSubspace.id H n) extended
  refine ⟨W, ?_⟩
  intro a b
  let K : ShapeSubspace H n :=
    ⟨a.representative H, a.representative_fixesBelow H⟩
  let L : ShapeSubspace H n :=
    ⟨b.representative H, b.representative_fixesBelow H⟩
  have h := hW K L
  change
    extended (H.shapeActK n k W a).1 =
      extended (H.shapeActK n k W b).1 at h
  rw [hext, hext] at h
  exact h

end SMTree
end SuccessorTree

import SuccessorTree.ShapeFiniteProduct

/-!
# The finite-dimensional Ramsey theorem for shape-preserving functions

This is the paper's theorem for every frozen prefix n and finite width k.
The one-moving-level case comes from the two large-set fusions. For larger
widths the ordinary finite-front fusion makes the colour depend only on the
shorter prefix; induction then homogenises that prefix.

No Ellentuck amalgamation hypothesis, fat-tree projection, or unproved
pigeonhole hypothesis is used. The intermediate theorem is relative to an
arbitrary prescribed subspace. Width zero is included.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Postcomposition respects equality of finite approximations. -/
theorem ramseyApprox_comp_congr
    (H : SMTree S) {m : Nat} (F : MMap H) {G K : MMap H}
    (h : ramseyApprox H m G = ramseyApprox H m K) :
    ramseyApprox H m (MMap.comp H F G) =
      ramseyApprox H m (MMap.comp H F K) := by
  cases m with
  | zero => rfl
  | succ m =>
      apply Subtype.ext
      funext x
      exact congrArg F (H.ramseyApprox_apply_eq h x.1 (by omega))

/-- Acting on the finite restriction of a total map is literal composition
on that finite source domain, independent of the chosen representative. -/
theorem shapeActK_toAM_val
    (H : SMTree S) (n k : Nat)
    (W K : ShapeSubspace H n) :
    (H.shapeActK n k W (K.1.toAM H n k K.2)).1 =
      ramseyApprox H (n + k) (MMap.comp H W.1 K.1) := by
  exact H.ramseyApprox_comp_congr W.1
    (AM.representative_top H (K.1.toAM H n k K.2))

/-- One-moving-level homogeneity inside a prescribed subspace. -/
theorem shapeRamsey_one_relative
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
  obtain ⟨U, hU⟩ := H.shapeOneDimensionalRamsey n c
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

/-- Relative finite-dimensional homogeneity in absolute approximation
coordinates. The right factors preserve exactly the requested frozen prefix. -/
theorem shapeRamsey_approximations
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
          exact H.shapeRamsey_one_relative n B colour
      | succ k =>
          let m : Nat := n + (k + 1)
          have hnm : n < m := by dsimp [m]; omega
          let default : κ := colour (ramseyApprox H (m + 1) (MMap.id H))
          let P : ShapeProductStep H n m B colour :=
            H.buildShapeProductStep default hnm B colour
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

/-- The paper's finite-dimensional Ramsey theorem: for every finite colouring
of AM^n_k, some F in M^n makes all Fg, g in AM^n_k, the same colour. -/
theorem shapePreservingRamsey
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
    H.shapeRamsey_approximations n k (ShapeSubspace.id H n) extended
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

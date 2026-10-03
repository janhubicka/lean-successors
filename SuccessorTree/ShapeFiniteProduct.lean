import SuccessorTree.ShapeLocalPigeonhole
import Mathlib.Tactic

/-!
# Finite-dimensional product induction for shape maps

The one-dimensional theorem and its arbitrary-prefix version are now
available.  This file carries out the standard finite product induction:
settle the last moving source level by ordinary front fusion, replace the
colour of a block by the common colour of its one-step extensions, and apply
the induction hypothesis to the shorter prefix.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Action of a frozen-prefix shape subspace on an arbitrary finite AM block. -/
noncomputable def shapeActK
    (H : SMTree S) (n k : Nat)
    (W : ShapeSubspace H n)
    (a : AM H n k) : AM H n k :=
  (MMap.comp H W.1 (a.representative H)).toAM H n k
    (MMap.comp_fixesBelow H W.1 (a.representative H) n
      W.2 (a.representative_fixesBelow H))

/-- A toAM representative agrees with its defining total map throughout the
represented source segment. -/
theorem MMap.toAM_representative_agrees
    (H : SMTree S) (F : MMap H) (n k : Nat)
    (hfix : F.FixesBelow H n)
    (x : T) (hx : LevelTree.lev x < n + k) :
    (F.toAM H n k hfix).representative H x = F x := by
  cases hnk : n + k with
  | zero =>
      omega
  | succ m =>
      have htop := (F.toAM H n k hfix).representative_top H
      have hval := congrArg Subtype.val htop
      change
        ((F.toAM H n k hfix).representative H).restrictLe H m =
          F.restrictLe H m at hval
      have hxm : LevelTree.lev x ≤ m := by omega
      exact congrFun hval ⟨x, hxm⟩

/-- Chosen representatives of a shape action agree with literal composition
on the whole finite block. -/
theorem shapeActK_representative_agrees
    (H : SMTree S) (n k : Nat)
    (W : ShapeSubspace H n)
    (a : AM H n k)
    (x : T) (hx : LevelTree.lev x < n + k) :
    (H.shapeActK n k W a).representative H x =
      W.1 (a.representative H x) := by
  exact MMap.toAM_representative_agrees H
    (MMap.comp H W.1 (a.representative H)) n k
    (MMap.comp_fixesBelow H W.1 (a.representative H) n
      W.2 (a.representative_fixesBelow H))
    x hx

/-- Truncate a finite AM block by one moving source level. -/
noncomputable def AM.dropLast
    (H : SMTree S) {n k : Nat}
    (a : AM H n (k + 1)) : AM H n k :=
  (a.representative H).toAM H n k
    (a.representative_fixesBelow H)

/-- The truncated representative agrees with the original block on its
shorter source segment. -/
theorem AM.dropLast_representative_agrees
    (H : SMTree S) {n k : Nat}
    (a : AM H n (k + 1))
    (x : T) (hx : LevelTree.lev x < n + k) :
    (a.dropLast H).representative H x =
      a.representative H x := by
  exact MMap.toAM_representative_agrees H
    (a.representative H) n k
    (a.representative_fixesBelow H) x hx

/-- Width zero has a unique finite approximation. -/
theorem AM.zero_eq_id
    (H : SMTree S) (n : Nat)
    (a : AM H n 0) :
    a = (MMap.id H).toAM H n 0 (MMap.id_fixesBelow H n) := by
  apply Subtype.ext
  exact (ramseyApproximationSystem H).isInitial_eq_sameLevel a.2

/-- The generic k-action specializes to the previously used one-dimensional
shape action. -/
theorem shapeActK_one
    (H : SMTree S) (n : Nat)
    (W : ShapeSubspace H n)
    (a : AM H n 1) :
    H.shapeActK n 1 W a = H.shapeAct n W a := by
  apply Subtype.ext
  rfl



/-- Before the requested starting depth N, front-fusion stages are literally
the initial map. -/
theorem frontFusionStage_eq_base_of_lt
    [Fintype κ]
    (H : SMTree S)
    (colour : StepColouring H κ)
    (hpig : LocalPigeonhole H colour)
    (N : Nat) (B : MMap H) :
    ∀ {i : Nat}, i < N →
      frontFusionStage H colour hpig N B i = B := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [frontFusionStage]
      have hnot : ¬ N ≤ i + 1 := by omega
      simp only [hnot, dif_neg]
      exact ih (by omega)

/-- Starting front fusion at depth N preserves every source node below N. -/
theorem frontFusion_fixesBelow
    [Fintype κ]
    (H : SMTree S)
    (colour : StepColouring H κ)
    (hpig : LocalPigeonhole H colour)
    (N : Nat) (B : MMap H)
    (hB : B.FixesBelow H N) :
    (H.frontFusion colour hpig N B).FixesBelow H N := by
  intro x hx
  change
    frontFusionStage H colour hpig N B (LevelTree.lev x) x = x
  rw [H.frontFusionStage_eq_base_of_lt colour hpig N B hx]
  exact hB x hx

/-- The final front fusion is a genuine refinement of its initial map. -/
theorem frontFusion_reduction_base
    [Fintype κ]
    (H : SMTree S)
    (colour : StepColouring H κ)
    (hpig : LocalPigeonhole H colour)
    (N : Nat) (B : MMap H) :
    RamseyReduction H (H.frontFusion colour hpig N B) B := by
  let F : Nat → MMap H := frontFusionStage H colour hpig N B
  let hstep : ∀ i : Nat, FusionStep H i (F i) (F (i + 1)) :=
    H.frontFusionStage_step colour hpig N B
  have h :=
    H.fusionOfSteps_reduction_stage F hstep 0
  simpa [frontFusion, F, hstep] using h

/-- A right factor between two maps which both fix below n must itself fix
below n. -/
theorem exists_frozen_rightFactor
    (H : SMTree S) {n : Nat}
    {A B : MMap H}
    (hA : A.FixesBelow H n)
    (hB : B.FixesBelow H n)
    (hAB : RamseyReduction H A B) :
    ∃ R : MMap H,
      R.FixesBelow H n ∧
      A = MMap.comp H B R := by
  rcases hAB with ⟨R, hR⟩
  have hRfix : R.FixesBelow H n := by
    intro x hx
    apply B.map.injective
    calc
      B (R x) = A x := (hR x).symm
      _ = x := hA x hx
      _ = B x := (hB x hx).symm
  refine ⟨R, hRfix, ?_⟩
  apply MMap.ext_apply
  intro x
  exact hR x

/-- A step colouring concentrated on one absolute approximation level. -/
def singleLevelStepColour
    (H : SMTree S) {κ : Type w}
    (default : κ)
    (m : Nat)
    (nextColour : RamseyApprox H (m + 1) → κ) :
    StepColouring H κ :=
  fun j b =>
    if h : j = m then
      by
        subst j
        exact nextColour b
    else default

@[simp] theorem singleLevelStepColour_at
    (H : SMTree S) {κ : Type w}
    (default : κ)
    (m : Nat)
    (nextColour : RamseyApprox H (m + 1) → κ)
    (b : RamseyApprox H (m + 1)) :
    H.singleLevelStepColour default m nextColour m b =
      nextColour b := by
  simp [singleLevelStepColour]



/-- Common colour chosen at a prefix after its one-step extensions have been
made homogeneous. Irrelevant prefixes receive the supplied default colour. -/
noncomputable def previousColour
    (H : SMTree S) {κ : Type w}
    (default : κ)
    (A : MMap H)
    (m : Nat)
    (nextColour : RamseyApprox H (m + 1) → κ)
    (p : RamseyApprox H m) : κ :=
  if h : (ramseyApproximationSystem H).neighborhood p A |>.Nonempty then
    nextColour
      (ramseyApprox H (m + 1) (Classical.choose h))
  else default

/-- At a one-step homogeneous relevant prefix, previousColour is the colour
of every actual one-step extension. -/
theorem previousColour_eq_child
    [Fintype κ]
    (H : SMTree S)
    (default : κ)
    (A : MMap H)
    (m : Nat)
    (nextColour : RamseyApprox H (m + 1) → κ)
    (p : RamseyApprox H m)
    (hhom :
      OneStepHomogeneous H
        (H.singleLevelStepColour default m nextColour)
        ⟨m, p⟩ A)
    {X : MMap H}
    (hX : X ∈ (ramseyApproximationSystem H).neighborhood p A) :
    H.previousColour default A m nextColour p =
      nextColour (ramseyApprox H (m + 1) X) := by
  classical
  have hne :
      ((ramseyApproximationSystem H).neighborhood p A).Nonempty :=
    ⟨X, hX⟩
  let Y : MMap H := Classical.choose hne
  have hY :
      Y ∈ (ramseyApproximationSystem H).neighborhood p A :=
    Classical.choose_spec hne
  rcases hhom with ⟨c, hc⟩
  have hcx :
      nextColour (ramseyApprox H (m + 1) X) = c := by
    have hxstep :
        ramseyApprox H (m + 1) X ∈
          (ramseyApproximationSystem H).oneStepApproximations p A :=
      ⟨X, hX, rfl⟩
    simpa [singleLevelStepColour] using
      hc (ramseyApprox H (m + 1) X) hxstep
  have hcy :
      nextColour (ramseyApprox H (m + 1) Y) = c := by
    have hystep :
        ramseyApprox H (m + 1) Y ∈
          (ramseyApproximationSystem H).oneStepApproximations p A :=
      ⟨Y, hY, rfl⟩
    simpa [singleLevelStepColour] using
      hc (ramseyApprox H (m + 1) Y) hystep
  rw [previousColour]
  simp only [hne, dite_true]
  exact hcy.trans hcx.symm

/-- One backward product step, from colour level m+1 to level m. -/
structure ShapeProductStep
    (H : SMTree S) {κ : Type w}
    (n m : Nat)
    (B : ShapeSubspace H n)
    (nextColour : RamseyApprox H (m + 1) → κ) where
  space : ShapeSubspace H n
  reduction : RamseyReduction H space.1 B.1
  colour : RamseyApprox H m → κ
  child_colour :
    ∀ K : ShapeSubspace H n,
      nextColour
          (ramseyApprox H (m + 1)
            (MMap.comp H space.1 K.1)) =
        colour
          (ramseyApprox H m
            (MMap.comp H space.1 K.1))

/-- Settle one source level by the ordinary finite-front Milliken fusion. -/
noncomputable def buildShapeProductStep
    [Fintype κ]
    (H : SMTree S)
    (default : κ)
    {n m : Nat} (hnm : n < m)
    (B : ShapeSubspace H n)
    (nextColour : RamseyApprox H (m + 1) → κ) :
    ShapeProductStep H n m B nextColour := by
  let sc : StepColouring H κ :=
    H.singleLevelStepColour default m nextColour
  let hpig : LocalPigeonhole H sc :=
    H.shapeLocalPigeonhole sc
  let Amap : MMap H :=
    H.frontFusion sc hpig n B.1
  have hAfix : Amap.FixesBelow H n :=
    H.frontFusion_fixesBelow sc hpig n B.1 B.2
  let A : ShapeSubspace H n := ⟨Amap, hAfix⟩
  have hred : RamseyReduction H A.1 B.1 :=
    H.frontFusion_reduction_base sc hpig n B.1
  let prev : RamseyApprox H m → κ :=
    H.previousColour default A.1 m nextColour
  refine {
    space := A
    reduction := hred
    colour := prev
    child_colour := ?_
  }
  intro K
  let F : MMap H := MMap.comp H A.1 K.1
  let p : RamseyApprox H m := ramseyApprox H m F
  have hFA : RamseyReduction H F A.1 := by
    refine ⟨K.1, ?_⟩
    intro x
    rfl
  have hFpA :
      F ∈ (ramseyApproximationSystem H).neighborhood p A.1 :=
    ⟨hFA, rfl⟩
  obtain ⟨d, hd⟩ :=
    (ramseyFinitization H).exists_hasDepth_of_mem_neighborhood hFpA
  have hmd : m ≤ d :=
    ramseyLeFin_level_le H hd.1
  have hdpos : 0 < d := lt_of_lt_of_le (Nat.zero_lt_of_lt hnm) hmd
  have hnd : n ≤ d := (Nat.le_of_lt hnm).trans hmd
  have hhom :
      OneStepHomogeneous H sc
        (⟨m, p⟩ :
          (ramseyApproximationSystem H).FiniteApprox)
        A.1 := by
    exact H.frontFusion_homogeneous sc hpig n B.1
      ⟨m, p⟩ hd hdpos hnd
  have hprev :=
    H.previousColour_eq_child default A.1 m nextColour p hhom hFpA
  exact hprev.symm


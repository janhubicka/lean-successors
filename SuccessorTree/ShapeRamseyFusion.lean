import SuccessorTree.ShapeLargeShapeLine
import Mathlib.Tactic

/-!
# The second Milliken fusion: from large good tails to a full subspace

ShapeMillikenFusion is the analogue of forcing Lemma 2: from a large set it
produces a refiner, a head, and a large set of good tails.  This file iterates
that construction, exactly as Proposition 1 in the combinatorial-forcing
proof of Hales--Jewett.

At a large stage X with cut c we choose W,g so that g is in the pullback of
X through W and the good tails after g form the next large stage.  The finite
tail of length r is nested as

  W_0 o W_1 o ... o g_1^+ o g_0^+

with the recursive form W o T_next o g^+.  M1 fuses these finite tails.
-/

namespace SuccessorTree
namespace SMTree

open SuccessorTree.HalesJewett

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

structure ShapeLargeStage (H : SMTree S) where
  cut : Nat
  set : Set (AM H cut 1)
  large : (H.shapeSubspaceAction cut).Large set

structure ShapeLargeChoice
    (H : SMTree S) (X : ShapeLargeStage H) where
  refiner : ShapeSubspace H X.cut
  head : AM H X.cut 1
  head_mem : head ∈ H.shapePullback refiner X.set
  good_large :
    (H.shapeSubspaceAction (head.nextCut H)).Large
      (H.shapeGoodTails head (H.shapePullback refiner X.set))

noncomputable def chooseLargeStage
    (H : SMTree S) (X : ShapeLargeStage H) :
    ShapeLargeChoice H X := by
  let h :=
    H.exists_large_goodTails (H.largeSetHasShapeLine X.cut)
      X.set X.large
  let W : ShapeSubspace H X.cut := Classical.choose h
  let hW := Classical.choose_spec h
  let g : AM H X.cut 1 := Classical.choose hW
  have hg := Classical.choose_spec hW
  exact ⟨W, g, hg.1, hg.2⟩

noncomputable def nextLargeStage
    (H : SMTree S) (X : ShapeLargeStage H) :
    ShapeLargeStage H where
  cut := (H.chooseLargeStage X).head.nextCut H
  set :=
    H.shapeGoodTails (H.chooseLargeStage X).head
      (H.shapePullback (H.chooseLargeStage X).refiner X.set)
  large := (H.chooseLargeStage X).good_large

/-- The finite nested tail determined by the first r large stages. -/
noncomputable def largeFiniteTail
    (H : SMTree S) (X : ShapeLargeStage H) : Nat → MMap H
  | 0 => MMap.id H
  | r + 1 =>
      MMap.comp H (H.chooseLargeStage X).refiner.1
        (MMap.comp H
          (H.largeFiniteTail (H.nextLargeStage X) r)
          ((H.chooseLargeStage X).head.canonical H))

theorem largeFiniteTail_fixesBelow
    (H : SMTree S) :
    ∀ (X : ShapeLargeStage H) (r : Nat),
      (H.largeFiniteTail X r).FixesBelow H X.cut := by
  intro X r
  induction r generalizing X with
  | zero =>
      exact MMap.id_fixesBelow H X.cut
  | succ r ih =>
      let C := H.chooseLargeStage X
      let Y := H.nextLargeStage X
      have hnext : X.cut < Y.cut := by
        change X.cut < C.head.nextCut H
        exact C.head.lt_nextCut H
      have hfutureY :
          (H.largeFiniteTail Y r).FixesBelow H Y.cut :=
        ih Y
      have hfutureX :
          (H.largeFiniteTail Y r).FixesBelow H X.cut := by
        intro x hx
        exact hfutureY x (lt_trans hx hnext)
      have hinner :
          (MMap.comp H (H.largeFiniteTail Y r)
            (C.head.canonical H)).FixesBelow H X.cut :=
        MMap.comp_fixesBelow H
          (H.largeFiniteTail Y r) (C.head.canonical H) X.cut
          hfutureX (C.head.canonical_fixesBelow H)
      exact MMap.comp_fixesBelow H
        C.refiner.1
        (MMap.comp H (H.largeFiniteTail Y r) (C.head.canonical H))
        X.cut C.refiner.2 hinner

noncomputable def largeFiniteSubspace
    (H : SMTree S) (X : ShapeLargeStage H) (r : Nat) :
    ShapeSubspace H X.cut :=
  ⟨H.largeFiniteTail X r, H.largeFiniteTail_fixesBelow X r⟩


/-- A canonical head sends a source node lying before c+r+1 to a target node
lying before the next cut plus r. -/
theorem largeHeadCanonical_bound
    (H : SMTree S)
    (X : ShapeLargeStage H)
    (r : Nat)
    (x : T)
    (hx : LevelTree.lev x < X.cut + r + 1) :
    LevelTree.lev ((H.chooseLargeStage X).head.canonical H x) <
      (H.nextLargeStage X).cut + r := by
  let C := H.chooseLargeStage X
  change LevelTree.lev (C.head.canonical H x) < C.head.nextCut H + r
  by_cases hlow : LevelTree.lev x < X.cut
  · have hcan :
        C.head.canonical H x = x := by
      rw [AM.canonical,
        H.canonicalExtension_agrees
          (C.head.representative H) X.cut x (Nat.le_of_lt hlow)]
      exact C.head.representative_fixesBelow H x hlow
    rw [hcan]
    exact lt_of_lt_of_le hlow
      (le_trans (Nat.le_of_lt (C.head.lt_nextCut H))
        (Nat.le_add_right (C.head.nextCut H) r))
  · have hge : X.cut ≤ LevelTree.lev x := Nat.le_of_not_gt hlow
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hge
    have hjr : j ≤ r := by omega
    calc
      LevelTree.lev (C.head.canonical H x) =
          H.levelMap (C.head.canonical H).map (LevelTree.lev x) :=
        (H.levelMap_eq (C.head.canonical H).map (a := x)).symm
      _ = H.levelMap (C.head.canonical H).map (X.cut + j) := by rw [hj]
      _ = H.levelMap (C.head.representative H).map X.cut + j := by
        rw [AM.canonical,
          H.canonicalExtension_level_tail
            (C.head.representative H) X.cut j]
      _ = C.head.topLevel H + j := rfl
      _ < C.head.topLevel H + 1 + r := by omega
      _ = C.head.nextCut H + r := rfl

/-- Adding one more large stage changes nothing below c+r. -/
theorem largeFiniteTail_succ_agrees
    (H : SMTree S) :
    ∀ (X : ShapeLargeStage H) (r : Nat) (x : T),
      LevelTree.lev x < X.cut + r →
      H.largeFiniteTail X (r + 1) x =
        H.largeFiniteTail X r x := by
  intro X r
  induction r generalizing X with
  | zero =>
      intro x hx
      let C := H.chooseLargeStage X
      change
        C.refiner.1
          ((H.largeFiniteTail (H.nextLargeStage X) 0)
            (C.head.canonical H x)) = x
      rw [largeFiniteTail]
      rw [MMap.id_apply]
      have hcan : C.head.canonical H x = x := by
        rw [AM.canonical,
          H.canonicalExtension_agrees
            (C.head.representative H) X.cut x (Nat.le_of_lt hx)]
        exact C.head.representative_fixesBelow H x hx
      rw [hcan]
      exact C.refiner.2 x hx
  | succ r ih =>
      intro x hx
      let C := H.chooseLargeStage X
      let Y := H.nextLargeStage X
      change
        C.refiner.1
          ((H.largeFiniteTail Y (r + 1))
            (C.head.canonical H x)) =
        C.refiner.1
          ((H.largeFiniteTail Y r)
            (C.head.canonical H x))
      apply congrArg C.refiner.1
      apply ih Y
      exact H.largeHeadCanonical_bound X r x (by omega)

/-- Once a finite tail has length d, every longer finite tail has the same
value below cut+d. -/
theorem largeFiniteTail_stable_of_le
    (H : SMTree S)
    (X : ShapeLargeStage H)
    {d e : Nat} (hde : d ≤ e)
    (x : T) (hx : LevelTree.lev x < X.cut + d) :
    H.largeFiniteTail X e x = H.largeFiniteTail X d x := by
  induction e with
  | zero =>
      have hd : d = 0 := by omega
      subst d
      rfl
  | succ e ih =>
      by_cases hEq : d = e + 1
      · subst d
        rfl
      · have hde' : d ≤ e := by omega
        calc
          H.largeFiniteTail X (e + 1) x =
              H.largeFiniteTail X e x := by
            apply H.largeFiniteTail_succ_agrees X e x
            exact lt_of_lt_of_le hx (Nat.add_le_add_left hde' X.cut)
          _ = H.largeFiniteTail X d x := ih hde'

noncomputable def largeFusionStage
    (H : SMTree S) (X : ShapeLargeStage H)
    (i : Nat) : MMap H :=
  H.largeFiniteTail X (i + 1)

theorem largeFusionStage_stable
    (H : SMTree S) (X : ShapeLargeStage H) :
    ShapeMap.FusionStable
      (fun i => (H.largeFusionStage X i).map) := by
  intro i x hx
  change
    H.largeFiniteTail X (i + 1) x =
      H.largeFiniteTail X (i + 2) x
  symm
  apply H.largeFiniteTail_succ_agrees X (i + 1) x
  omega

noncomputable def largeFusionLimit
    (H : SMTree S) (X : ShapeLargeStage H) :
    ShapeSubspace H X.cut := by
  let F : Nat → MMap H := fun i => H.largeFusionStage X i
  let hstable :
      ShapeMap.FusionStable (fun i => (F i).map) :=
    H.largeFusionStage_stable X
  let L : MMap H := {
    map := ShapeMap.fusionLimit (fun i => (F i).map) hstable
    mem := H.fusion_mem
      (fun i => (F i).map)
      (fun i => (F i).mem)
      hstable
  }
  refine ⟨L, ?_⟩
  intro x hx
  change H.largeFiniteTail X (LevelTree.lev x + 1) x = x
  exact H.largeFiniteTail_fixesBelow X (LevelTree.lev x + 1) x hx

/-- The diagonal limit agrees with the finite tail long enough to cover a
prescribed source level. -/
theorem largeFusionLimit_agrees_finite
    (H : SMTree S)
    (X : ShapeLargeStage H)
    (d : Nat)
    (x : T)
    (hx : LevelTree.lev x < X.cut + d) :
    (H.largeFusionLimit X).1 x =
      H.largeFiniteTail X d x := by
  let F : Nat → MMap H := fun i => H.largeFusionStage X i
  let hstable :
      ShapeMap.FusionStable (fun i => (F i).map) :=
    H.largeFusionStage_stable X
  change F (LevelTree.lev x) x = H.largeFiniteTail X d x
  change
    H.largeFiniteTail X (LevelTree.lev x + 1) x =
      H.largeFiniteTail X d x
  by_cases hle : LevelTree.lev x + 1 ≤ d
  · symm
    exact H.largeFiniteTail_stable_of_le X hle x (by
      omega)
  · have hdl : d ≤ LevelTree.lev x + 1 := by omega
    exact H.largeFiniteTail_stable_of_le X hdl x hx


/-- Evaluate a one-moving coordinate in a finite nested Milliken tail. -/
noncomputable def largeFiniteEval
    (H : SMTree S)
    (X : ShapeLargeStage H)
    (d : Nat)
    (r : AM H X.cut 1) :
    AM H X.cut 1 :=
  H.shapeAct X.cut (H.largeFiniteSubspace X d) r

/-- At length one, the identity coordinate evaluates to the chosen refiner
applied to the chosen head. -/
theorem largeFiniteEval_id_one
    (H : SMTree S)
    (X : ShapeLargeStage H) :
    H.largeFiniteEval X 1 (AM.id1 H X.cut) =
      H.shapeAct X.cut (H.chooseLargeStage X).refiner
        (H.chooseLargeStage X).head := by
  let C := H.chooseLargeStage X
  apply Subtype.ext
  rw [largeFiniteEval, H.shapeAct_val, H.shapeAct_val]
  apply Subtype.ext
  funext x
  have hid :=
    MMap.toAM_one_representative_agrees
      H (MMap.id H) X.cut (MMap.id_fixesBelow H X.cut)
      x.1 x.2
  have hheadTop := C.head.representative_top H
  have hheadVal := congrArg Subtype.val hheadTop
  change C.head.representative H |>.restrictLe H X.cut =
    C.head.1.1 at hheadVal
  have hxHead := congrFun hheadVal x
  change
    H.largeFiniteTail X 1
      ((AM.id1 H X.cut).representative H x.1) =
      C.refiner.1 (C.head.representative H x.1)
  rw [hid]
  change
    C.refiner.1
      ((H.largeFiniteTail (H.nextLargeStage X) 0)
        (C.head.canonical H x.1)) =
      C.refiner.1 (C.head.representative H x.1)
  rw [largeFiniteTail, MMap.id_apply]
  apply congrArg C.refiner.1
  rw [AM.canonical,
    H.canonicalExtension_agrees
      (C.head.representative H) X.cut x.1 x.2]

/-- Membership form of the preceding base case. -/
theorem largeFiniteEval_id_mem
    (H : SMTree S)
    (X : ShapeLargeStage H) :
    H.largeFiniteEval X 1 (AM.id1 H X.cut) ∈ X.set := by
  rw [H.largeFiniteEval_id_one X]
  exact (H.chooseLargeStage X).head_mem

end SMTree
end SuccessorTree

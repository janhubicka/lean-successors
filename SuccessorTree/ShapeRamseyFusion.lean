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


/-- The diagonal limit has the expected recursive decomposition into the
current refiner, the next diagonal limit, and the current canonical head. -/
theorem largeFusionLimit_decompose
    (H : SMTree S) (X : ShapeLargeStage H) :
    (H.largeFusionLimit X).1 =
      MMap.comp H (H.chooseLargeStage X).refiner.1
        (MMap.comp H
          (H.largeFusionLimit (H.nextLargeStage X)).1
          ((H.chooseLargeStage X).head.canonical H)) := by
  apply MMap.ext_apply
  intro x
  let C := H.chooseLargeStage X
  let Y := H.nextLargeStage X
  let r : Nat := LevelTree.lev x + 1
  have hxX : LevelTree.lev x < X.cut + (r + 1) := by
    dsimp [r]
    omega
  have hxY :
      LevelTree.lev (C.head.canonical H x) < Y.cut + r := by
    exact H.largeHeadCanonical_bound X r x (by
      dsimp [r]
      omega)
  have hX :=
    H.largeFusionLimit_agrees_finite X (r + 1) x hxX
  have hY :=
    H.largeFusionLimit_agrees_finite Y r
      (C.head.canonical H x) hxY
  change
    (H.largeFusionLimit X).1 x =
      C.refiner.1
        ((H.largeFusionLimit Y).1 (C.head.canonical H x))
  rw [hX, hY]
  change
    H.largeFiniteTail X (r + 1) x =
      C.refiner.1
        (H.largeFiniteTail Y r (C.head.canonical H x))
  rfl

/-- Evaluation of a one-moving coordinate in the diagonal large-stage limit. -/
noncomputable def largeFusionEval
    (H : SMTree S) (X : ShapeLargeStage H)
    (r : AM H X.cut 1) : AM H X.cut 1 :=
  H.shapeAct X.cut (H.largeFusionLimit X) r

/-- Zero excess evaluates to the current chosen head after the current
refiner. -/
theorem largeFusionEval_id
    (H : SMTree S) (X : ShapeLargeStage H) :
    H.largeFusionEval X (AM.id1 H X.cut) =
      H.shapeAct X.cut (H.chooseLargeStage X).refiner
        (H.chooseLargeStage X).head := by
  let C := H.chooseLargeStage X
  let Y := H.nextLargeStage X
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hid :
      (AM.id1 H X.cut).representative H x.1 = x.1 := by
    exact MMap.toAM_one_representative_agrees
      H (MMap.id H) X.cut (MMap.id_fixesBelow H X.cut)
      x.1 x.2
  have hdec := congrArg
    (fun F : MMap H => F x.1)
    (H.largeFusionLimit_decompose X)
  have hcanLev :
      LevelTree.lev (C.head.canonical H x.1) < Y.cut := by
    change LevelTree.lev (C.head.canonical H x.1) < C.head.nextCut H
    calc
      LevelTree.lev (C.head.canonical H x.1) =
          H.levelMap (C.head.canonical H).map (LevelTree.lev x.1) :=
        (H.levelMap_eq (C.head.canonical H).map (a := x.1)).symm
      _ ≤ H.levelMap (C.head.canonical H).map X.cut :=
        (H.levelMap_strictMono (C.head.canonical H).map).monotone x.2
      _ = C.head.topLevel H := C.head.canonical_level_cut H
      _ < C.head.nextCut H := Nat.lt_succ_self _
  have hfuture :
      (H.largeFusionLimit Y).1 (C.head.canonical H x.1) =
        C.head.canonical H x.1 :=
    (H.largeFusionLimit Y).2 _ hcanLev
  have hheadTop := C.head.representative_top H
  have hheadVal := congrArg Subtype.val hheadTop
  change
    (C.head.representative H).restrictLe H X.cut =
      C.head.1.1 at hheadVal
  have hxHead := congrFun hheadVal x
  change
    (H.largeFusionLimit X).1
        ((AM.id1 H X.cut).representative H x.1) =
      C.refiner.1 (C.head.representative H x.1)
  rw [hid]
  calc
    (H.largeFusionLimit X).1 x.1 =
        C.refiner.1
          ((H.largeFusionLimit Y).1 (C.head.canonical H x.1)) := hdec
    _ = C.refiner.1 (C.head.canonical H x.1) := by rw [hfuture]
    _ = C.refiner.1 (C.head.representative H x.1) := by
      rw [AM.canonical,
        H.canonicalExtension_agrees
          (C.head.representative H) X.cut x.1 x.2]

/-- One positive-excess coordinate is an algebraic line over a coordinate in
the next large stage, with excess decreased by one. -/
theorem largeFusionEval_step
    (H : SMTree S) (X : ShapeLargeStage H)
    (r : AM H X.cut 1)
    (hmove : X.cut < r.topLevel H) :
    ∃ q : AM H (H.nextLargeStage X).cut 1,
      AM.excess H q = AM.excess H r - 1 ∧
      H.largeFusionEval X r =
        H.shapeAct X.cut (H.chooseLargeStage X).refiner
          (H.shapeLineApply (H.chooseLargeStage X).head
            (H.amCastCut
              (show (H.nextLargeStage X).cut =
                  (H.chooseLargeStage X).head.nextCut H by rfl)
              (H.largeFusionEval (H.nextLargeStage X) q))
            (.letter (H.firstMoveSplit r hmove).first)) := by
  let C := H.chooseLargeStage X
  let Y := H.nextLargeStage X
  let R := H.firstMoveSplit r hmove
  obtain ⟨t, htfixHead, htlevHead, htcomm⟩ :=
    H.exists_transport_after_head C.head R.tail R.tail_fixes
  have hcut : Y.cut = C.head.nextCut H := rfl
  have htfix : t.FixesBelow H Y.cut := by
    rw [hcut]
    exact htfixHead
  have htlev :
      H.levelMap t.map Y.cut =
        Y.cut +
          (H.levelMap R.tail.map (X.cut + 1) - (X.cut + 1)) := by
    rw [hcut]
    exact htlevHead
  let q : AM H Y.cut 1 :=
    t.toAM H Y.cut 1 htfix
  have hqex : AM.excess H q = AM.excess H r - 1 := by
    unfold AM.excess
    rw [show q.topLevel H = H.levelMap t.map Y.cut by
      exact MMap.toAM_one_topLevel H t Y.cut htfix]
    rw [htlev]
    have htail := H.firstMoveSplit_tail_excess r hmove
    change
      (Y.cut +
          (H.levelMap R.tail.map (X.cut + 1) - (X.cut + 1)) -
        Y.cut) =
        r.topLevel H - X.cut - 1
    rw [Nat.add_sub_cancel_left]
    simpa [AM.excess] using htail
  refine ⟨q, hqex, ?_⟩
  let qe : AM H Y.cut 1 := H.largeFusionEval Y q
  let qline : AM H (C.head.nextCut H) 1 :=
    H.amCastCut hcut qe
  have hqlineRep :
      qline.representative H = qe.representative H := by
    exact amCastCut_representative H hcut qe
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hrTop := r.representative_top H
  have hrVal := congrArg Subtype.val hrTop
  change
    (r.representative H).restrictLe H X.cut = r.1.1 at hrVal
  have hrx := congrFun hrVal x
  have hsplitVal := congrArg Subtype.val R.agrees
  change
    (MMap.comp H R.tail R.first.toMMap).restrictLe H X.cut =
      r.1.1 at hsplitVal
  have hsx := congrFun hsplitVal x
  have hrSplit :
      r.representative H x.1 =
        R.tail (R.first.toMMap x.1) := by
    calc
      r.representative H x.1 = r.1.1 x := hrx
      _ = R.tail (R.first.toMMap x.1) := hsx.symm
  have hdec := congrArg
    (fun F : MMap H => F (r.representative H x.1))
    (H.largeFusionLimit_decompose X)
  have hfirstLev :
      LevelTree.lev (R.first.toMMap x.1) ≤ X.cut + 1 := by
    rw [R.first.level_apply H]
    split <;> omega
  have hcomm :=
    htcomm (R.first.toMMap x.1) hfirstLev
  let z : T := C.head.canonical H (R.first.toMMap x.1)
  have hz : LevelTree.lev z ≤ Y.cut := by
    change LevelTree.lev z ≤ C.head.nextCut H
    calc
      LevelTree.lev z =
          H.levelMap (C.head.canonical H).map
            (LevelTree.lev (R.first.toMMap x.1)) :=
        (H.levelMap_eq (C.head.canonical H).map
          (a := R.first.toMMap x.1)).symm
      _ ≤ H.levelMap (C.head.canonical H).map (X.cut + 1) :=
        (H.levelMap_strictMono (C.head.canonical H).map).monotone
          hfirstLev
      _ = C.head.nextCut H := C.head.canonical_level_next H
  have hqe :
      qe.representative H z =
        (H.largeFusionLimit Y).1 (q.representative H z) := by
    exact H.shapeAct_representative_agrees
      Y.cut (H.largeFusionLimit Y) q z hz
  have hqrep : q.representative H z = t z := by
    exact MMap.toAM_one_representative_agrees
      H t Y.cut htfix z hz
  change
    (H.largeFusionLimit X).1 (r.representative H x.1) =
      C.refiner.1
        (qline.representative H
          (C.head.canonical H (R.first.toMMap x.1)))
  calc
    (H.largeFusionLimit X).1 (r.representative H x.1) =
        C.refiner.1
          ((H.largeFusionLimit Y).1
            (C.head.canonical H (r.representative H x.1))) := hdec
    _ =
        C.refiner.1
          ((H.largeFusionLimit Y).1
            (C.head.canonical H
              (R.tail (R.first.toMMap x.1)))) := by rw [hrSplit]
    _ =
        C.refiner.1
          ((H.largeFusionLimit Y).1
            (t (C.head.canonical H (R.first.toMMap x.1)))) := by
      rw [hcomm]
    _ = C.refiner.1 (qe.representative H z) := by
      rw [hqe, hqrep]
    _ = C.refiner.1 (qline.representative H z) := by
      rw [hqlineRep]

/-- Every one-moving coordinate evaluated in the diagonal large-stage limit
lands in the stage set. -/
theorem largeFusionEval_mem
    (H : SMTree S) :
    ∀ (X : ShapeLargeStage H) (r : AM H X.cut 1),
      H.largeFusionEval X r ∈ X.set := by
  intro X r
  generalize hk : AM.excess H r = k
  induction k using Nat.strong_induction_on generalizing X r with
  | h k ih =>
      by_cases hk0 : k = 0
      · have hexcess0 : AM.excess H r = 0 := hk.trans hk0
        have hex0 : r.topLevel H - X.cut = 0 := by
          simpa [AM.excess] using hexcess0
        have htopLe : r.topLevel H ≤ X.cut :=
          Nat.sub_eq_zero_iff_le.mp hex0
        have rid : r = AM.id1 H X.cut :=
          AM.eq_id1_of_topLevel_le H r htopLe
        rw [rid, H.largeFusionEval_id X]
        exact (H.chooseLargeStage X).head_mem
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hmove : X.cut < r.topLevel H := by
          have hge : X.cut ≤ r.topLevel H := by
            have h0 := H.levelMap_id_le (r.representative H).map X.cut
            simpa [AM.topLevel] using h0
          have hexpos : 0 < AM.excess H r := by
            rw [hk]
            exact hkpos
          unfold AM.excess at hexpos
          omega
        obtain ⟨q, hqex, heval⟩ :=
          H.largeFusionEval_step X r hmove
        have hqk : AM.excess H q = k - 1 := by
          calc
            AM.excess H q = AM.excess H r - 1 := hqex
            _ = k - 1 := by rw [hk]
        have hqmem :
            H.largeFusionEval (H.nextLargeStage X) q ∈
              (H.nextLargeStage X).set :=
          ih (k - 1) (by omega) (H.nextLargeStage X) q hqk
        have hgood :
            H.shapeLineApply (H.chooseLargeStage X).head
              (H.amCastCut
                (show (H.nextLargeStage X).cut =
                    (H.chooseLargeStage X).head.nextCut H by rfl)
                (H.largeFusionEval (H.nextLargeStage X) q))
              (.letter (H.firstMoveSplit r hmove).first) ∈
              H.shapePullback (H.chooseLargeStage X).refiner X.set := by
          exact hqmem (.letter (H.firstMoveSplit r hmove).first)
        rw [heval]
        exact hgood


/-- One positive-excess coordinate in a finite nested tail becomes the
current refiner applied to one algebraic shape line; the tail coordinate at
the next stage has one smaller excess. -/
theorem largeFiniteEval_step
    (H : SMTree S)
    (X : ShapeLargeStage H)
    (d : Nat)
    (r : AM H X.cut 1)
    (hmove : X.cut < r.topLevel H) :
    ∃ q : AM H (H.nextLargeStage X).cut 1,
      AM.excess H q = AM.excess H r - 1 ∧
      H.largeFiniteEval X (d + 1) r =
        H.shapeAct X.cut (H.chooseLargeStage X).refiner
          (H.shapeLineApply (H.chooseLargeStage X).head
            (H.amCastCut rfl
              (H.largeFiniteEval (H.nextLargeStage X) d q))
            (.letter (H.firstMoveSplit r hmove).first)) := by
  let C := H.chooseLargeStage X
  let Y := H.nextLargeStage X
  let R := H.firstMoveSplit r hmove
  obtain ⟨t, htfixHead, htlevHead, htcomm⟩ :=
    H.exists_transport_after_head C.head R.tail R.tail_fixes
  have hcut : Y.cut = C.head.nextCut H := rfl
  have htfix : t.FixesBelow H Y.cut := by
    rw [hcut]
    exact htfixHead
  have htlev :
      H.levelMap t.map Y.cut =
        Y.cut + (H.levelMap R.tail.map (X.cut + 1) - (X.cut + 1)) := by
    rw [hcut]
    exact htlevHead
  let q : AM H Y.cut 1 := t.toAM H Y.cut 1 htfix
  have hqex : AM.excess H q = AM.excess H r - 1 := by
    unfold AM.excess
    rw [show q.topLevel H = H.levelMap t.map Y.cut by
      exact MMap.toAM_one_topLevel H t Y.cut htfix]
    rw [htlev]
    have htail := H.firstMoveSplit_tail_excess r hmove
    change
      (Y.cut +
          (H.levelMap R.tail.map (X.cut + 1) - (X.cut + 1)) -
        Y.cut) =
        r.topLevel H - X.cut - 1
    rw [Nat.add_sub_cancel_left]
    simpa [AM.excess] using htail
  refine ⟨q, hqex, ?_⟩
  let qe : AM H Y.cut 1 := H.largeFiniteEval Y d q
  have hlineCast :
      H.amCastCut rfl qe = qe := by rfl
  apply Subtype.ext
  rw [largeFiniteEval, H.shapeAct_val, H.shapeAct_val]
  apply Subtype.ext
  funext x
  have hrTop := r.representative_top H
  have hrVal := congrArg Subtype.val hrTop
  change (r.representative H).restrictLe H X.cut = r.1.1 at hrVal
  have hrx := congrFun hrVal x
  have hsplitVal := congrArg Subtype.val R.agrees
  change
    (MMap.comp H R.tail R.first.toMMap).restrictLe H X.cut =
      r.1.1 at hsplitVal
  have hsx := congrFun hsplitVal x
  have hrSplit :
      r.representative H x.1 =
        R.tail (R.first.toMMap x.1) := by
    calc
      r.representative H x.1 = r.1.1 x := hrx
      _ = R.tail (R.first.toMMap x.1) := hsx.symm
  have hfirstLev :
      LevelTree.lev (R.first.toMMap x.1) ≤ X.cut + 1 := by
    rw [R.first.level_apply H]
    split <;> omega
  have hcomm := htcomm (R.first.toMMap x.1) hfirstLev
  let z : T := C.head.canonical H (R.first.toMMap x.1)
  have hz : LevelTree.lev z ≤ Y.cut := by
    calc
      LevelTree.lev z =
          H.levelMap (C.head.canonical H).map
            (LevelTree.lev (R.first.toMMap x.1)) :=
        (H.levelMap_eq (C.head.canonical H).map
          (a := R.first.toMMap x.1)).symm
      _ ≤ H.levelMap (C.head.canonical H).map (X.cut + 1) :=
        (H.levelMap_strictMono (C.head.canonical H).map).monotone hfirstLev
      _ = C.head.nextCut H := C.head.canonical_level_next H
      _ = Y.cut := hcut.symm
  have hqrep : q.representative H z = t z := by
    exact MMap.toAM_one_representative_agrees H t Y.cut htfix z hz
  have hqe :
      qe.representative H z =
        H.largeFiniteTail Y d (q.representative H z) := by
    exact H.shapeAct_representative_agrees
      Y.cut (H.largeFiniteSubspace Y d) q z hz
  have hlineRep :
      (H.shapeLineApply C.head qe (.letter R.first)).representative H x.1 =
        qe.representative H z := by
    exact H.shapeLineApply_representative_agrees
      C.head qe (.letter R.first) x.1 x.2
  change
    C.refiner.1
      (H.largeFiniteTail Y d
        (C.head.canonical H (r.representative H x.1))) =
      C.refiner.1
        ((H.shapeLineApply C.head
          (H.amCastCut rfl qe) (.letter R.first)).representative H x.1)
  rw [hlineCast]
  apply congrArg C.refiner.1
  rw [hlineRep]
  calc
    H.largeFiniteTail Y d
        (C.head.canonical H (r.representative H x.1)) =
      H.largeFiniteTail Y d
        (C.head.canonical H
          (R.tail (R.first.toMMap x.1))) := by rw [hrSplit]
    _ = H.largeFiniteTail Y d
        (t (C.head.canonical H (R.first.toMMap x.1))) := by rw [hcomm]
    _ = H.largeFiniteTail Y d (q.representative H z) := by rw [hqrep]
    _ = qe.representative H z := hqe.symm


/-- Boolean Ramsey theorem for one-moving shape maps, obtained by the two
Milliken fusions above. -/
theorem shapeBinaryRamsey
    (H : SMTree S) (n : Nat) :
    (H.shapeSubspaceAction n).BinaryRamsey := by
  classical
  letI : Nonempty (AM H n 1) := ⟨AM.id1 H n⟩
  intro colour
  let A0 : Set (AM H n 1) := {g | colour g = false}
  let A1 : Set (AM H n 1) := {g | colour g = true}
  have hcover : Set.univ ⊆ A0 ∪ A1 := by
    intro g hg
    cases h : colour g with
    | false =>
        exact Or.inl h
    | true =>
        exact Or.inr h
  obtain ⟨W, hlarge⟩ :=
    (H.shapeSubspaceAction n).binary_cover_has_large_pullback
      A0 A1 hcover
  rcases hlarge with h0 | h1
  · let X : ShapeLargeStage H := {
      cut := n
      set := H.shapePullback W A0
      large := h0
    }
    let L : ShapeSubspace H n := H.largeFusionLimit X
    let V : ShapeSubspace H n := ShapeSubspace.comp H W L
    refine ⟨V, ?_⟩
    intro x y
    have hx := H.largeFusionEval_mem X x
    have hy := H.largeFusionEval_mem X y
    have hx0 :
        colour (H.shapeAct n W (H.shapeAct n L x)) = false := by
      exact hx
    have hy0 :
        colour (H.shapeAct n W (H.shapeAct n L y)) = false := by
      exact hy
    change
      colour (H.shapeAct n V x) =
        colour (H.shapeAct n V y)
    rw [show H.shapeAct n V x =
        H.shapeAct n W (H.shapeAct n L x) by
      exact H.shapeAct_comp n W L x]
    rw [show H.shapeAct n V y =
        H.shapeAct n W (H.shapeAct n L y) by
      exact H.shapeAct_comp n W L y]
    exact hx0.trans hy0.symm
  · let X : ShapeLargeStage H := {
      cut := n
      set := H.shapePullback W A1
      large := h1
    }
    let L : ShapeSubspace H n := H.largeFusionLimit X
    let V : ShapeSubspace H n := ShapeSubspace.comp H W L
    refine ⟨V, ?_⟩
    intro x y
    have hx := H.largeFusionEval_mem X x
    have hy := H.largeFusionEval_mem X y
    have hx1 :
        colour (H.shapeAct n W (H.shapeAct n L x)) = true := by
      exact hx
    have hy1 :
        colour (H.shapeAct n W (H.shapeAct n L y)) = true := by
      exact hy
    change
      colour (H.shapeAct n V x) =
        colour (H.shapeAct n V y)
    rw [show H.shapeAct n V x =
        H.shapeAct n W (H.shapeAct n L x) by
      exact H.shapeAct_comp n W L x]
    rw [show H.shapeAct n V y =
        H.shapeAct n W (H.shapeAct n L y) by
      exact H.shapeAct_comp n W L y]
    exact hx1.trans hy1.symm

/-- Finite-colour Ramsey theorem for one-moving shape-preserving maps. -/
theorem shapeOneDimensionalRamsey
    (H : SMTree S) (n : Nat)
    {κ : Type w} [Fintype κ] [DecidableEq κ]
    (colour : AM H n 1 → κ) :
    ∃ W : ShapeSubspace H n,
      (H.shapeSubspaceAction n).Homogeneous colour W := by
  letI : Nonempty (AM H n 1) := ⟨AM.id1 H n⟩
  exact (H.shapeSubspaceAction n).finiteRamsey_of_binary
    (H.shapeBinaryRamsey n) colour


/-- A finite nested tail of length excess(r)+1 already sends r into the
current large set. -/
theorem largeFiniteEval_mem
    (H : SMTree S) :
    ∀ (X : ShapeLargeStage H) (r : AM H X.cut 1),
      H.largeFiniteEval X (AM.excess H r + 1) r ∈ X.set := by
  intro X r
  generalize hk : AM.excess H r = k
  induction k using Nat.strong_induction_on generalizing X r with
  | h k ih =>
      by_cases hk0 : k = 0
      · have hex0 : AM.excess H r = 0 := hk.trans hk0
        have htopLe : r.topLevel H ≤ X.cut := by
          unfold AM.excess at hex0
          exact Nat.sub_eq_zero_iff_le.mp hex0
        have rid : r = AM.id1 H X.cut :=
          AM.eq_id1_of_topLevel_le H r htopLe
        rw [rid]
        simpa [AM.excess, AM.id1_topLevel] using
          H.largeFiniteEval_id_mem X
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hmove : X.cut < r.topLevel H := by
          have hpos : 0 < AM.excess H r := by
            rw [hk]
            exact hkpos
          unfold AM.excess at hpos
          omega
        obtain ⟨q, hqex, heval⟩ :=
          H.largeFiniteEval_step X k r hmove
        let Y := H.nextLargeStage X
        let C := H.chooseLargeStage X
        have hqk : AM.excess H q = k - 1 := by
          calc
            AM.excess H q = AM.excess H r - 1 := hqex
            _ = k - 1 := by rw [hk]
        have hqmem0 :=
          ih (k - 1) (by omega) Y q hqk
        have hlen : AM.excess H q + 1 = k := by
          rw [hqk]
          omega
        have hqmem :
            H.largeFiniteEval Y k q ∈ Y.set := by
          simpa [hlen] using hqmem0
        have hgood :
            H.largeFiniteEval Y k q ∈
              H.shapeGoodTails C.head
                (H.shapePullback C.refiner X.set) := by
          simpa [Y, C, nextLargeStage] using hqmem
        have hline :
            H.shapeLineApply C.head
                (H.largeFiniteEval Y k q)
                (.letter (H.firstMoveSplit r hmove).first) ∈
              H.shapePullback C.refiner X.set :=
          hgood (.letter (H.firstMoveSplit r hmove).first)
        have hout :
            H.shapeAct X.cut C.refiner
                (H.shapeLineApply C.head
                  (H.largeFiniteEval Y k q)
                  (.letter (H.firstMoveSplit r hmove).first)) ∈ X.set := by
          exact hline
        rw [hk]
        have heval' := heval
        simpa [Y, C] using heval'.symm ▸ hout

end SMTree
end SuccessorTree

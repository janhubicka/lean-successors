import SuccessorTree.ShapeGoodTails
import SuccessorTree.ShapeBlockForcing
import Mathlib.Tactic

/-!
# Direct Milliken fusion for one-moving shape maps

This follows the pre-Ramsey-space proof of the shape-preserving Ramsey
theorem.  The first goal is the old "1-dimensional pigeonhole in large
sets": every large subset of AM^n_1 contains the whole local line generated
by one AM^n_2 block.

All refinements are explicit right compositions; no fat subtree or pullback
from range containment is used.
-/

namespace SuccessorTree
namespace SMTree

open SuccessorTree.HalesJewett

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- The paper's local line input, packaged as AM^n_1. -/
noncomputable def lineInputAM
    (H : SMTree S) (n : Nat) :
    LineInput (OneLevelLetter H n) → AM H n 1
  | .base => AM.id1 H n
  | .letter e =>
      e.toMMap.toAM H n 1 (by
        intro x hx
        exact e.eq_id_below H hx)

theorem lineInputAM_representative_agrees
    (H : SMTree S) (n : Nat)
    (p : LineInput (OneLevelLetter H n))
    (x : T) (hx : LevelTree.lev x ≤ n) :
    (H.lineInputAM n p).representative H x =
      localInputMMap H n p x := by
  cases p with
  | base =>
      exact MMap.toAM_one_representative_agrees
        H (MMap.id H) n (MMap.id_fixesBelow H n) x hx
  | letter e =>
      exact MMap.toAM_one_representative_agrees
        H e.toMMap n
          (by
            intro y hy
            exact e.eq_id_below H hy)
          x hx

/-- Exact one-moving words cannot end below their frozen source level. -/
theorem AMExact.base_le
    (H : SMTree S) {n m : Nat}
    (p : AMExact H n m) :
    n ≤ m := by
  have h := H.levelMap_id_le (p.1.representative H).map n
  have htop :
      H.levelMap (p.1.representative H).map n = m := by
    simpa [AM.topLevel] using p.2
  exact h.trans_eq htop

/-- Compose an exact n-to-m one-moving prefix with one one-moving map based
at m. -/
noncomputable def composeAcross
    (H : SMTree S)
    {n m : Nat}
    (p : AMExact H n m)
    (q : AM H m 1) :
    AM H n 1 := by
  have hnm : n ≤ m := p.base_le H
  have hqfix : (q.representative H).FixesBelow H n := by
    intro x hx
    exact q.representative_fixesBelow H x (lt_of_lt_of_le hx hnm)
  let K : MMap H :=
    MMap.comp H (q.representative H) (p.1.representative H)
  exact K.toAM H n 1
    (MMap.comp_fixesBelow H
      (q.representative H) (p.1.representative H) n
      hqfix p.1.representative_fixesBelow)

theorem composeAcross_representative_agrees
    (H : SMTree S)
    {n m : Nat}
    (p : AMExact H n m)
    (q : AM H m 1)
    (x : T) (hx : LevelTree.lev x ≤ n) :
    (H.composeAcross p q).representative H x =
      q.representative H (p.1.representative H x) := by
  unfold composeAcross
  apply MMap.toAM_one_representative_agrees
  exact hx

/-- Evaluate a local m-word after an exact n-to-m prefix and an outer
n-subspace. -/
noncomputable def crossEval
    (H : SMTree S)
    {n m : Nat}
    (F : ShapeSubspace H n)
    (p : AMExact H n m)
    (q : AM H m 1) :
    AM H n 1 :=
  H.shapeAct n F (H.composeAcross p q)

/-- Right refinement by a replay block at the exact target level m. -/
def refineByReplay
    (H : SMTree S)
    {n m : Nat}
    (F : ShapeSubspace H n)
    (p : AMExact H n m)
    (R : ReplayBlock H m) :
    ShapeSubspace H n :=
  ShapeSubspace.comp H F
    (ShapeSubspace.weaken H (p.base_le H)
      ⟨R.toMMap, R.fixesBelow⟩)

/-- The base member of a replay line is exactly the effect of refining the
outer subspace by that replay block. -/
theorem crossEval_replay_base
    (H : SMTree S)
    {n m : Nat}
    (F : ShapeSubspace H n)
    (p : AMExact H n m)
    (R : ReplayBlock H m) :
    H.crossEval F p (replayApplyAM H m R LineInput.base) =
      H.shapeAct n (H.refineByReplay F p R) p.1 := by
  apply Subtype.ext
  rw [crossEval, H.shapeAct_val, H.shapeAct_val]
  apply Subtype.ext
  funext x
  have hpLev :
      LevelTree.lev (p.1.representative H x.1) ≤ m := by
    exact (p.1.level_le_topLevel H x.1 x.2).trans_eq p.2
  have hbase :=
    H.replayApplyAM_base_representative_agrees
      m R (p.1.representative H x.1) hpLev
  have hcomp :=
    H.composeAcross_representative_agrees p
      (replayApplyAM H m R LineInput.base) x.1 x.2
  change
    F.1
      ((H.composeAcross p
        (replayApplyAM H m R LineInput.base)).representative H x.1) =
      F.1 (R.toMMap (p.1.representative H x.1))
  rw [hcomp, hbase]

/-- A two-level block obtained by inserting an exact prefix into a replay
block and then applying the current outer subspace. -/
noncomputable def replayTwoBlock
    (H : SMTree S)
    {n m : Nat}
    (F : ShapeSubspace H n)
    (p : AMExact H n m)
    (R : ReplayBlock H m) :
    AM H n 2 := by
  let K : MMap H :=
    MMap.comp H F.1
      (MMap.comp H R.toMMap (p.1.canonical H))
  have hfixR : R.toMMap.FixesBelow H n := by
    intro x hx
    exact R.fixesBelow x (lt_of_lt_of_le hx (p.base_le H))
  have hfixInner :
      (MMap.comp H R.toMMap (p.1.canonical H)).FixesBelow H n :=
    MMap.comp_fixesBelow H
      R.toMMap (p.1.canonical H) n
      hfixR (p.1.canonical_fixesBelow H)
  exact K.toAM H n 2
    (MMap.comp_fixesBelow H F.1
      (MMap.comp H R.toMMap (p.1.canonical H)) n
      F.2 hfixInner)

/-- Chosen representatives of a two-level block built by toAM agree with the
literal total block on its represented source segment. -/
theorem replayTwoBlock_representative_agrees
    (H : SMTree S)
    {n m : Nat}
    (F : ShapeSubspace H n)
    (p : AMExact H n m)
    (R : ReplayBlock H m)
    (x : T) (hx : LevelTree.lev x ≤ n + 1) :
    (H.replayTwoBlock F p R).representative H x =
      F.1 (R.toMMap (p.1.canonical H x)) := by
  let K : MMap H :=
    MMap.comp H F.1
      (MMap.comp H R.toMMap (p.1.canonical H))
  have htop := (H.replayTwoBlock F p R).representative_top H
  have hval := congrArg Subtype.val htop
  change
    ((H.replayTwoBlock F p R).representative H).restrictLe H (n + 1) =
      K.restrictLe H (n + 1) at hval
  exact congrFun hval ⟨x, hx⟩

/-- The finite line generated by the replay two-block is transported to the
local replay line at level m. -/
theorem blockEval_replayTwoBlock_line
    (H : SMTree S)
    {n m : Nat}
    (F : ShapeSubspace H n)
    (p : AMExact H n m)
    (R : ReplayBlock H m)
    (x : LineInput (OneLevelLetter H n)) :
    ∃ y : LineInput (OneLevelLetter H m),
      H.blockEval (H.replayTwoBlock F p R) (H.lineInputAM n x) =
        H.crossEval F p (replayApplyAM H m R y) := by
  cases x with
  | base =>
      refine ⟨LineInput.base, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      funext z
      have hid :=
        H.lineInputAM_representative_agrees n LineInput.base z.1 z.2
      have hblock :=
        H.replayTwoBlock_representative_agrees F p R z.1
          (Nat.le_succ_of_le z.2)
      have hid' :
          (H.lineInputAM n LineInput.base).representative H z.1 = z.1 := by
        simpa [localInputMMap] using hid
      have hpCan :
          p.1.canonical H z.1 = p.1.representative H z.1 := by
        rw [AM.canonical, H.canonicalExtension_agrees
          (p.1.representative H) n z.1 z.2]
      have hq :=
        H.composeAcross_representative_agrees p
          (replayApplyAM H m R LineInput.base) z.1 z.2
      change
        (H.replayTwoBlock F p R).representative H
          ((H.lineInputAM n LineInput.base).representative H z.1) =
        F.1
          ((H.composeAcross p
            (replayApplyAM H m R LineInput.base)).representative H z.1)
      rw [hid', hblock, hpCan, hq]
      exact congrArg F.1
        (H.replayApplyAM_base_representative_agrees
          m R (p.1.representative H z.1)
          (by
            exact p.1.level_le_topLevel H z.1 z.2 |>.trans_eq p.2))
  | letter e =>
      have hpm : H.levelMap (p.1.representative H).map n = m := by
        simpa [AM.topLevel] using p.2
      subst m
      let et : OneLevelLetter H
          (H.levelMap (p.1.representative H).map n) :=
        H.transportLetter (p.1.representative H) n e
      refine ⟨LineInput.letter et, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      funext z
      have he :=
        H.lineInputAM_representative_agrees n (LineInput.letter e) z.1 z.2
      have he' :
          (H.lineInputAM n (LineInput.letter e)).representative H z.1 =
            e.toMMap z.1 := by
        simpa [localInputMMap] using he
      have hblock :=
        H.replayTwoBlock_representative_agrees F p R
          (e.toMMap z.1) (by
            rw [e.level_apply H]
            split <;> omega)
      have htransport :=
        H.transportLetter_commutes
          (p.1.representative H) n e z.1 z.2
      have hpCan :
          p.1.canonical H z.1 = p.1.representative H z.1 := by
        rw [AM.canonical, H.canonicalExtension_agrees
          (p.1.representative H) n z.1 z.2]
      have hq :=
        H.composeAcross_representative_agrees p
          (replayApplyAM H m R (LineInput.letter et)) z.1 z.2
      have hfixComp :
          (MMap.comp H R.toMMap et.toMMap).FixesBelow H
            (H.levelMap (p.1.representative H).map n) :=
        MMap.comp_fixesBelow H R.toMMap et.toMMap
          (H.levelMap (p.1.representative H).map n)
          R.fixesBelow
          (by
            intro a ha
            exact et.eq_id_below H ha)
      have hlocal :
          (replayApplyAM H
              (H.levelMap (p.1.representative H).map n)
              R (LineInput.letter et)).representative H
              (p.1.representative H z.1) =
            R.toMMap
              (et.toMMap (p.1.representative H z.1)) := by
        exact MMap.toAM_one_representative_agrees
          H (MMap.comp H R.toMMap et.toMMap)
          (H.levelMap (p.1.representative H).map n)
          hfixComp
          (p.1.representative H z.1)
          (by
            exact (p.1.level_le_topLevel H z.1 z.2).trans_eq p.2)
      change
        (H.replayTwoBlock F p R).representative H
          ((H.lineInputAM n (LineInput.letter e)).representative H z.1) =
        F.1
          ((H.composeAcross p
            (replayApplyAM H m R (LineInput.letter et))).representative H z.1)
      rw [he', hblock, hq, hlocal]
      change
        F.1 (R.toMMap (p.1.canonical H (e.toMMap z.1))) =
          F.1 (R.toMMap (et.toMMap (p.1.representative H z.1)))
      apply congrArg F.1
      apply congrArg R.toMMap
      have ht :
          et.toMMap (p.1.representative H z.1) =
            p.1.canonical H (e.toMMap z.1) := by
        change
          (H.transportLetter (p.1.representative H) n e)
              (p.1.canonical H z.1) =
            p.1.canonical H (e.toMMap z.1)
        exact H.transportLetter_commutes
          (p.1.representative H) n e z.1 z.2
      simpa [hpCan] using ht

end SMTree
end SuccessorTree

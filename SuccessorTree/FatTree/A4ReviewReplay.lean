import SuccessorTree.FatTree.A4ReplaySemantics

/-!
# Actual-edge correctness of the review's common second block

The optional profile at a trace may be bottom. Equality of bottom profiles
cannot be used to identify successor codes. Instead, a constant symbol uses
its unchanged original recorded occurrence, and a parameter symbol repeats
the actual first-parameter edge. The pointwise induction below works at every
trace coordinate, without a non-bottom hypothesis and without A4.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v w
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

private theorem review_map_fixed {A : Type*} (f : A → A) (xs : List A)
    (h : ∀ x ∈ xs, f x = x) : xs.map f = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx : f x = x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons, hx, ih hxs]

/-- A canonical ambient row transports a successor edge at its source cut
without changing the edge's parameters or character. -/
theorem review_rowExtension_succ
    (U : FatTree H) (i : Nat) {x z : T} (hx : LevelTree.lev x = U.cut i)
    {params : List T} {ch : Label} (he : S.succ x params ch = some z) :
    S.succ (U.rowExtension H i x) params ch =
      some (U.rowExtension H i z) := by
  let R := U.rowExtension H i
  have hz : LevelTree.lev z = U.cut i + 1 := by
    rw [LevelTree.covBy_level_eq (S.covBy_of_succ_eq_some he), hx]
  have hlevels : H.levelMap R.map (LevelTree.lev z) =
      H.levelMap R.map (LevelTree.lev x) + 1 := by
    rw [hz, hx]
    change H.levelMap (U.rowExtension H i).map (U.cut i + 1) =
      H.levelMap (U.rowExtension H i).map (U.cut i) + 1
    rw [U.rowExtension_level_succ H i, U.rowExtension_level_at_cut H i]
    exact (U.row_cut i).symm
  have hparams : params.map R.map = params := by
    apply review_map_fixed
    intro p hp
    apply U.rowExtension_fixesBelow H i
    have hlt := S.parameter_level_lt he hp
    rwa [hx] at hlt
  have h := H.succ_eq_of_consecutive_levels R.map he hlevels
  rwa [hparams] at h

private theorem review_duplicate_congr
    {r r' m m' : Nat} (hrm : r < m) (hrm' : r' < m')
    (hr : r = r') (hm : m = m') :
    H.duplicate r m hrm = H.duplicate r' m' hrm' := by
  cases hr
  cases hm
  rfl

namespace ProfileReplayState

variable {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
variable (U : FatTree H) (a : Nat) (trace : C → AM H c 1)
variable (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
variable (K : ProfileCollector H U a trace)

omit [Fintype C] [Nonempty C] in
include hend in
private theorem review_trace_level
    (j : C) (x : InitialNode T c) (hx : LevelTree.lev x.1 = c) :
    LevelTree.lev ((trace j).representative H x.1) = U.cut a := by
  calc
    LevelTree.lev ((trace j).representative H x.1) =
        H.levelMap ((trace j).representative H).map (LevelTree.lev x.1) :=
      (H.levelMap_eq ((trace j).representative H).map (a := x.1)).symm
    _ = (trace j).rowEndLevel H := by rw [hx]; rfl
    _ = U.cut a := hend j

/-- Constant suffix symbols have exactly the same total M-map in the common
second block and in a replay of the evaluated word. Occurrence stability,
not equality of optional profiles, supplies this identity. -/
theorem review_common_const_letter
    (Rstar R : ProfileReplayState H U a trace hend K)
    (r : Nat) (beta : SeenProfile H K)
    (hindex : a + R.collector.index = firstParameterIndex H Rstar + 1 + r) :
    (lineTailLetter H U a trace hend K Rstar r (.const beta)).toMMap =
      (replayLetter H U a trace hend K R beta).toMMap := by
  have hbeta : beta.1 ∈ Rstar.collector.seen := by
    rw [Rstar.seen_eq]
    exact beta.2
  have hlevel := ProfileCollector.reachable_occurrence_level H hend
    Rstar.reachable beta.1 beta.2 hbeta
  have hnew := fixed_occurrence_level_lt H hend R beta
  have hold : (Rstar.collector.occurrence beta.1 hbeta).level <
      U.cut (firstParameterIndex H Rstar + 1 + r) := by
    calc
      (Rstar.collector.occurrence beta.1 hbeta).level =
          (K.occurrence beta.1 beta.2).level := hlevel
      _ < U.cut (a + R.collector.index) := hnew
      _ = U.cut (firstParameterIndex H Rstar + 1 + r) := congrArg U.cut hindex
  rw [replayLetter_eq_fixed H hend R beta]
  change H.duplicate (Rstar.collector.occurrence beta.1 hbeta).level
      (U.cut (firstParameterIndex H Rstar + 1 + r)) hold =
    H.duplicate (K.occurrence beta.1 beta.2).level
      (U.cut (a + R.collector.index)) hnew
  exact review_duplicate_congr H hold hnew hlevel (congrArg U.cut hindex.symm)

/-- The first parameter edge carries the code of its original recorded
occurrence, even when that profile coordinate is bottom. -/
theorem review_first_parameter_edge
    (Rstar : ProfileReplayState H U a trace hend K) (alpha : SeenProfile H K)
    (j : C) (x : InitialNode T c) (hx : LevelTree.lev x.1 = c)
    (params : List T) (ch : Label)
    (hcode : S.succ
      ((K.occurrence alpha.1 alpha.2).base ((trace j).representative H x.1))
      params ch = some
        ((K.occurrence alpha.1 alpha.2).letter.toMMap
          ((K.occurrence alpha.1 alpha.2).base ((trace j).representative H x.1)))) :
    S.succ
      (U.rowExtension H (firstParameterIndex H Rstar)
        (Rstar.collector.state ((trace j).representative H x.1))) params ch =
      some ((step H U a trace hend K Rstar alpha).collector.state
        ((trace j).representative H x.1)) := by
  have h := replayLetter_rule_from_original H hend Rstar alpha j x hx params ch hcode
  have hlev := Rstar.collector.state.level_apply H U a Rstar.collector.index
    (review_trace_level H U a trace hend j x hx)
  have hrow := review_rowExtension_succ H U (a + Rstar.collector.index) hlev h
  simpa only [firstParameterIndex, step_state_apply] using hrow

/-- A suffix symbol in the common second block agrees on an actual history
point with the evaluated replay symbol. The first-parameter endpoint is
retained as an ancestor; that is the only additional geometric invariant. -/
theorem review_common_letter_agrees
    (Rstar R : ProfileReplayState H U a trace hend K)
    (alpha : SeenProfile H K) (r : Nat)
    (hindex : a + R.collector.index = firstParameterIndex H Rstar + 1 + r)
    (j : C) (x : InitialNode T c) (hx : LevelTree.lev x.1 = c)
    (hbelow :
      (step H U a trace hend K Rstar alpha).collector.state
          ((trace j).representative H x.1) ≤
        R.collector.state ((trace j).representative H x.1))
    (s : LineSymbol (SeenProfile H K)) :
    (lineTailLetter H U a trace hend K Rstar r s).toMMap
        (R.collector.state ((trace j).representative H x.1)) =
      (replayLetter H U a trace hend K R (LineSymbol.eval alpha s)).toMMap
        (R.collector.state ((trace j).representative H x.1)) := by
  cases s with
  | const beta =>
      exact congrArg (fun F : MMap H => F
        (R.collector.state ((trace j).representative H x.1)))
        (review_common_const_letter H U a trace hend K Rstar R r beta hindex)
  | parameter =>
      let qx := (trace j).representative H x.1
      let occ := K.occurrence alpha.1 alpha.2
      have hq : LevelTree.lev qx = U.cut a :=
        review_trace_level H U a trace hend j x hx
      have hocclev : LevelTree.lev (occ.base qx) = occ.level := by
        calc
          LevelTree.lev (occ.base qx) = H.levelMap occ.base.map (LevelTree.lev qx) :=
            (H.levelMap_eq occ.base.map (a := qx)).symm
          _ = H.levelMap occ.base.map (U.cut a) := by rw [hq]
          _ = H.levelMap occ.base.map ((trace j).rowEndLevel H) :=
            congrArg (H.levelMap occ.base.map) (hend j).symm
          _ = occ.level := occ.base_top j
      let code := H.letterCode occ.letter (occ.base qx) hocclev
      have hedge := review_first_parameter_edge H U a trace hend K
        Rstar alpha j x hx code.params code.char code.succ_eq
      let parent := U.rowExtension H (firstParameterIndex H Rstar)
        (Rstar.collector.state qx)
      let child := (step H U a trace hend K Rstar alpha).collector.state qx
      let b := R.collector.state qx
      let ell := firstParameterLevel H Rstar
      let m := U.cut (firstParameterIndex H Rstar + 1 + r)
      have hparent : LevelTree.lev parent = ell := by
        have hstar := Rstar.collector.state.level_apply H U a Rstar.collector.index hq
        calc
          LevelTree.lev parent = H.levelMap
              (U.rowExtension H (firstParameterIndex H Rstar)).map
              (LevelTree.lev (Rstar.collector.state qx)) :=
            (H.levelMap_eq (U.rowExtension H (firstParameterIndex H Rstar)).map
              (a := Rstar.collector.state qx)).symm
          _ = H.levelMap (U.rowExtension H (firstParameterIndex H Rstar)).map
              (U.cut (firstParameterIndex H Rstar)) :=
            congrArg _ hstar
          _ = ell := U.rowExtension_level_at_cut H (firstParameterIndex H Rstar)
      have hb : LevelTree.lev b = m := by
        exact (R.collector.state.level_apply H U a R.collector.index hq).trans
          (congrArg U.cut hindex)
      have hchild : LevelTree.lev child = ell + 1 := by
        exact (LevelTree.covBy_level_eq (S.covBy_of_succ_eq_some hedge)).trans
          (congrArg (fun n => n + 1) hparent)
      have hlt : ell < m := by
        have hlev := LevelTree.level_le_of_le hbelow
        change LevelTree.lev child ≤ LevelTree.lev b at hlev
        rw [hchild, hb] at hlev
        omega
      have hcommon : S.succ b code.params code.char =
          some ((lineTailLetter H U a trace hend K Rstar r .parameter).toMMap b) := by
        change S.succ b code.params code.char = some (H.duplicate ell m hlt b)
        exact H.duplicate_rule ell m hlt parent b code.params code.char child
          hparent hb hedge hbelow
      have hactual := replayLetter_rule_from_original H hend R alpha j x hx
        code.params code.char code.succ_eq
      exact Option.some.inj (hcommon.symm.trans hactual)

/-- Pointwise common-tail evaluation, with the stage parameter explicit.
The existing `LineTailState` supplies its admissible total map and geometry. -/
noncomputable def reviewTailEval
    (Rstar : ProfileReplayState H U a trace hend K) :
    Nat → List (LineSymbol (SeenProfile H K)) → T → T
  | _, [], t => t
  | r, s :: xs, t => reviewTailEval Rstar (r + 1) xs
      (U.rowExtension H (firstParameterIndex H Rstar + 1 + r)
        ((lineTailLetter H U a trace hend K Rstar r s).toMMap t))

/-- Actual-edge induction for an arbitrary suffix. No coordinate is discarded
when its optional profile is bottom. -/
theorem reviewTailEval_replay
    (Rstar : ProfileReplayState H U a trace hend K)
    (alpha : SeenProfile H K)
    (j : C) (x : InitialNode T c) (hx : LevelTree.lev x.1 = c)
    (xs : List (LineSymbol (SeenProfile H K))) :
    ∀ (r : Nat) (R : ProfileReplayState H U a trace hend K),
      a + R.collector.index = firstParameterIndex H Rstar + 1 + r →
      (step H U a trace hend K Rstar alpha).collector.state
          ((trace j).representative H x.1) ≤
        R.collector.state ((trace j).representative H x.1) →
      reviewTailEval H U a trace hend K Rstar r xs
          (R.collector.state ((trace j).representative H x.1)) =
        ((evalWord alpha xs).foldl
          (fun Q beta => step H U a trace hend K Q beta) R).collector.state
            ((trace j).representative H x.1) := by
  induction xs with
  | nil => intro r R _ _; rfl
  | cons s xs ih =>
      intro r R hindex hbelow
      let Rnext := step H U a trace hend K R (LineSymbol.eval alpha s)
      let qx := (trace j).representative H x.1
      have hletter := review_common_letter_agrees H U a trace hend K
        Rstar R alpha r hindex j x hx hbelow s
      have hstep : U.rowExtension H (firstParameterIndex H Rstar + 1 + r)
          ((lineTailLetter H U a trace hend K Rstar r s).toMMap (R.collector.state qx)) =
          Rnext.collector.state qx := by
        calc
          U.rowExtension H (firstParameterIndex H Rstar + 1 + r)
              ((lineTailLetter H U a trace hend K Rstar r s).toMMap (R.collector.state qx)) =
            U.rowExtension H (firstParameterIndex H Rstar + 1 + r)
              ((replayLetter H U a trace hend K R (LineSymbol.eval alpha s)).toMMap
                (R.collector.state qx)) := congrArg _ hletter
          _ = U.rowExtension H (a + R.collector.index)
              ((replayLetter H U a trace hend K R (LineSymbol.eval alpha s)).toMMap
                (R.collector.state qx)) :=
            congrArg (fun i => U.rowExtension H i
              ((replayLetter H U a trace hend K R (LineSymbol.eval alpha s)).toMMap
                (R.collector.state qx))) hindex.symm
          _ = Rnext.collector.state qx :=
            (step_state_apply H U a trace hend K R (LineSymbol.eval alpha s) qx).symm
      have hindex' : a + Rnext.collector.index =
          firstParameterIndex H Rstar + 1 + (r + 1) := by
        change a + (R.collector.index + 1) = _
        omega
      have hbelow' : (step H U a trace hend K Rstar alpha).collector.state qx ≤
          Rnext.collector.state qx :=
        hbelow.trans (TraceHistoryState.le_step H U a R.collector.index
          R.collector.state (replayLetter H U a trace hend K R (LineSymbol.eval alpha s))
          (review_trace_level H U a trace hend j x hx))
      change reviewTailEval H U a trace hend K Rstar (r + 1) xs
        (U.rowExtension H (firstParameterIndex H Rstar + 1 + r)
          ((lineTailLetter H U a trace hend K Rstar r s).toMMap (R.collector.state qx))) = _
      rw [hstep]
      exact ih (r + 1) Rnext hindex' hbelow'

/-- The pointwise recursion agrees with the already geometric common-tail
state, for any starting state and every input node. -/
theorem reviewTailEval_eq_foldl_state
    (Rstar : ProfileReplayState H U a trace hend K)
    (xs : List (LineSymbol (SeenProfile H K))) :
    ∀ (Q : LineTailState H U a trace hend K Rstar) (z : T),
      reviewTailEval H U a trace hend K Rstar Q.index xs (Q.state z) =
        (xs.foldl (fun Q s => LineTailState.step H U a trace hend K Rstar Q s) Q).state z := by
  induction xs with
  | nil => intro Q z; rfl
  | cons s xs ih =>
      intro Q z
      have h := ih (LineTailState.step H U a trace hend K Rstar Q s) z
      change reviewTailEval H U a trace hend K Rstar (Q.index + 1) xs
        ((LineTailState.step H U a trace hend K Rstar Q s).state z) = _ at h
      rw [LineTailState.step_state_apply] at h
      exact h

/-- The common second block replays every evaluated suffix at every trace.
In particular this includes coordinates labelled bottom by the profile. -/
theorem review_common_tail_replays
    (Rstar : ProfileReplayState H U a trace hend K)
    (alpha : SeenProfile H K)
    (xs : List (LineSymbol (SeenProfile H K)))
    (j : C) (x : InitialNode T c) (hx : LevelTree.lev x.1 = c) :
    (LineTailState.word H U a trace hend K Rstar xs).state
        ((step H U a trace hend K Rstar alpha).collector.state
          ((trace j).representative H x.1)) =
      ((evalWord alpha xs).foldl
        (fun R beta => step H U a trace hend K R beta)
        (step H U a trace hend K Rstar alpha)).collector.state
          ((trace j).representative H x.1) := by
  let t := (step H U a trace hend K Rstar alpha).collector.state
    ((trace j).representative H x.1)
  have hfold := reviewTailEval_eq_foldl_state H U a trace hend K Rstar xs
    (LineTailState.initial H U a trace hend K Rstar) t
  have htail : reviewTailEval H U a trace hend K Rstar 0 xs t =
      (LineTailState.word H U a trace hend K Rstar xs).state t := hfold
  rw [← htail]
  exact reviewTailEval_replay H U a trace hend K Rstar alpha j x hx xs 0
    (step H U a trace hend K Rstar alpha)
    (by change a + (Rstar.collector.index + 1) = a + Rstar.collector.index + 1 + 0; omega)
    le_rfl

end ProfileReplayState
end SuccessorTree.SMTree.FatTree

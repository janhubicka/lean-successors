import SuccessorTree.FatTree.A4ProfileSaturation

/-!
# Replaying words of saturated successor-fan profiles

A globally saturated collector contains a witnessed occurrence of every profile
which can appear in a continuation.  M3 lets us replay any such occurrence at
the current cut.  This file packages the resulting word recursion.  It is the
bridge from the finite profile collector to the Hales--Jewett line used in A4.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- A continuation of a fixed profile collector which has not changed the
finite set of seen profiles. -/
structure ProfileReplayState
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace) where
  collector : ProfileCollector H U a trace
  reachable :
    ProfileCollector.ReachableFrom H U a trace hend K collector
  seen_eq : collector.seen = K.seen

namespace ProfileReplayState

/-- The empty replay continuation. -/
noncomputable def initial
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace) :
    ProfileReplayState H U a trace hend K where
  collector := K
  reachable := ProfileCollector.ReachableFrom.refl
  seen_eq := rfl

/-- A recorded occurrence always lies strictly below the current replay cut.
The endpoint of the recorded letter is one level above its source, and that
endpoint lies below the current history state. -/
theorem occurrence_level_lt_current
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (R : ProfileReplayState H U a trace hend K)
    (alpha : FanProfile H C trace)
    (halpha : alpha ∈ R.collector.seen) :
    (R.collector.occurrence alpha halpha).level <
      U.cut (a + R.collector.index) := by
  let occ := R.collector.occurrence alpha halpha
  let j : C := Classical.choice (inferInstance : Nonempty C)
  obtain ⟨x, hx⟩ := H.level_nonempty c
  let xx : InitialNode T c := ⟨x, by omega⟩
  have hqlev :
      LevelTree.lev ((trace j).representative H x) =
        (trace j).rowEndLevel H := by
    calc
      LevelTree.lev ((trace j).representative H x) =
          H.levelMap ((trace j).representative H).map
            (LevelTree.lev x) :=
        (H.levelMap_eq ((trace j).representative H).map (a := x)).symm
      _ = H.levelMap ((trace j).representative H).map c := by rw [hx]
      _ = (trace j).rowEndLevel H := rfl
  have hbaselev :
      LevelTree.lev (occ.base ((trace j).representative H x)) =
        occ.level := by
    calc
      LevelTree.lev (occ.base ((trace j).representative H x)) =
          H.levelMap occ.base.map
            (LevelTree.lev ((trace j).representative H x)) :=
        (H.levelMap_eq occ.base.map
          (a := (trace j).representative H x)).symm
      _ = H.levelMap occ.base.map ((trace j).rowEndLevel H) := by
        rw [hqlev]
      _ = occ.level := occ.base_top j
  have hleft :
      LevelTree.lev
          (occ.letter.toMMap
            (occ.base ((trace j).representative H x))) =
        occ.level + 1 := by
    exact occ.letter.level_succ_at H hbaselev
  have hqsource :
      LevelTree.lev ((trace j).representative H x) = U.cut a := by
    rw [hqlev, hend j]
  have hright :
      LevelTree.lev
          (R.collector.state ((trace j).representative H x)) =
        U.cut (a + R.collector.index) :=
    R.collector.state.level_apply H U a R.collector.index hqsource
  have hle :=
    occ.endpoint_below j xx hx
  have hlevle :=
    LevelTree.level_le_of_le hle
  rw [hleft, hright] at hlevle
  omega

/-- Replay a seen profile at the current cut by duplicating one of its recorded
occurrences. -/
noncomputable def replayLetter
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (R : ProfileReplayState H U a trace hend K)
    (alpha : {p : FanProfile H C trace // p ∈ K.seen}) :
    OneLevelLetter H (U.cut (a + R.collector.index)) := by
  have halpha : alpha.1 ∈ R.collector.seen := by
    rw [R.seen_eq]
    exact alpha.2
  let occ := R.collector.occurrence alpha.1 halpha
  exact duplicateHistoryLetter H occ.level
    (U.cut (a + R.collector.index))
    (occurrence_level_lt_current H U a trace hend K R alpha.1 halpha)

/-- The M3 replay letter has exactly the requested complete profile, including
all bottom coordinates. -/
theorem replayLetter_profile
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (R : ProfileReplayState H U a trace hend K)
    (alpha : {p : FanProfile H C trace // p ∈ K.seen}) :
    ProfileCollector.currentProfile H U a trace R.collector
        (replayLetter H U a trace hend K R alpha) =
      alpha.1 := by
  classical
  have halpha : alpha.1 ∈ R.collector.seen := by
    rw [R.seen_eq]
    exact alpha.2
  let occ := R.collector.occurrence alpha.1 halpha
  let m := U.cut (a + R.collector.index)
  have hrm : occ.level < m := by
    exact occurrence_level_lt_current H U a trace hend K R alpha.1 halpha
  funext j
  have hPtop :
      H.levelMap R.collector.state.toMMap.map
          ((trace j).rowEndLevel H) = m := by
    rw [hend j]
    exact R.collector.state.topLevel
  have hdup :=
    historyProfile_duplicate H
      (trace j)
      occ.base
      R.collector.state.toMMap
      occ.letter
      hrm
      (occ.base_top j)
      hPtop
      (occ.endpoint_below j)
  have hocc :=
    congrFun occ.profile_eq j
  change
    historyProfile H (trace j) R.collector.state.toMMap
      (replayLetter H U a trace hend K R alpha) =
      alpha.1 j
  change
    historyProfile H (trace j) R.collector.state.toMMap
      (duplicateHistoryLetter H occ.level m hrm) =
      alpha.1 j
  exact hdup.trans hocc

/-- Advance a replay continuation by one requested seen profile. -/
noncomputable def step
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (R : ProfileReplayState H U a trace hend K)
    (alpha : {p : FanProfile H C trace // p ∈ K.seen}) :
    ProfileReplayState H U a trace hend K := by
  classical
  let E := replayLetter H U a trace hend K R alpha
  let P :=
    ProfileCollector.advanceAny H U a trace hend R.collector E
  refine {
    collector := P
    reachable := ProfileCollector.ReachableFrom.step R.reachable E
    seen_eq := ?_
  }
  change
    (ProfileCollector.advanceAny H U a trace hend R.collector E).seen =
      K.seen
  rw [ProfileCollector.advanceAny_seen]
  rw [replayLetter_profile H U a trace hend K R alpha]
  rw [R.seen_eq]
  exact Finset.insert_eq_self.mpr alpha.2

/-- Replay a finite word of seen profiles, in its left-to-right order. -/
noncomputable def word
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (w : List {p : FanProfile H C trace // p ∈ K.seen}) :
    ProfileReplayState H U a trace hend K :=
  w.foldl
    (fun R alpha => step H U a trace hend K R alpha)
    (initial H U a trace hend K)

@[simp] theorem word_nil_collector
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace) :
    (word H U a trace hend K []).collector = K := rfl

private theorem foldl_step_index
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace) :
    ∀ (w : List {p : FanProfile H C trace // p ∈ K.seen})
      (R : ProfileReplayState H U a trace hend K),
      (w.foldl
        (fun Q alpha => step H U a trace hend K Q alpha) R).collector.index =
        R.collector.index + w.length := by
  intro w
  induction w with
  | nil =>
      intro R
      simp
  | cons alpha w ih =>
      intro R
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (step H U a trace hend K R alpha)]
      change R.collector.index + 1 + w.length =
        R.collector.index + (w.length + 1)
      omega

/-- Each replayed letter advances the history index by one. -/
theorem word_index
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (w : List {p : FanProfile H C trace // p ∈ K.seen}) :
    (word H U a trace hend K w).collector.index =
      K.index + w.length := by
  exact foldl_step_index H U a trace hend K w
    (initial H U a trace hend K)

end ProfileReplayState

end FatTree
end SMTree
end SuccessorTree

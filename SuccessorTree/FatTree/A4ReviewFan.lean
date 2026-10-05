import SuccessorTree.FatTree.A4ReviewForward

/-!
# Simultaneous homogeneity of the entire admissible raw-fan image

This joins forward M2 saturation, actual-edge common-tail replay, and
starred Hales--Jewett. Only the canonical image of a raw successor table is
assumed admissible. The conclusion is simultaneous over the original finite
trace family, with one common second block.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v w z
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- One-moving approximations are determined by their action on the moving
source level; every lower source level is fixed. -/
theorem review_AM_ext_top {c : Nat} (f g : AM H c 1)
    (h : ∀ x : T, LevelTree.lev x = c → f.representative H x = g.representative H x) :
    f = g := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hf := congrArg Subtype.val (f.representative_top H)
  have hg := congrArg Subtype.val (g.representative_top H)
  change (f.representative H).restrictLe H c = f.1.1 at hf
  change (g.representative H).restrictLe H c = g.1.1 at hg
  have hx : LevelTree.lev x.1 ≤ c := x.2
  calc
    f.1.1 x = f.representative H x.1 := (congrFun hf x).symm
    _ = g.representative H x.1 := by
      rcases lt_or_eq_of_le hx with hlt | heq
      · rw [f.representative_fixesBelow H x.1 hlt, g.representative_fixesBelow H x.1 hlt]
      · exact h x.1 heq
    _ = g.1.1 x := congrFun hg x

namespace ProfileReplayState

variable {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
variable (U : FatTree H) (a : Nat) (trace : C → AM H c 1)
variable (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
variable (K : ProfileCollector H U a trace)

/-- The common first head selected by a starred profile line. -/
noncomputable def reviewLineHead (L : StarLine (SeenProfile H K)) : AM H (U.cut a) 1 :=
  let R := word H U a trace hend K L.star
  TraceHistoryState.headRow H U a R.collector.index R.collector.state

/-- The source cut of the common second head. -/
noncomputable def reviewLineCut (L : StarLine (SeenProfile H K)) : Nat :=
  U.cut (firstParameterIndex H (word H U a trace hend K L.star) + 1)

/-- The common second head; its construction is independent of the evaluated
letter and of the chosen trace coordinate. -/
noncomputable def reviewLineTail (L : StarLine (SeenProfile H K)) :
    AM H (reviewLineCut H U a trace hend K L) 1 :=
  LineTailState.headRow H U a trace hend K
    (word H U a trace hend K L.star) (afterFirstParameter L.word)

/-- Evaluation of a starred line is a first parameter step followed by the
evaluated suffix of that line. -/
theorem review_word_eval (L : StarLine (SeenProfile H K)) (alpha : SeenProfile H K) :
    word H U a trace hend K (L.eval alpha) =
      (evalWord alpha (afterFirstParameter L.word)).foldl
        (fun R beta => step H U a trace hend K R beta)
        (step H U a trace hend K (word H U a trace hend K L.star) alpha) := by
  rw [L.eval_eq_star_parameter_tail, word_append]
  rfl

/-- Close the common-tail identity by the last ambient row. The result is
an equality of actual admissible one-moving approximations. -/
theorem review_lineTail_composite
    (L : StarLine (SeenProfile H K)) (alpha : SeenProfile H K) (j : C)
    (theta : AM H c 1) (htheta : theta.rowEndLevel H = reviewLineCut H U a trace hend K L)
    (hpoint : ∀ (x : InitialNode T c), LevelTree.lev x.1 = c →
      theta.representative H x.1 =
        (step H U a trace hend K (word H U a trace hend K L.star) alpha).collector.state
          ((trace j).representative H x.1)) :
    H.composeAcross (⟨theta, htheta⟩ : AMExact H c (reviewLineCut H U a trace hend K L))
        (reviewLineTail H U a trace hend K L) =
      colouredComposite H U a trace hend (word H U a trace hend K (L.eval alpha)) j := by
  let Rstar := word H U a trace hend K L.star
  let Rfull := word H U a trace hend K (L.eval alpha)
  let xs := afterFirstParameter L.word
  let Q := LineTailState.word H U a trace hend K Rstar xs
  have hQidx : Q.index = xs.length := LineTailState.word_index H U a trace hend K Rstar xs
  have hstaridx : Rstar.collector.index = K.index + L.star.length :=
    word_index H U a trace hend K L.star
  have hfullidx : Rfull.collector.index = K.index + (L.eval alpha).length :=
    word_index H U a trace hend K (L.eval alpha)
  have hlen : (L.eval alpha).length = L.star.length + (1 + xs.length) := by
    rw [L.eval_eq_star_parameter_tail]
    simp [xs, evalWord, Nat.add_comm]
  have hindices : firstParameterIndex H Rstar + 1 + Q.index = a + Rfull.collector.index := by
    change a + Rstar.collector.index + 1 + Q.index = a + Rfull.collector.index
    omega
  apply review_AM_ext_top H
  intro x hx
  let xx : InitialNode T c := ⟨x, Nat.le_of_eq hx⟩
  let qx := (trace j).representative H x
  have hq : LevelTree.lev qx = U.cut a := by
    calc
      LevelTree.lev qx = H.levelMap ((trace j).representative H).map (LevelTree.lev x) :=
        (H.levelMap_eq ((trace j).representative H).map (a := x)).symm
      _ = (trace j).rowEndLevel H := by rw [hx]; rfl
      _ = U.cut a := hend j
  have hthetal : LevelTree.lev (theta.representative H x) = reviewLineCut H U a trace hend K L := by
    calc
      LevelTree.lev (theta.representative H x) = H.levelMap (theta.representative H).map (LevelTree.lev x) :=
        (H.levelMap_eq (theta.representative H).map (a := x)).symm
      _ = theta.rowEndLevel H := by rw [hx]; rfl
      _ = _ := htheta
  have htail : Q.state (theta.representative H x) = Rfull.collector.state qx := by
    rw [hpoint xx hx]
    have h := review_common_tail_replays H U a trace hend K Rstar alpha xs j xx hx
    exact h.trans (congrArg (fun R : ProfileReplayState H U a trace hend K =>
      R.collector.state.toMMap qx) (review_word_eval H U a trace hend K L alpha).symm)
  have hroweq : U.rowExtension H (firstParameterIndex H Rstar + 1 + Q.index) =
      U.rowExtension H (a + Rfull.collector.index) :=
    congrArg (fun i => U.rowExtension H i) hindices
  calc
    (H.composeAcross ⟨theta, htheta⟩ (reviewLineTail H U a trace hend K L)).representative H x =
        (reviewLineTail H U a trace hend K L).representative H (theta.representative H x) :=
      H.composeAcross_representative_agrees ⟨theta, htheta⟩
        (reviewLineTail H U a trace hend K L) x (Nat.le_of_eq hx)
    _ = U.rowExtension H (firstParameterIndex H Rstar + 1 + Q.index)
        (Q.state (theta.representative H x)) :=
      TraceHistoryState.headRow_representative_eq_rowExtension H U
        (firstParameterIndex H Rstar + 1) Q.index Q.state (theta.representative H x)
        (Nat.le_of_eq hthetal)
    _ = U.rowExtension H (a + Rfull.collector.index) (Rfull.collector.state qx) := by
      rw [htail, hroweq]
    _ = (TraceHistoryState.headRow H U a Rfull.collector.index Rfull.collector.state).representative H qx :=
      (TraceHistoryState.headRow_representative_eq_rowExtension H U a Rfull.collector.index
        Rfull.collector.state qx (Nat.le_of_eq hq)).symm
    _ = (colouredComposite H U a trace hend Rfull j).representative H x :=
      (H.composeAcross_representative_agrees (⟨trace j, hend j⟩ : AMExact H c (U.cut a))
        (TraceHistoryState.headRow H U a Rfull.collector.index Rfull.collector.state)
        x (Nat.le_of_eq hx)).symm

/-- Simultaneous homogeneity of every admissible canonical raw-fan image.
Saturation supplies its profile, actual-edge replay identifies its common
second-block composite, and the vector Hales--Jewett colouring supplies the
colour. There is no admissibility assumption on the raw fan. -/
theorem review_exists_profile_fan_homogeneity
    {κ : Type z} [Fintype κ]
    (hglobal : ProfileCollector.GloballySaturated H U a trace hend K)
    (hseen : K.seen.Nonempty) (chi : AM H c 1 → κ) :
    ∃ L : StarLine (SeenProfile H K),
      ∀ (j : C) (e : RawSuccessorFan H (trace j))
        (theta : AM H c 1)
        (htheta : theta.rowEndLevel H = reviewLineCut H U a trace hend K L),
        (∀ (x : InitialNode T c), LevelTree.lev x.1 = c →
          theta.representative H x.1 =
            H.canonicalExtension ((reviewLineHead H U a trace hend K L).representative H)
              (U.cut a) (e.toFun x).1) →
        chi (H.composeAcross ⟨theta, htheta⟩ (reviewLineTail H U a trace hend K L)) =
          chi (colouredComposite H U a trace hend (word H U a trace hend K L.star) j) := by
  obtain ⟨L, hL⟩ := exists_colour_stable_replayLine H U a trace hend K hseen chi
  obtain ⟨p, hp⟩ := hseen
  let alpha0 : SeenProfile H K := ⟨p, hp⟩
  refine ⟨L, ?_⟩
  intro j e theta htheta hraw
  obtain ⟨alpha, _, hpoint⟩ := review_raw_fan_represented H U a trace hend K hglobal
    (word H U a trace hend K L.star) alpha0 j e theta htheta hraw
  rw [review_lineTail_composite H U a trace hend K L alpha j theta htheta hpoint]
  exact hL alpha j

end ProfileReplayState
end SuccessorTree.SMTree.FatTree

import SuccessorTree.FatTree.A4HistoryGeometry

/-!
# The common tail of a replayed profile line

After the first parameter of a starred Hales--Jewett line, the manuscript
builds a common second block.  Constant symbols replay their recorded profile
occurrence, while later parameter symbols replay the first parameter edge.
Interleaving these M3 duplications with the ambient fat-tree rows is naturally
another `TraceHistoryState`.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

namespace ProfileReplayState

/-- The ambient row index immediately before the first parameter edge of a
replay line based at state `R`. -/
def firstParameterIndex
    {c : Nat} {C : Type w} [Fintype C]
    {U : FatTree H} {a : Nat}
    {trace : C → AM H c 1}
    {hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a}
    {K : ProfileCollector H U a trace}
    (R : ProfileReplayState H U a trace hend K) : Nat :=
  a + R.collector.index

/-- The target level of the first parameter edge, i.e. the last image level
of the ambient row used for the first block. -/
noncomputable def firstParameterLevel
    {c : Nat} {C : Type w} [Fintype C]
    {U : FatTree H} {a : Nat}
    {trace : C → AM H c 1}
    {hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a}
    {K : ProfileCollector H U a trace}
    (R : ProfileReplayState H U a trace hend K) : Nat :=
  (U.row (firstParameterIndex H R)).rowEndLevel H

/-- The replay letter used in the common tail after the first parameter.
Constants replay their recorded occurrence; a later parameter replays the
first parameter edge. -/
noncomputable def lineTailLetter
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (R : ProfileReplayState H U a trace hend K)
    (r : Nat)
    (x : LineSymbol (SeenProfile H K)) :
    OneLevelLetter H
      (U.cut (firstParameterIndex H R + 1 + r)) := by
  let j := firstParameterIndex H R
  let m := U.cut (j + 1 + r)
  cases x with
  | const alpha =>
      have halphaR : alpha.1 ∈ R.collector.seen := by
        rw [R.seen_eq]
        exact alpha.2
      let occ := R.collector.occurrence alpha.1 halphaR
      have hoccj : occ.level < U.cut j := by
        simpa [j, firstParameterIndex] using
          occurrence_level_lt_current H U a trace hend K R
            alpha.1 halphaR
      have hjm : U.cut j < m := by
        dsimp [m]
        exact U.cut_strictMono H (by omega)
      exact duplicateHistoryLetter H occ.level m (hoccj.trans hjm)
  | parameter =>
      let ell := firstParameterLevel H R
      have hellNext : ell + 1 = U.cut (j + 1) := by
        dsimp [ell, firstParameterLevel, j, firstParameterIndex]
        exact U.row_cut (a + R.collector.index)
      have hell : ell < m := by
        have hcut :
            U.cut (j + 1) ≤ U.cut (j + 1 + r) :=
          (U.cut_strictMono H).monotone (by omega)
        dsimp [m]
        omega
      exact duplicateHistoryLetter H ell m hell

/-- A common-tail state after a finite number of symbols following the first
parameter. -/
structure LineTailState
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (R : ProfileReplayState H U a trace hend K) where
  index : Nat
  state :
    TraceHistoryState H U (firstParameterIndex H R + 1) index

namespace LineTailState

/-- Empty common tail, immediately after the first parameter edge. -/
noncomputable def initial
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (R : ProfileReplayState H U a trace hend K) :
    LineTailState H U a trace hend K R where
  index := 0
  state :=
    TraceHistoryState.initial H U
      (firstParameterIndex H R + 1)

/-- Process one suffix symbol. -/
noncomputable def step
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (R : ProfileReplayState H U a trace hend K)
    (Q : LineTailState H U a trace hend K R)
    (x : LineSymbol (SeenProfile H K)) :
    LineTailState H U a trace hend K R := by
  let j := firstParameterIndex H R
  have hcut :
      U.cut ((j + 1) + Q.index) =
        U.cut (j + 1 + Q.index) := by
    congr 2 <;> omega
  let E0 :=
    lineTailLetter H U a trace hend K R Q.index x
  let E :
      OneLevelLetter H
        (U.cut ((firstParameterIndex H R + 1) + Q.index)) := by
    simpa [firstParameterIndex, Nat.add_assoc] using E0
  exact {
    index := Q.index + 1
    state :=
      TraceHistoryState.step H U
        (firstParameterIndex H R + 1)
        Q.index Q.state E
  }


/-- A common-tail step has the expected explicit action. -/
@[simp] theorem step_state_apply
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (R : ProfileReplayState H U a trace hend K)
    (Q : LineTailState H U a trace hend K R)
    (x : LineSymbol (SeenProfile H K))
    (z : T) :
    (step H U a trace hend K R Q x).state z =
      U.rowExtension H
        ((firstParameterIndex H R + 1) + Q.index)
        ((lineTailLetter H U a trace hend K R Q.index x).toMMap
          (Q.state z)) := by
  unfold step
  dsimp only
  exact TraceHistoryState.step_apply H U
    (firstParameterIndex H R + 1)
    Q.index Q.state
    (by
      simpa [firstParameterIndex, Nat.add_assoc] using
        (lineTailLetter H U a trace hend K R Q.index x))
    z

/-- Process the suffix in left-to-right order. -/
noncomputable def word
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (R : ProfileReplayState H U a trace hend K)
    (xs : List (LineSymbol (SeenProfile H K))) :
    LineTailState H U a trace hend K R :=
  xs.foldl
    (fun Q x => step H U a trace hend K R Q x)
    (initial H U a trace hend K R)

private theorem foldl_step_index
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (R : ProfileReplayState H U a trace hend K) :
    ∀ (xs : List (LineSymbol (SeenProfile H K)))
      (Q : LineTailState H U a trace hend K R),
      (xs.foldl
        (fun W x => step H U a trace hend K R W x) Q).index =
        Q.index + xs.length := by
  intro xs
  induction xs with
  | nil =>
      intro Q
      simp
  | cons x xs ih =>
      intro Q
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (step H U a trace hend K R Q x)]
      change Q.index + 1 + xs.length =
        Q.index + (xs.length + 1)
      omega

theorem word_index
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (R : ProfileReplayState H U a trace hend K)
    (xs : List (LineSymbol (SeenProfile H K))) :
    (word H U a trace hend K R xs).index = xs.length := by
  have h :=
    foldl_step_index H U a trace hend K R xs
      (initial H U a trace hend K R)
  simpa [initial] using h

/-- The common second block obtained after the suffix, followed by the next
ambient row. -/
noncomputable def headRow
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (R : ProfileReplayState H U a trace hend K)
    (xs : List (LineSymbol (SeenProfile H K))) :
    AM H (U.cut (firstParameterIndex H R + 1)) 1 := by
  let Q := word H U a trace hend K R xs
  exact TraceHistoryState.headRow H U
    (firstParameterIndex H R + 1) Q.index Q.state

/-- The common second block is geometric in the ambient tail. -/
theorem headRow_stemAt
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (R : ProfileReplayState H U a trace hend K)
    (xs : List (LineSymbol (SeenProfile H K))) :
    FatTree.StemAt H
      (FiniteFatTree.appendRow H
        (U.initialSegment H (firstParameterIndex H R + 1))
        (headRow H U a trace hend K R xs))
      U
      (firstParameterIndex H R + 1 + xs.length + 1) := by
  let Q := word H U a trace hend K R xs
  have hQ := TraceHistoryState.headRow_stemAt H U
    (firstParameterIndex H R + 1) Q.index Q.state
  rw [word_index H U a trace hend K R xs] at hQ
  simpa [headRow, Q, Nat.add_assoc] using hQ

end LineTailState
end ProfileReplayState

end FatTree
end SMTree
end SuccessorTree

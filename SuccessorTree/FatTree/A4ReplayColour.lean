import SuccessorTree.FatTree.A4LineTail

/-!
# Colour stabilization for replayed profile lines

This file states the Hales--Jewett conclusion in the algebraic form used by
the fat-tree A4 proof.  A replay state is closed by the current ambient row,
then composed after each member of the fixed finite trace family.
-/

namespace SuccessorTree
namespace SMTree

universe u v w z

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree
namespace ProfileReplayState

variable (H : SMTree S)

/-- Close a replay state by its current ambient row and compose it after one
fixed trace from the original source cut. -/
noncomputable def colouredComposite
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    {K : ProfileCollector H U a trace}
    (R : ProfileReplayState H U a trace hend K)
    (q : C) :
    AM H c 1 := by
  let qExact : AMExact H c (U.cut a) :=
    ⟨trace q, hend q⟩
  let h :=
    TraceHistoryState.headRow H U a
      R.collector.index R.collector.state
  exact H.composeAcross qExact h

/-- Starred Hales--Jewett simultaneously stabilizes the colours of all
trace composites. -/
theorem exists_colour_stable_replayLine
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    {κ : Type z} [Fintype κ]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (hseen : K.seen.Nonempty)
    (chi : AM H c 1 → κ) :
    ∃ L : StarLine (SeenProfile H K),
      ∀ alpha : SeenProfile H K, ∀ q : C,
        chi (colouredComposite H U a trace hend
          (word H U a trace hend K (L.eval alpha)) q) =
        chi (colouredComposite H U a trace hend
          (word H U a trace hend K L.star) q) := by
  classical
  exact replayWordStarHJ_family H U a trace hend K hseen
    (fun R q => chi (colouredComposite H U a trace hend R q))

/-- The first block attached to the star prefix is geometric and occurs at
the expected ambient depth. -/
theorem starHead_stemAt
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (L : StarLine (SeenProfile H K)) :
    let Rstar := word H U a trace hend K L.star
    StemAt H
      (FiniteFatTree.appendRow H (U.initialSegment H a)
        (TraceHistoryState.headRow H U a
          Rstar.collector.index Rstar.collector.state))
      U (a + Rstar.collector.index + 1) := by
  dsimp only
  exact TraceHistoryState.headRow_stemAt H U a
    (word H U a trace hend K L.star).collector.index
    (word H U a trace hend K L.star).collector.state

end ProfileReplayState
end FatTree
end SMTree
end SuccessorTree

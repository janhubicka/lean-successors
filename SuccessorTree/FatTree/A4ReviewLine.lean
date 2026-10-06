import SuccessorTree.FatTree.A4ReviewFan

/-!
# The review proof's simultaneous geometric fan-line data

Global profile saturation and a nonempty seen alphabet are constructed here,
not passed as hypotheses. Both heads carry their full geometric stem
certificates and agree at the middle cut. The second head is coloured
simultaneously after every admissible canonical image of every raw fan.

At a positive initial cut, M3 supplies the required source letter. At cut
zero a root-moving letter suffices; the root-fixed case is handled separately.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v w z
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- Geometric head and common tail of a simultaneous raw-fan line. The tail
is certified on the entire ambient middle level, not just on trace images. -/
structure ReviewFanLine
    {c : Nat} {C : Type w} {κ : Type z}
    (U : FatTree H) (a : Nat) (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (chi : AM H c 1 → κ) where
  headDepth : Nat
  head : AM H (U.cut a) 1
  head_end : head.rowEndLevel H + 1 = U.cut headDepth
  head_geometric : StemAt H (FiniteFatTree.appendRow H (U.initialSegment H a) head) U headDepth
  tailDepth : Nat
  tail : AM H (U.cut headDepth) 1
  tail_geometric :
    StemAt H (FiniteFatTree.appendRow H (U.initialSegment H headDepth) tail) U tailDepth
  fan_colour :
    ∀ (j : C) (e : RawSuccessorFan H (trace j))
      (theta : AM H c 1) (htheta : theta.rowEndLevel H = U.cut headDepth),
      (∀ (x : InitialNode T c), LevelTree.lev x.1 = c →
        theta.representative H x.1 =
          H.canonicalExtension (head.representative H) (U.cut a) (e.toFun x).1) →
      chi (H.composeAcross (⟨theta, htheta⟩ : AMExact H c (U.cut headDepth)) tail) =
        chi (H.composeAcross (⟨trace j, hend j⟩ : AMExact H c (U.cut a)) head)

/-- The actual middle and terminal depths are strictly increasing. -/
theorem ReviewFanLine.depths_strict
    {c : Nat} {C : Type w} {κ : Type z}
    {U : FatTree H} {a : Nat} {trace : C → AM H c 1}
    {hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a}
    {chi : AM H c 1 → κ}
    (L : ReviewFanLine H U a trace hend chi) :
    a < L.headDepth ∧ L.headDepth < L.tailDepth := by
  have hhead : a < L.headDepth := by
    rcases L.head_geometric.1 with ⟨w⟩
    have h := w.height_le H
    change a + 1 ≤ L.headDepth at h
    omega
  have htail : L.headDepth < L.tailDepth := by
    rcases L.tail_geometric.1 with ⟨w⟩
    have h := w.height_le H
    change L.headDepth + 1 ≤ L.tailDepth at h
    omega
  exact ⟨hhead, htail⟩

/-- The review's simultaneous raw-fan construction from a source letter.
All saturation and Hales--Jewett data are supplied by the tree axioms and
previously proved finite combinatorics. No pigeonhole conclusion is assumed. -/
theorem exists_reviewFanLine_of_sourceLetter
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    {κ : Type z} [Fintype κ]
    (U : FatTree H) (a : Nat) (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (E : OneLevelLetter H (U.cut a)) (chi : AM H c 1 → κ) :
    Nonempty (ReviewFanLine H U a trace hend chi) := by
  classical
  obtain ⟨K, _, hglobal⟩ := ProfileCollector.exists_globallySaturated H U a trace hend
  have hcut : U.cut a ≤ U.cut (a + K.index) :=
    (U.cut_strictMono H).monotone (by omega)
  have hcurrent : Nonempty (OneLevelLetter H (U.cut (a + K.index))) := by
    by_cases heq : U.cut a = U.cut (a + K.index)
    · exact ⟨heq ▸ E⟩
    · exact ⟨duplicateHistoryLetter H (U.cut a) (U.cut (a + K.index))
        (lt_of_le_of_ne hcut heq)⟩
  obtain ⟨Ecurrent⟩ := hcurrent
  have hseen := ProfileCollector.seen_nonempty_of_globallySaturated H U a trace hend K hglobal Ecurrent
  obtain ⟨L, hL⟩ := ProfileReplayState.review_exists_profile_fan_homogeneity H U a trace hend K hglobal hseen chi
  let R := ProfileReplayState.word H U a trace hend K L.star
  let xs := afterFirstParameter L.word
  refine ⟨{
    headDepth := ProfileReplayState.firstParameterIndex H R + 1
    head := ProfileReplayState.reviewLineHead H U a trace hend K L
    head_end := TraceHistoryState.headRow_nextCut H U a R.collector.index R.collector.state
    head_geometric := TraceHistoryState.headRow_stemAt H U a R.collector.index R.collector.state
    tailDepth := ProfileReplayState.firstParameterIndex H R + 1 + xs.length + 1
    tail := ProfileReplayState.reviewLineTail H U a trace hend K L
    tail_geometric := ProfileReplayState.LineTailState.headRow_stemAt H U a trace hend K R xs
    fan_colour := ?_
  }⟩
  intro j e theta htheta hraw
  exact hL j e theta htheta hraw

end SuccessorTree.SMTree.FatTree

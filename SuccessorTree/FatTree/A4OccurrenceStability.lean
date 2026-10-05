import SuccessorTree.FatTree.A4ReplayWord

/-!
# Stability of the recorded occurrences used in A4 replay

Extending a profile history changes its current state, but not the source
level, base map, or letter chosen for an already recorded profile. These
lemmas lift the one-step preservation facts to arbitrary finite histories.
The replay source is therefore fixed by the original collector, not by the
word being replayed. This is needed to identify the constant letters in the
common second block of a Hales--Jewett line.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v w
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)
variable {c : Nat} {C : Type w} [Fintype C]
variable {U : FatTree H} {a : Nat} {trace : C → AM H c 1}
variable (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)

namespace ProfileCollector

variable {K L : ProfileCollector H U a trace}

/-- A finite continuation preserves the source level of every old occurrence. -/
theorem reachable_occurrence_level
    (hKL : ReachableFrom H U a trace hend K L)
    (beta : FanProfile H C trace) (hbeta : beta ∈ K.seen)
    (hbetaL : beta ∈ L.seen) :
    (L.occurrence beta hbetaL).level = (K.occurrence beta hbeta).level := by
  induction hKL with
  | refl => rfl
  | @step P hKP E ih =>
      have hbetaP : beta ∈ P.seen :=
        reachable_seen_mono H U a trace hend hKP hbeta
      exact (advanceAny_occurrence_old_level H U a trace hend P E beta hbetaP).trans
        (ih hbetaP)

/-- The base map of an old occurrence is independent of the continuation. -/
theorem reachable_occurrence_base
    (hKL : ReachableFrom H U a trace hend K L)
    (beta : FanProfile H C trace) (hbeta : beta ∈ K.seen)
    (hbetaL : beta ∈ L.seen) :
    (L.occurrence beta hbetaL).base = (K.occurrence beta hbeta).base := by
  induction hKL with
  | refl => rfl
  | @step P hKP E ih =>
      have hbetaP : beta ∈ P.seen :=
        reachable_seen_mono H U a trace hend hKP hbeta
      exact (advanceAny_occurrence_old_base H U a trace hend P E beta hbetaP).trans
        (ih hbetaP)

/-- The dependent source letter is preserved as well. -/
theorem reachable_occurrence_letter
    (hKL : ReachableFrom H U a trace hend K L)
    (beta : FanProfile H C trace) (hbeta : beta ∈ K.seen)
    (hbetaL : beta ∈ L.seen) :
    HEq (L.occurrence beta hbetaL).letter (K.occurrence beta hbeta).letter := by
  induction hKL with
  | refl => rfl
  | @step P hKP E ih =>
      have hbetaP : beta ∈ P.seen :=
        reachable_seen_mono H U a trace hend hKP hbeta
      exact (advanceAny_occurrence_old_letter H U a trace hend P E beta hbetaP).trans
        (ih hbetaP)

/-- Global saturation fixes the seen alphabet along every finite continuation. -/
theorem seen_eq_of_globallySaturated
    (hglobal : GloballySaturated H U a trace hend K)
    (hKL : ReachableFrom H U a trace hend K L) :
    L.seen = K.seen :=
  Finset.Subset.antisymm (hglobal L hKL)
    (reachable_seen_mono H U a trace hend hKL)

/-- Global saturation is inherited by every reachable collector. -/
theorem globallySaturated_of_reachable
    (hglobal : GloballySaturated H U a trace hend K)
    (hKL : ReachableFrom H U a trace hend K L) :
    GloballySaturated H U a trace hend L := by
  intro M hLM
  exact (hglobal M (reachable_trans H U a trace hend hKL hLM)).trans
    (reachable_seen_mono H U a trace hend hKL)

/-- A profile first examined after any finite continuation already occurs in
the starting alphabet. This is stronger than one-step saturation at K. -/
theorem currentProfile_mem_start
    (hglobal : GloballySaturated H U a trace hend K)
    (hKL : ReachableFrom H U a trace hend K L)
    (E : OneLevelLetter H (U.cut (a + L.index))) :
    currentProfile H U a trace L E ∈ K.seen := by
  apply hglobal (advanceAny H U a trace hend L E)
    (ReachableFrom.step hKL E)
  rw [advanceAny_seen]
  exact Finset.mem_insert_self _ _

end ProfileCollector

namespace ProfileReplayState

variable [Nonempty C] {K : ProfileCollector H U a trace}

/-- The fixed occurrence in the original collector lies below every replay cut. -/
theorem fixed_occurrence_level_lt
    (R : ProfileReplayState H U a trace hend K)
    (alpha : {p : FanProfile H C trace // p ∈ K.seen}) :
    (K.occurrence alpha.1 alpha.2).level < U.cut (a + R.collector.index) := by
  have halpha : alpha.1 ∈ R.collector.seen := by
    rw [R.seen_eq]
    exact alpha.2
  have hlevel := ProfileCollector.reachable_occurrence_level H hend
    R.reachable alpha.1 alpha.2 halpha
  rw [← hlevel]
  exact occurrence_level_lt_current H U a trace hend K R alpha.1 halpha

/-- Every occurrence of a constant profile is replayed from the same original
source level, independently of earlier letters in the word. -/
theorem replayLetter_eq_fixed
    (R : ProfileReplayState H U a trace hend K)
    (alpha : {p : FanProfile H C trace // p ∈ K.seen}) :
    replayLetter H U a trace hend K R alpha =
      duplicateHistoryLetter H (K.occurrence alpha.1 alpha.2).level
        (U.cut (a + R.collector.index))
        (fixed_occurrence_level_lt H hend R alpha) := by
  have halpha : alpha.1 ∈ R.collector.seen := by
    rw [R.seen_eq]
    exact alpha.2
  have hlevel := ProfileCollector.reachable_occurrence_level H hend
    R.reachable alpha.1 alpha.2 halpha
  unfold replayLetter
  dsimp only
  congr 1 <;> exact hlevel

end ProfileReplayState
end SuccessorTree.SMTree.FatTree

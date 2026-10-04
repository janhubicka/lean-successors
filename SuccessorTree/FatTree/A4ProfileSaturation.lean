import SuccessorTree.FatTree.A4ProfileReplay
import Mathlib.Data.Finset.Card

/-!
# Maximal finite successor-profile histories

For a fixed finite family of one-moving traces, a collector stores a current
fat-tree history state and one witnessed occurrence of every profile already
seen.  Occurrences are transported forward when the history is extended.
Since the profile type is finite, repeatedly adjoining a genuinely new
profile must terminate.  The resulting collector is saturated: every possible
next history letter has a profile already witnessed earlier.

This is the finite maximal-history step in the manuscript's all-trace A4
argument.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- A witnessed occurrence of one complete fan profile, recorded relative to
a current history state.  The occurrence endpoint is required to lie below
the current state on every trace coordinate, which is exactly what later M3
replay needs. -/
structure ProfileOccurrence
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    {i : Nat}
    (P : TraceHistoryState H U a i)
    (alpha : FanProfile H C trace) where
  level : Nat
  base : MMap H
  letter : OneLevelLetter H level
  base_top :
    ∀ j : C,
      H.levelMap base.map ((trace j).rowEndLevel H) = level
  profile_eq :
    historyFanProfile H trace base letter = alpha
  endpoint_below :
    ∀ (j : C) (x : InitialNode T c)
      (hx : LevelTree.lev x.1 = c),
        letter.toMMap (base ((trace j).representative H x.1)) ≤
          P ((trace j).representative H x.1)

namespace ProfileOccurrence

/-- The endpoint of a trace in a family whose common terminal level is the
history source cut lies on that cut. -/
theorem trace_endpoint_level
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (j : C) (x : InitialNode T c)
    (hx : LevelTree.lev x.1 = c) :
    LevelTree.lev ((trace j).representative H x.1) = U.cut a := by
  calc
    LevelTree.lev ((trace j).representative H x.1) =
        H.levelMap ((trace j).representative H).map
          (LevelTree.lev x.1) :=
      (H.levelMap_eq ((trace j).representative H).map (a := x.1)).symm
    _ = H.levelMap ((trace j).representative H).map c := by rw [hx]
    _ = (trace j).rowEndLevel H := rfl
    _ = U.cut a := hend j

/-- An already recorded profile occurrence remains valid after one more
history step. -/
noncomputable def advance
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    {i : Nat}
    (P : TraceHistoryState H U a i)
    {alpha : FanProfile H C trace}
    (occ : ProfileOccurrence H U a trace P alpha)
    (E : OneLevelLetter H (U.cut (a + i))) :
    ProfileOccurrence H U a trace
      (TraceHistoryState.step H U a i P E) alpha where
  level := occ.level
  base := occ.base
  letter := occ.letter
  base_top := occ.base_top
  profile_eq := occ.profile_eq
  endpoint_below := by
    intro j x hx
    have hqlev :
        LevelTree.lev ((trace j).representative H x.1) = U.cut a :=
      trace_endpoint_level H U a trace hend j x hx
    exact (occ.endpoint_below j x hx).trans
      (P.le_step H U a i E hqlev)

/-- The current step itself yields a new witnessed profile occurrence after
transport through the ambient row. -/
noncomputable def current
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    {i : Nat}
    (P : TraceHistoryState H U a i)
    (E : OneLevelLetter H (U.cut (a + i))) :
    ProfileOccurrence H U a trace
      (TraceHistoryState.step H U a i P E)
      (historyFanProfile H trace P.toMMap E) := by
  let r : Nat := a + i
  let R : MMap H := U.rowExtension H r
  refine {
    level := (U.row r).rowEndLevel H
    base := rowTransportBase H U r P.toMMap
    letter := rowTransportLetter H U r E
    base_top := ?_
    profile_eq := ?_
    endpoint_below := ?_
  }
  · intro j
    change
      H.levelMap
          (MMap.comp H (U.rowExtension H r) P.toMMap).map
          ((trace j).rowEndLevel H) =
        (U.row r).rowEndLevel H
    rw [H.levelMap_comp]
    rw [hend j, P.topLevel]
    change
      H.levelMap (U.rowExtension H r).map (U.cut r) =
        (U.row r).rowEndLevel H
    exact U.rowExtension_level_at_cut H r
  · funext j
    have hPtop :
        H.levelMap P.toMMap.map ((trace j).rowEndLevel H) =
          U.cut r := by
      rw [hend j, P.topLevel]
    exact historyProfile_rowTransport H U r (trace j) P.toMMap E hPtop
  · intro j x hx
    have hqlev :
        LevelTree.lev ((trace j).representative H x.1) ≤ U.cut r := by
      have hbase :
          LevelTree.lev ((trace j).representative H x.1) = U.cut a :=
        trace_endpoint_level H U a trace hend j x hx
      rw [hbase]
      exact (U.cut_strictMono H).monotone (by
        dsimp [r]
        omega)
    have hcomm :=
      rowTransportLetter_commutes H U r E
        (P ((trace j).representative H x.1))
        (by
          have hPlev :
              LevelTree.lev (P ((trace j).representative H x.1)) =
                U.cut r := by
            exact P.level_apply H U a i
              (trace_endpoint_level H U a trace hend j x hx)
          exact Nat.le_of_eq hPlev)
    change
      (rowTransportLetter H U r E).toMMap
          ((rowTransportBase H U r P.toMMap)
            ((trace j).representative H x.1)) ≤
        (TraceHistoryState.step H U a i P E)
          ((trace j).representative H x.1)
    change
      (rowTransportLetter H U r E).toMMap
          (U.rowExtension H r
            (P ((trace j).representative H x.1))) ≤
        U.rowExtension H r
          (E.toMMap (P ((trace j).representative H x.1)))
    rw [hcomm]

end ProfileOccurrence

/-- A current history together with a finite set of already witnessed
profiles. -/
structure ProfileCollector
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1) where
  index : Nat
  state : TraceHistoryState H U a index
  seen : Finset (FanProfile H C trace)
  occurrence :
    ∀ alpha : FanProfile H C trace, alpha ∈ seen →
      ProfileOccurrence H U a trace state alpha

namespace ProfileCollector

/-- Empty collector at the identity history. -/
noncomputable def initial
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1) :
    ProfileCollector H U a trace where
  index := 0
  state := TraceHistoryState.initial H U a
  seen := ∅
  occurrence := by
    intro alpha h
    simp at h

/-- The profile of one possible next history letter. -/
noncomputable def currentProfile
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (K : ProfileCollector H U a trace)
    (E : OneLevelLetter H (U.cut (a + K.index))) :
    FanProfile H C trace :=
  historyFanProfile H trace K.state.toMMap E

/-- A collector is saturated when no next history letter introduces a new
profile. -/
def Saturated
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (K : ProfileCollector H U a trace) : Prop :=
  ∀ E : OneLevelLetter H (U.cut (a + K.index)),
    currentProfile H U a trace K E ∈ K.seen

/-- Adjoin one genuinely new profile and advance the history by that step. -/
noncomputable def advance
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (E : OneLevelLetter H (U.cut (a + K.index)))
    (hnew : currentProfile H U a trace K E ∉ K.seen) :
    ProfileCollector H U a trace := by
  classical
  let alpha := currentProfile H U a trace K E
  let Pnext :=
    TraceHistoryState.step H U a K.index K.state E
  refine {
    index := K.index + 1
    state := Pnext
    seen := insert alpha K.seen
    occurrence := ?_
  }
  intro beta hbeta
  by_cases hEq : beta = alpha
  · subst beta
    exact ProfileOccurrence.current H U a trace hend K.state E
  · have hOld : beta ∈ K.seen := by
      simpa [hEq] using hbeta
    exact ProfileOccurrence.advance H U a trace hend
      K.state (K.occurrence beta hOld) E

@[simp] theorem advance_seen
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (E : OneLevelLetter H (U.cut (a + K.index)))
    (hnew : currentProfile H U a trace K E ∉ K.seen) :
    (advance H U a trace hend K E hnew).seen =
      insert (currentProfile H U a trace K E) K.seen := by
  rfl

/-- The number of profiles not yet witnessed by a collector. -/
noncomputable def missingCount
    {c : Nat} {C : Type w} [Fintype C]
    (trace : C → AM H c 1)
    (K : ProfileCollector H U a trace) : Nat := by
  classical
  letI : Fintype (FanProfile H C trace) :=
    fanProfileFintype H trace
  exact (Finset.univ \ K.seen).card

/-- Adding a genuinely new profile strictly decreases the number of missing
profiles. -/
theorem missingCount_advance_lt
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (E : OneLevelLetter H (U.cut (a + K.index)))
    (hnew : currentProfile H U a trace K E ∉ K.seen) :
    missingCount H trace (advance H U a trace hend K E hnew) <
      missingCount H trace K := by
  classical
  letI : Fintype (FanProfile H C trace) :=
    fanProfileFintype H trace
  let alpha := currentProfile H U a trace K E
  have halpha :
      alpha ∈ (Finset.univ \ K.seen :
        Finset (FanProfile H C trace)) := by
    simp [alpha, hnew]
  unfold missingCount
  rw [advance_seen]
  have hdiff :
      (Finset.univ \ insert alpha K.seen :
        Finset (FanProfile H C trace)) =
        (Finset.univ \ K.seen).erase alpha := by
    ext beta
    simp [and_assoc, and_left_comm, and_comm]
  rw [hdiff]
  exact Finset.card_erase_lt_of_mem halpha

/-- Every finite trace family has a saturated history collector. -/
theorem exists_saturated
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a) :
    ∃ K : ProfileCollector H U a trace,
      Saturated H U a trace K := by
  classical
  let start := initial H U a trace
  let measure (K : ProfileCollector H U a trace) : Nat :=
    missingCount H trace K
  have main :
      ∀ N : Nat,
        ∀ K : ProfileCollector H U a trace,
          measure K = N →
            ∃ L : ProfileCollector H U a trace,
              Saturated H U a trace L := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro K hKN
        by_cases hsat : Saturated H U a trace K
        · exact ⟨K, hsat⟩
        · have hex :
            ∃ E : OneLevelLetter H (U.cut (a + K.index)),
              currentProfile H U a trace K E ∉ K.seen := by
            simpa [Saturated] using hsat
          rcases hex with ⟨E, hE⟩
          let K' := advance H U a trace hend K E hE
          have hlt : measure K' < N := by
            rw [← hKN]
            exact missingCount_advance_lt H U a trace hend K E hE
          exact ih (measure K') hlt K' rfl
  exact main (measure start) start rfl


/-- Advance by an arbitrary next letter, recording its profile whether or not
it has been seen before.  This is the transition used for finite-extension
reachability. -/
noncomputable def advanceAny
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (E : OneLevelLetter H (U.cut (a + K.index))) :
    ProfileCollector H U a trace := by
  classical
  let alpha := currentProfile H U a trace K E
  let Pnext :=
    TraceHistoryState.step H U a K.index K.state E
  refine {
    index := K.index + 1
    state := Pnext
    seen := insert alpha K.seen
    occurrence := ?_
  }
  intro beta hbeta
  by_cases hEq : beta = alpha
  · subst beta
    exact ProfileOccurrence.current H U a trace hend K.state E
  · have hOld : beta ∈ K.seen := by
      simpa [hEq] using hbeta
    exact ProfileOccurrence.advance H U a trace hend
      K.state (K.occurrence beta hOld) E

@[simp] theorem advanceAny_seen
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (E : OneLevelLetter H (U.cut (a + K.index))) :
    (advanceAny H U a trace hend K E).seen =
      insert (currentProfile H U a trace K E) K.seen := by
  rfl

/-- Finite history extension between collectors. -/
inductive ReachableFrom
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K₀ : ProfileCollector H U a trace) :
    ProfileCollector H U a trace → Prop
  | refl :
      ReachableFrom U a trace hend K₀ K₀
  | step {K : ProfileCollector H U a trace} :
      ReachableFrom U a trace hend K₀ K →
      (E : OneLevelLetter H (U.cut (a + K.index))) →
      ReachableFrom U a trace hend K₀
        (advanceAny H U a trace hend K E)

theorem reachable_trans
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    {K L M : ProfileCollector H U a trace}
    (hKL : ReachableFrom H U a trace hend K L)
    (hLM : ReachableFrom H U a trace hend L M) :
    ReachableFrom H U a trace hend K M := by
  induction hLM with
  | refl => exact hKL
  | @step P hLP E ih =>
      exact ReachableFrom.step ih E

/-- Seen profiles only increase along a finite extension. -/
theorem reachable_seen_mono
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    {K L : ProfileCollector H U a trace}
    (hKL : ReachableFrom H U a trace hend K L) :
    K.seen ⊆ L.seen := by
  induction hKL with
  | refl =>
      exact fun _ h => h
  | @step P hKP E ih =>
      intro alpha halpha
      rw [advanceAny_seen]
      exact Finset.mem_insert_of_mem (ih halpha)

/-- If a finite extension has acquired some profile outside the starting
collector, there is a first step where this happens.  Before that step the
seen set is still contained in the starting one. -/
theorem reachable_first_new
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    {K L : ProfileCollector H U a trace}
    (hKL : ReachableFrom H U a trace hend K L)
    (hnew : ¬ L.seen ⊆ K.seen) :
    ∃ (P : ProfileCollector H U a trace)
      (E : OneLevelLetter H (U.cut (a + P.index))),
        ReachableFrom H U a trace hend K P ∧
        P.seen ⊆ K.seen ∧
        currentProfile H U a trace P E ∉ K.seen := by
  induction hKL with
  | refl =>
      exfalso
      exact hnew (fun _ h => h)
  | @step P hKP E ih =>
      by_cases hPsub : P.seen ⊆ K.seen
      · refine ⟨P, E, hKP, hPsub, ?_⟩
        intro hprof
        apply hnew
        intro alpha halpha
        rw [advanceAny_seen] at halpha
        rcases Finset.mem_insert.mp halpha with hEq | hOld
        · simpa [hEq] using hprof
        · exact hPsub hOld
      · exact ih hPsub

/-- Inserting a genuinely new profile with \`advanceAny\` strictly lowers the
finite missing-profile count. -/
theorem missingCount_advanceAny_lt
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (E : OneLevelLetter H (U.cut (a + K.index)))
    (hnew : currentProfile H U a trace K E ∉ K.seen) :
    missingCount H trace (advanceAny H U a trace hend K E) <
      missingCount H trace K := by
  classical
  letI : Fintype (FanProfile H C trace) :=
    fanProfileFintype H trace
  let alpha := currentProfile H U a trace K E
  have halpha :
      alpha ∈ (Finset.univ \ K.seen :
        Finset (FanProfile H C trace)) := by
    simp [alpha, hnew]
  unfold missingCount
  rw [advanceAny_seen]
  have hdiff :
      (Finset.univ \ insert alpha K.seen :
        Finset (FanProfile H C trace)) =
        (Finset.univ \ K.seen).erase alpha := by
    ext beta
    simp [and_assoc, and_left_comm, and_comm]
  rw [hdiff]
  exact Finset.card_erase_lt_of_mem halpha

/-- Manuscript-strength saturation: no finite history extension can introduce
a profile which has not already been witnessed. -/
def GloballySaturated
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace) : Prop :=
  ∀ L : ProfileCollector H U a trace,
    ReachableFrom H U a trace hend K L →
      L.seen ⊆ K.seen

/-- Every collector has a finite extension which is globally saturated.
The induction measure is the number of profiles not yet seen. -/
theorem exists_globallySaturated_from
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K₀ : ProfileCollector H U a trace) :
    ∃ K : ProfileCollector H U a trace,
      ReachableFrom H U a trace hend K₀ K ∧
      GloballySaturated H U a trace hend K := by
  classical
  let measure (K : ProfileCollector H U a trace) : Nat :=
    missingCount H trace K
  have main :
      ∀ N : Nat,
        ∀ K : ProfileCollector H U a trace,
          measure K = N →
            ∃ L : ProfileCollector H U a trace,
              ReachableFrom H U a trace hend K L ∧
              GloballySaturated H U a trace hend L := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro K hKN
        by_cases hglobal :
            GloballySaturated H U a trace hend K
        · exact ⟨K, ReachableFrom.refl, hglobal⟩
        · unfold GloballySaturated at hglobal
          push_neg at hglobal
          rcases hglobal with ⟨M, hKM, hMnew⟩
          rcases reachable_first_new H U a trace hend hKM hMnew with
            ⟨P, E, hKP, hPsub, hEnewK⟩
          have hKsubP : K.seen ⊆ P.seen :=
            reachable_seen_mono H U a trace hend hKP
          have hseenEq : P.seen = K.seen :=
            Finset.Subset.antisymm hPsub hKsubP
          have hEnewP :
              currentProfile H U a trace P E ∉ P.seen := by
            simpa [hseenEq] using hEnewK
          let P' := advanceAny H U a trace hend P E
          have hPP' :
              ReachableFrom H U a trace hend P P' := by
            exact ReachableFrom.step ReachableFrom.refl E
          have hKP' :
              ReachableFrom H U a trace hend K P' :=
            reachable_trans H U a trace hend hKP hPP'
          have hmeasureEq : measure P = measure K := by
            unfold measure
            unfold missingCount
            rw [hseenEq]
          have hlt : measure P' < N := by
            have hstep :=
              missingCount_advanceAny_lt
                H U a trace hend P E hEnewP
            rw [hmeasureEq, hKN] at hstep
            exact hstep
          rcases ih (measure P') hlt P' rfl with
            ⟨L, hP'L, hLsat⟩
          exact ⟨L,
            reachable_trans H U a trace hend hKP' hP'L,
            hLsat⟩
  exact main (measure K₀) K₀ rfl

/-- In particular there is a globally maximal finite profile history starting
from the identity history. -/
theorem exists_globallySaturated
    {c : Nat} {C : Type w} [Fintype C]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a) :
    ∃ K : ProfileCollector H U a trace,
      ReachableFrom H U a trace hend
        (initial H U a trace) K ∧
      GloballySaturated H U a trace hend K :=
  exists_globallySaturated_from H U a trace hend
    (initial H U a trace)

end ProfileCollector

end FatTree
end SMTree
end SuccessorTree

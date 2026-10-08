import SuccessorTree.EnvelopeEmbeddingType
import SuccessorTree.EnvelopeGlobalMinimality
import SuccessorTree.EnvelopeLevelSets
import Mathlib.Tactic

/-!
# Proposition-level envelope runs

This packages the local Section 5 lemmas into the decreasing run used by the
manuscript's envelope algorithm. A run records only the choices made by the
algorithm. Level selection and forced levels of competitors use the run alone;
coverage of the output and independence of embedding type additionally use E1.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

/-- Descending induction on the finite stage interval. This is only natural-number
bookkeeping; it carries no tree or envelope hypotheses. -/
private theorem induction_down {ell : Nat} {P : Nat → Prop}
    (htop : P ell)
    (hstep : ∀ i, i < ell → P (i + 1) → P i) :
    ∀ i, i ≤ ell → P i := by
  have main : ∀ d : Nat, ∀ i, ell - i = d → i ≤ ell → P i := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i hdi hiell
        by_cases hieq : i = ell
        · simpa [hieq] using htop
        · have hilt : i < ell := lt_of_le_of_ne hiell hieq
          apply hstep i hilt
          apply ih (ell - (i + 1)) (by omega) (i + 1) rfl (by omega)
  intro i hiell
  exact main (ell - i) i rfl hiell

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- A complete decreasing run of Algorithm 5.4 through levels ell-1,...,0. -/
structure AlgorithmRun (H : SMTree S) (X : Set T) (ell : Nat) where
  I : Nat → Set Nat
  F : Nat → MMap H
  topI : I ell = {ell}
  topF : F ell = MMap.id H
  interesting_step :
    ∀ (i : Nat), i < ell →
      IsInterestingAt H (closure S (I (i + 1)) X) i →
      I i = insert i (I (i + 1)) ∧ F i = F (i + 1)
  noninteresting_step :
    ∀ (i : Nat), i < ell →
      ¬ IsInterestingAt H (closure S (I (i + 1)) X) i →
      ∃ D : MMap H,
        D.map.SkipsOnly i ∧
        (∀ ⦃c : T⦄, c ∈ closure S (I (i + 1)) X →
          ∀ (hic : i < LevelTree.lev c),
            D (LevelTree.ancestor c i (Nat.le_of_lt hic)) =
              LevelTree.ancestor c (i + 1) (Nat.succ_le_iff.mpr hic)) ∧
        I i = I (i + 1) ∧
        F i = MMap.comp H (F (i + 1)) D

namespace AlgorithmRun

variable {H : SMTree S} {X : Set T} {ell : Nat}

/-- Every recorded run satisfies the strengthened invariant of Lemma 5.8. -/
theorem fullInvariant
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell) :
    ∀ (i : Nat), i ≤ ell →
      StageFullInvariant H X ell i (R.I i) (R.F i) := by
  apply induction_down
  · rw [R.topI, R.topF]
    exact stageFullInvariant_base H X ell
  · intro i hilt hnext
    by_cases hinter :
        IsInterestingAt H (closure S (R.I (i + 1)) X) i
    · rcases R.interesting_step i hilt hinter with ⟨hI, hF⟩
      rw [hI, hF]
      exact stageFullInvariant_interesting
        H X ell i (R.I (i + 1)) (R.F (i + 1)) hilt hnext
    · rcases R.noninteresting_step i hilt hinter with
        ⟨D, hDskip, hDcross, hI, hF⟩
      have hno :
          ∀ ⦃x : T⦄,
            x ∈ closure S (R.I (i + 1)) X →
            LevelTree.lev x ≠ i := by
        intro x hx hxi
        exact hinter (Or.inl ⟨x, hx, hxi⟩)
      rw [hI, hF]
      exact stageFullInvariant_noninteresting
        H hE1 X ell i hXbound (R.I (i + 1))
        (R.F (i + 1)) D hilt hnext hDskip hno hDcross

/-- The level-set part of either algorithm branch. No E1 is needed. -/
theorem level_step (R : AlgorithmRun H X ell) (i : Nat) (hi : i < ell) :
    R.I i = R.I (i + 1) ∨ R.I i = insert i (R.I (i + 1)) := by
  by_cases hinter : IsInterestingAt H (closure S (R.I (i + 1)) X) i
  · exact Or.inr (R.interesting_step i hi hinter).1
  · obtain ⟨D, hskip, hcross, hI, hF⟩ := R.noninteresting_step i hi hinter
    exact Or.inl hI

/-- Bounds on selected levels follow from the recursion, not map coverage. -/
theorem I_mem_bounds (R : AlgorithmRun H X ell) :
    ∀ i, i ≤ ell → ∀ q ∈ R.I i, i ≤ q ∧ q ≤ ell :=
  levelSets_mem_bounds R.I ell R.topI R.level_step

/-- The one-stage level-set identity without E1 or a bound on X. -/
theorem nextI_eq_of_run (R : AlgorithmRun H X ell) (i : Nat) (hi : i < ell) :
    R.I (i + 1) = {q | q ∈ R.I i ∧ i < q} :=
  levelSets_next_eq R.I ell R.topI R.level_step i hi

/-- The final-tail identity without E1 or a bound on X. -/
theorem I_eq_final_tail_of_run (R : AlgorithmRun H X ell) :
    ∀ i, i ≤ ell → R.I i = {q | q ∈ R.I 0 ∧ i ≤ q} :=
  levelSets_eq_final_tail R.I ell R.topI R.level_step

/-- The next stage consists of final selected levels strictly above i. -/
theorem I_succ_eq_higher_final_of_run
    (R : AlgorithmRun H X ell) (i : Nat) (hi : i < ell) :
    R.I (i + 1) = higherLevels (R.I 0) i := by
  rw [R.I_eq_final_tail_of_run (i + 1) (by omega)]
  ext q
  simp only [Set.mem_setOf_eq, higherLevels]
  constructor
  · rintro ⟨hq, hiq⟩
    exact ⟨hq, by omega⟩
  · rintro ⟨hq, hiq⟩
    exact ⟨hq, by omega⟩

/-- Compatibility interface; the two hypotheses are no longer needed. -/
theorem nextI_eq
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    (i : Nat) (hilt : i < ell) :
    R.I (i + 1) = {q | q ∈ R.I i ∧ i < q} := by
  clear hE1 hXbound
  exact R.nextI_eq_of_run i hilt

/-- Compatibility interface for the final-tail identity. -/
theorem I_eq_final_tail
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell) :
    ∀ (i : Nat), i ≤ ell →
      R.I i = {q | q ∈ R.I 0 ∧ i ≤ q} := by
  clear hE1 hXbound
  exact R.I_eq_final_tail_of_run

/-- Compatibility interface for the next-stage final-tail identity. -/
theorem I_succ_eq_higher_final
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    (i : Nat) (hilt : i < ell) :
    R.I (i + 1) = higherLevels (R.I 0) i := by
  clear hE1 hXbound
  exact R.I_succ_eq_higher_final_of_run i hilt

/-- Every selected level is interesting relative to the selected levels above
it. This is a property of the decisions, independent of E1 and output coverage. -/
theorem finalLevel_interesting_of_run
    (R : AlgorithmRun H X ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell) :
    ∀ ⦃i : Nat⦄, i ∈ R.I 0 →
      IsInterestingAt H (closure S (higherLevels (R.I 0) i) X) i := by
  intro i hiI
  have hiell : i ≤ ell := (R.I_mem_bounds 0 (Nat.zero_le ell) i hiI).2
  by_cases hieq : i = ell
  · subst i
    obtain ⟨x, hx, hxlev⟩ := hTop
    exact Or.inl ⟨x, subset_closure S (higherLevels (R.I 0) ell) X hx, hxlev⟩
  · have hilt : i < ell := by omega
    have hiStage : i ∈ R.I i := by
      rw [R.I_eq_final_tail_of_run i hiell]
      exact ⟨hiI, le_rfl⟩
    have hiNotNext : i ∉ R.I (i + 1) := by
      intro hmem
      have hb := R.I_mem_bounds (i + 1) (by omega) i hmem
      omega
    have hinter : IsInterestingAt H (closure S (R.I (i + 1)) X) i := by
      by_contra hnot
      obtain ⟨D, hskip, hcross, hI, hF⟩ := R.noninteresting_step i hilt hnot
      exact hiNotNext (hI ▸ hiStage)
    rw [R.I_succ_eq_higher_final_of_run i hilt] at hinter
    exact hinter

/-- Every selected level is forced in every competing prefix envelope.
Unlike correctness of the output map, this implication does not require E1
or a bound on X. The underlying SMTree hypotheses are unchanged. -/
theorem finalLevels_subset_competitor_of_run
    (R : AlgorithmRun H X ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell)
    (E : MMap H) (m : Nat)
    (hEnvelope : IsPrefixEnvelope E.map m X) :
    ∀ ⦃i : Nat⦄, i ∈ R.I 0 → RepresentedBefore H E.map m i := by
  apply algorithmLevels_subset_competitor H X ell m (R.I 0) E hTop
  · intro i hi
    exact (R.I_mem_bounds 0 (Nat.zero_le ell) i hi).2
  · exact hEnvelope
  · exact R.finalLevel_interesting_of_run hTop

/-- Compatibility interface for the selected-level decisions. -/
theorem finalLevel_interesting
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell) :
    ∀ ⦃i : Nat⦄, i ∈ R.I 0 →
      IsInterestingAt H (closure S (higherLevels (R.I 0) i) X) i := by
  clear hE1 hXbound
  exact R.finalLevel_interesting_of_run hTop

/-- Compatibility interface for forced levels of competing envelopes. -/
theorem finalLevels_subset_competitor
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell)
    (E : MMap H) (m : Nat)
    (hEnvelope : IsPrefixEnvelope E.map m X) :
    ∀ ⦃i : Nat⦄, i ∈ R.I 0 →
      RepresentedBefore H E.map m i := by
  clear hE1 hXbound
  exact R.finalLevels_subset_competitor_of_run hTop E m hEnvelope

/-- The final level sets of any two runs coincide. -/
theorem I_eq
    (R R' : AlgorithmRun H X ell) :
    ∀ (i : Nat), i ≤ ell → R.I i = R'.I i := by
  apply induction_down
  · rw [R.topI, R'.topI]
  · intro i hilt hnext
    by_cases hinter :
        IsInterestingAt H (closure S (R.I (i + 1)) X) i
    · have hinter' :
          IsInterestingAt H (closure S (R'.I (i + 1)) X) i := by
        simpa [← hnext] using hinter
      have hR := (R.interesting_step i hilt hinter).1
      have hR' := (R'.interesting_step i hilt hinter').1
      rw [hR, hR', hnext]
    · have hinter' :
          ¬ IsInterestingAt H (closure S (R'.I (i + 1)) X) i := by
        simpa [← hnext] using hinter
      rcases R.noninteresting_step i hilt hinter with
        ⟨D, hDskip, hDcross, hR, hRF⟩
      rcases R'.noninteresting_step i hilt hinter' with
        ⟨E, hEskip, hEcross, hR', hR'F⟩
      rw [hR, hR', hnext]

/-- The embedding type of X is independent of every one-level choice made in
the run. -/
theorem embeddingType_eq
    (R R' : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell) :
    ∀ (i : Nat), i ≤ ell →
      (R.F i).map ⁻¹' X = (R'.F i).map ⁻¹' X := by
  apply induction_down
  · rw [R.topF, R'.topF]
  · intro i hilt htypeNext
    have hIeq : R.I (i + 1) = R'.I (i + 1) :=
      R.I_eq R' (i + 1) (by omega)
    have hInvR :=
      R.fullInvariant hE1 hXbound (i + 1) (by omega)
    have hInvR'0 :=
      R'.fullInvariant hE1 hXbound (i + 1) (by omega)
    have hInvR' :
        StageInvariant H X ell (i + 1)
          (R.I (i + 1)) (R'.F (i + 1)) := by
      have := hInvR'0.1
      rw [← hIeq] at this
      exact this
    by_cases hinter :
        IsInterestingAt H (closure S (R.I (i + 1)) X) i
    · have hinter' :
          IsInterestingAt H (closure S (R'.I (i + 1)) X) i := by
        simpa [← hIeq] using hinter
      have hRF := (R.interesting_step i hilt hinter).2
      have hR'F := (R'.interesting_step i hilt hinter').2
      rw [hRF, hR'F]
      exact htypeNext
    · have hinter' :
          ¬ IsInterestingAt H (closure S (R'.I (i + 1)) X) i := by
        simpa [← hIeq] using hinter
      rcases R.noninteresting_step i hilt hinter with
        ⟨D, hDskip, hDcross, hRI, hRF⟩
      rcases R'.noninteresting_step i hilt hinter' with
        ⟨E, hEskip, hEcross0, hR'I, hR'F⟩
      have hEcross :
          ∀ ⦃c : T⦄, c ∈ closure S (R.I (i + 1)) X →
            ∀ (hic : i < LevelTree.lev c),
              E (LevelTree.ancestor c i (Nat.le_of_lt hic)) =
                LevelTree.ancestor c (i + 1)
                  (Nat.succ_le_iff.mpr hic) := by
        intro c hc hic
        apply hEcross0
        · rw [← hIeq]
          exact hc
        · exact hic
      have hno :
          ∀ ⦃x : T⦄,
            x ∈ closure S (R.I (i + 1)) X →
            LevelTree.lev x ≠ i := by
        intro x hx hxi
        exact hinter (Or.inl ⟨x, hx, hxi⟩)
      rw [hRF, hR'F]
      exact embeddingType_noninteresting_choice_independent
        H hE1 X ell i hXbound (R.I (i + 1))
        (R.F (i + 1)) (R'.F (i + 1)) D E
        hInvR.1 hInvR' htypeNext hDskip hEskip hno
        hDcross hEcross

end AlgorithmRun

end Envelope
end SMTree
end SuccessorTree

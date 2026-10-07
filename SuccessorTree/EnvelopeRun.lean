import SuccessorTree.EnvelopeEmbeddingType
import SuccessorTree.EnvelopeGlobalMinimality
import Mathlib.Tactic

/-!
# Proposition-level envelope runs

This packages the local Section 5 lemmas into the decreasing run used by the
manuscript's envelope algorithm.  A run records only the choices made by the
algorithm; the theorems below prove the invariant, global minimality of the
selected levels, and independence of the embedding type.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

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

/-- Every recorded run satisfies the strengthened invariant of Lemma 5.8. -/
theorem fullInvariant
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell) :
    ∀ (i : Nat), i ≤ ell →
      StageFullInvariant H X ell i (R.I i) (R.F i) := by
  have main :
      ∀ d : Nat, ∀ i : Nat, ell - i = d → i ≤ ell →
        StageFullInvariant H X ell i (R.I i) (R.F i) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i hdi hiell
        by_cases hieq : i = ell
        · subst i
          rw [R.topI, R.topF]
          exact stageFullInvariant_base H X ell
        · have hilt : i < ell := lt_of_le_of_ne hiell hieq
          have hsmall : ell - (i + 1) < d := by
            rw [← hdi]
            omega
          have hnext :
              StageFullInvariant H X ell (i + 1)
                (R.I (i + 1)) (R.F (i + 1)) :=
            ih (ell - (i + 1)) hsmall (i + 1) rfl (by omega)
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
  intro i hiell
  exact main (ell - i) i rfl hiell

/-- At stage i+1 the retained levels are exactly the retained stage-i levels
strictly above i. -/
theorem nextI_eq
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    (i : Nat) (hilt : i < ell) :
    R.I (i + 1) = {q | q ∈ R.I i ∧ i < q} := by
  have hnext :=
    R.fullInvariant hE1 hXbound (i + 1) (by omega)
  have hgt :
      ∀ ⦃q : Nat⦄, q ∈ R.I (i + 1) → i < q := by
    intro q hq
    have hrep : q ∈ representedLevels (R.F (i + 1)).map (i + 1) ell := by
      rw [← hnext.1.2.2]
      exact hq
    omega
  by_cases hinter :
      IsInterestingAt H (closure S (R.I (i + 1)) X) i
  · rcases R.interesting_step i hilt hinter with ⟨hI, _⟩
    ext q
    constructor
    · intro hq
      exact ⟨by rw [hI]; exact Set.mem_insert_of_mem i hq, hgt hq⟩
    · rintro ⟨hq, hiq⟩
      rw [hI] at hq
      rcases hq with hqi | hq
      · subst q
        omega
      · exact hq
  · rcases R.noninteresting_step i hilt hinter with
      ⟨D, hDskip, hDcross, hI, hF⟩
    ext q
    constructor
    · intro hq
      exact ⟨by rw [hI]; exact hq, hgt hq⟩
    · rintro ⟨hq, _⟩
      rw [hI] at hq
      exact hq

/-- Stage i contains precisely the final selected levels at least i. -/
theorem I_eq_final_tail
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell) :
    ∀ (i : Nat), i ≤ ell →
      R.I i = {q | q ∈ R.I 0 ∧ i ≤ q} := by
  intro i
  induction i with
  | zero =>
      intro _
      ext q
      simp
  | succ i ih =>
      intro hisucc
      have hiell : i < ell := by omega
      have hnext := R.nextI_eq hE1 hXbound i hiell
      have hprev := ih (by omega)
      ext q
      have hn := Set.ext_iff.mp hnext q
      have hp := Set.ext_iff.mp hprev q
      constructor
      · intro hq
        have hpair := hn.mp hq
        have hfinal := hp.mp hpair.1
        exact ⟨hfinal.1, by omega⟩
      · intro hq
        apply hn.mpr
        refine ⟨?_, by omega⟩
        apply hp.mpr
        exact ⟨hq.1, by omega⟩

/-- The next-stage level set is the final set of selected levels above i. -/
theorem I_succ_eq_higher_final
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    (i : Nat) (hilt : i < ell) :
    R.I (i + 1) = higherLevels (R.I 0) i := by
  have htail := R.I_eq_final_tail hE1 hXbound (i + 1) (by omega)
  rw [htail]
  ext q
  simp only [Set.mem_setOf_eq, higherLevels]
  constructor
  · rintro ⟨hq, hiq⟩
    exact ⟨hq, by omega⟩
  · rintro ⟨hq, hiq⟩
    exact ⟨hq, by omega⟩

/-- Every final selected level is interesting relative to the final selected
levels above it. -/
theorem finalLevel_interesting
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell) :
    ∀ ⦃i : Nat⦄, i ∈ R.I 0 →
      IsInterestingAt H (closure S (higherLevels (R.I 0) i) X) i := by
  intro i hiI
  have hfinal := R.fullInvariant hE1 hXbound 0 (Nat.zero_le ell)
  have hiell : i ≤ ell := by
    have hrep : i ∈ representedLevels (R.F 0).map 0 ell := by
      rw [← hfinal.1.2.2]
      exact hiI
    exact hrep.2.2
  by_cases hieq : i = ell
  · subst i
    obtain ⟨x, hx, hxlev⟩ := hTop
    exact Or.inl ⟨x, subset_closure S (higherLevels (R.I 0) ell) X hx, hxlev⟩
  · have hilt : i < ell := lt_of_le_of_ne hiell hieq
    have htail := R.I_eq_final_tail hE1 hXbound i (by omega)
    have hiStage : i ∈ R.I i := by
      rw [htail]
      exact ⟨hiI, le_rfl⟩
    have hnext := R.nextI_eq hE1 hXbound i hilt
    have hiNotNext : i ∉ R.I (i + 1) := by
      rw [hnext]
      intro h
      exact (lt_irrefl i) h.2
    have hinter :
        IsInterestingAt H (closure S (R.I (i + 1)) X) i := by
      by_contra hnot
      rcases R.noninteresting_step i hilt hnot with
        ⟨D, hDskip, hDcross, hI, hF⟩
      apply hiNotNext
      rw [← hI]
      exact hiStage
    have hlevels :=
      R.I_succ_eq_higher_final hE1 hXbound i hilt
    rw [hlevels] at hinter
    exact hinter

/-- Every selected level of a run is represented by every competing prefix
envelope. -/
theorem finalLevels_subset_competitor
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell)
    (E : MMap H) (m : Nat)
    (hEnvelope : IsPrefixEnvelope E.map m X) :
    ∀ ⦃i : Nat⦄, i ∈ R.I 0 →
      RepresentedBefore H E.map m i := by
  have hfinal := R.fullInvariant hE1 hXbound 0 (Nat.zero_le ell)
  have hbound :
      ∀ ⦃i : Nat⦄, i ∈ R.I 0 → i ≤ ell := by
    intro i hi
    have hrep : i ∈ representedLevels (R.F 0).map 0 ell := by
      rw [← hfinal.1.2.2]
      exact hi
    exact hrep.2.2
  exact algorithmLevels_subset_competitor
    H X ell m (R.I 0) E hTop hbound hEnvelope
    (R.finalLevel_interesting hE1 hXbound hTop)

/-- The final level sets of any two runs coincide. -/
theorem I_eq
    (R R' : AlgorithmRun H X ell) :
    ∀ (i : Nat), i ≤ ell → R.I i = R'.I i := by
  have main :
      ∀ d : Nat, ∀ i : Nat, ell - i = d → i ≤ ell →
        R.I i = R'.I i := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i hdi hiell
        by_cases hieq : i = ell
        · subst i
          rw [R.topI, R'.topI]
        · have hilt : i < ell := lt_of_le_of_ne hiell hieq
          have hsmall : ell - (i + 1) < d := by
            rw [← hdi]
            omega
          have hnext :
              R.I (i + 1) = R'.I (i + 1) :=
            ih (ell - (i + 1)) hsmall (i + 1) rfl (by omega)
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
  intro i hiell
  exact main (ell - i) i rfl hiell

/-- The embedding type of X is independent of every one-level choice made in
the run. -/
theorem embeddingType_eq
    (R R' : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell) :
    ∀ (i : Nat), i ≤ ell →
      (R.F i).map ⁻¹' X = (R'.F i).map ⁻¹' X := by
  have main :
      ∀ d : Nat, ∀ i : Nat, ell - i = d → i ≤ ell →
        (R.F i).map ⁻¹' X = (R'.F i).map ⁻¹' X := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i hdi hiell
        by_cases hieq : i = ell
        · subst i
          rw [R.topF, R'.topF]
        · have hilt : i < ell := lt_of_le_of_ne hiell hieq
          have hsmall : ell - (i + 1) < d := by
            rw [← hdi]
            omega
          have hIeq : R.I (i + 1) = R'.I (i + 1) :=
            R.I_eq R' (i + 1) (by omega)
          have htypeNext :
              (R.F (i + 1)).map ⁻¹' X =
                (R'.F (i + 1)).map ⁻¹' X :=
            ih (ell - (i + 1)) hsmall (i + 1) rfl (by omega)
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
  intro i hiell
  exact main (ell - i) i rfl hiell

end AlgorithmRun

end Envelope
end SMTree
end SuccessorTree

import SuccessorTree.V10.I3AlgorithmRunPool
import SuccessorTree.V10.I3ActualHigherSignature
import SuccessorTree.V10.HHighOriginalNameEnumeration
import Mathlib.Tactic

/-!
# V10 Proposition 6.44: actual AlgorithmRun I3 at one generation

The genuine Algorithm 5.4 run selects only levels interesting for
the closure of the previously selected higher levels. With (I1)
and (I2) excluded, the actual selected closure crossing has
a failed corrected B3 finite L-age test.

Use the canonical enumeration of ONE fixed final-stage original
pool V. By the full I3 relocation theorem, every selected upper
original of a failed age test has real generation strictly
greater than that of the tested vertex. These are precisely the
names in hHighOriginalNameIndices k g V.

The verified higher-generation signature collision theorem now
bounds the actual I3 levels at generation g by
R(|hGenerationHighOriginals k g V|).

This theorem does not assume signature witnesses or a separate
family of failed B3 tests. It requires the genuine AlgorithmRun,
its initial original-pool invariant, the two excluded I1/I2
events, and the manuscript's bounded forbidden arities.
The I1/I2 count and final downward summation are separate.
-/

namespace SuccessorTree.V10

/-- Actual Algorithm 5.4 I3 selection produces a FAILED corrected
finite B3 age test for the closure-selected source, with the complete
target graph of the SAME ambient originals. -/
theorem numericH_algorithmRun_I3_stage_failedB3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family (finiteNumericH K k N)
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun (normalizedKptSMTree family) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (ell : Nat) (hPos : 0 < ell)
    (hLt : ell < top) (hN : ell < N) (hSelected : ell ∈ R.I 0)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (ell+1)) X ∧
      LevelTree.lev z = ell)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I (ell+1)) X ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (ell+1)) X ∧
        SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = ell) :
    ¬ (selectedStagePoolPrescribedData
       (finiteNumericH K k N) ell
       (hOriginalName (hStageOriginals K k N U (R.I 0)))
       (closureSelectedOriginal family (finiteNumericH K k N)
         (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
         (hOriginalName (hStageOriginals K k N U (R.I 0)))
         (SMTree.Envelope.closure (admissibleKptSTree family)
           (R.I (ell+1)) X) ell)).CorrectedB3 family := by
  classical
  let A := finiteNumericH K k N
  let hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  let V := hStageOriginals K k N U (R.I 0)
  let original : Fin V.card → Fin N := hOriginalName V
  let Z := SMTree.Envelope.closure (admissibleKptSTree family)
    (R.I (ell+1)) X
  have hPool : ∀ z, z ∈ Z →
      ∃ v : Fin V.card, z ≤ A.kptOriginal family hAvoidA (original v) := by
    intro z hz
    obtain ⟨v,hv,hzv⟩ :=
      numericH_algorithmRun_closure_original_in_final_pool
        family K hCarrier hAvoidK k N U X hX top ell hLt R z hz
    let j : Fin V.card := V.equivFin ⟨v,hv⟩
    have hOriginal : original j = v := by
      simp [original, hOriginalName, j]
    refine ⟨j, ?_⟩
    simpa [A, hAvoidA, hOriginal] using hzv
  have hInteresting :
      SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family) Z ell := by
    have hI := R.finalLevel_interesting_of_run hTop hSelected
    have hNext := R.I_succ_eq_higher_final_of_run ell hLt
    simpa only [Z,hNext] using hI
  have hFail := algorithmI3_failsCorrectedB3
    family A hAvoidA original Z hPool ell hPos
    hNoI1 hNoI2 hInteresting
  exact hFail

/-- Sharp R(M_g) bound at one positive non-top real generation of
the ACTUAL envelope run. The only counted upper names are actual
members of the final maintained stage pool with generation >g;
the estimate does not charge to the entire original pool. -/
theorem numericH_algorithmRun_I3_generation_card_le_high_pool
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N g : Nat) (hg : g < k)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family (finiteNumericH K k N)
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun (normalizedKptSMTree family) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (levels : Finset Nat)
    (hLevels : ∀ ell, ell ∈ levels →
      0 < ell ∧ ell < top ∧ ell < N ∧ ell ∈ R.I 0 ∧
      ∃ iGen : Nat, ell = hPosition k iGen g)
    (hNoI1 : ∀ ell, ell ∈ levels →
      ¬ ∃ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (ell+1)) X ∧
        LevelTree.lev z = ell)
    (hNoI2 : ∀ ell, ell ∈ levels →
      ¬ ∃ a : AdmissibleKptNode family,
        a ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (ell+1)) X ∧
        ∃ b : AdmissibleKptNode family,
          b ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (ell+1)) X ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = ell)
    (hFamilyBound : ∀ bad, bad ∈ family →
      bad.patternCard ≤ k+1) :
    levels.card ≤ ageSignatureCapacity
      (fun i : Fin family.length => (family.get i).patternCard)
      (hGenerationHighOriginals k g
        (hStageOriginals K k N U (R.I 0))).card := by
  classical
  let V := hStageOriginals K k N U (R.I 0)
  let original : Fin V.card → Fin N := hOriginalName V
  let Selected : Nat → Fin V.card → Prop :=
    fun ell => closureSelectedOriginal family (finiteNumericH K k N)
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      original
      (SMTree.Envelope.closure (admissibleKptSTree family)
        (R.I (ell+1)) X) ell
  let H : Nat := (hHighOriginalNameIndices k g V).card
  let higher : Fin H → Fin V.card := hHighOriginalName k g V
  have hGeneration : ∀ ell, ell ∈ levels →
      ell < N ∧ ∃ iGen : Nat, ell = hPosition k iGen g := by
    intro ell hEll
    obtain ⟨_hPos,_hLt,hN,_hSelected,hGen⟩ := hLevels ell hEll
    exact ⟨hN,hGen⟩
  have hFailures : ∀ ell, ell ∈ levels →
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH K k N) ell original (Selected ell)).CorrectedB3
          family := by
    intro ell hEll
    obtain ⟨hPos,hLt,hN,hSelected,_hGen⟩ := hLevels ell hEll
    exact numericH_algorithmRun_I3_stage_failedB3
      family K hCarrier hAvoidK k N U X hX top R hTop
      ell hPos hLt hN hSelected (hNoI1 ell hEll) (hNoI2 ell hEll)
  have hCover : ∀ v : Fin V.card,
      (∃ j m : Nat, g < m ∧ m ≤ k ∧
        (original v).val = hPosition k j m) →
      ∃ h : Fin H, higher h = v := by
    intro v hReal
    exact hHighOriginalName_covers_real_higher k g V v hReal
  exact numericH_selectedB3_generation_levels_card_le_higher_budget
    family K hCarrier hAvoidK k N g hg
    original Selected levels hGeneration hFamilyBound hFailures
    higher hCover (hGenerationHighOriginals k g V).card
    (hHighOriginalNameIndices_card_le k g V)

end SuccessorTree.V10

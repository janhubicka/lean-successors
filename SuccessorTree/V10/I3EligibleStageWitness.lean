import SuccessorTree.V10.I3EligibleStagePool
import SuccessorTree.V10.I3ActualStageGeneration
import SuccessorTree.V10.I3AmbientSocleBridge
import Mathlib.Tactic

/-!
# I3: failed B3 on the actual cut-filtered stage original pool

The manuscript keeps one fixed finite original-name pool across all
selected levels, but only originals whose E-free cut reaches ell+1
are sources at the tested level ell.  A failed B3 test on this
filtered source gives an L-only forbidden age witness.  Crucially
every UPPER witness type still comes from an *eligible* original
name, not merely some name in the unfiltered pool.

Combining this fact with the verified numerical H relocation lemma
gives the exact generation conclusions of Lemma 6.53 for the
cut-filtered stage prescription.  No E is assigned to the age
witness, no new axiom or arity assumption is introduced, and the
original pool has the same cardinal M at every stage.

It remains to identify the manuscript's selected I3 levels with
failed tests of precisely this stage prescription and connect their
per-generation signature bounds to Proposition 6.44.
-/

namespace SuccessorTree.V10

/-- The failed corrected B3 of the real stage prescription produces
an actual finite L-only witness with a forbidden copy, the common
ambient L-socle and an ELIGIBLE original name for every upper
witness.  This retains the free-cut guard for use in the numerical
H generation lemma, which is lost if one applies the unfiltered
ambient-pool witness theorem. -/
theorem stagePool_failedCorrectedB3_has_eligible_original_witness
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hEll : ell < A.size)
    (original : Fin M → Fin A.size)
    (hFailure :
      ¬ (stagePoolPrescribedData A ell original).CorrectedB3 family) :
    ∃ S0 : PartialTypeWithE ell db du dd,
      S0 ∈ (stagePoolPrescribedData A ell original).source ∧
      ∃ W : AgeTestModel db du dd,
        W.BoundedCarrier ∧
        SameInitialL W A.L ell ∧
        (∀ bad, bad ∈ family → bad.Avoids (W.withoutVertex ell)) ∧
        (∀ x, x ∈ W.carrier → ell < x →
          ∃ v : Fin M,
            ell+1 ≤ A.freeLevel (original v).val ∧
            RelationalPrefixType.ofAgeModel W (ell+1) x =
              RelationalPrefixType.ofAgeModel A.L (ell+1)
                (original v).val) ∧
        ∃ bad, bad ∈ family ∧ ¬ bad.Avoids W := by
  classical
  let F := stagePoolPrescribedData A ell original
  have hFailCompatible : ¬ F.CompatibleB3 family := by
    intro hGood
    apply hFailure
    exact (stagePoolPrescribedData_correctedB3_iff_compatibleB3
      family A ell original).2 hGood
  unfold PrescribedBoringData.CompatibleB3 at hFailCompatible
  push_neg at hFailCompatible
  obtain ⟨S0,hS0,hFailedAge⟩ := hFailCompatible
  obtain ⟨W,hFinite,hSame,hUpper,hDelete,bad,hMember,hBad⟩ :=
    failedCommonSocleAgeTest_has_finite_L_witness
      family (prescribedOrdinarySocle (F.target S0))
      ell (F.CompatibleUpperLType S0) hFailedAge
  have hSameAmbient : SameInitialL W A.L ell := by
    obtain ⟨v,_hCut,_hOld,hTarget⟩ :=
      stagePoolPrescribedData_source_original A ell original S0 hS0
    have hSocleTarget :
        SameInitialL (prescribedOrdinarySocle (F.target S0))
          A.L ell := by
      rw [hTarget]
      exact ambient_partialType_prescribedSocle
        A ell (original v).val hEll
    exact hSame.trans hSocleTarget
  refine ⟨S0,hS0,W,hFinite,hSameAmbient,hDelete,?_,bad,hMember,hBad⟩
  intro x hx hAbove
  obtain ⟨T,hT,_hCompatible,hType⟩ := hUpper x hx hAbove
  obtain ⟨v,hCut,_hOld,hTarget⟩ :=
    stagePoolPrescribedData_source_original A ell original T hT
  refine ⟨v,hCut,?_⟩
  have hReduct :
      (F.target T).lReduct =
        RelationalPrefixType.ofAgeModel A.L (ell+1)
          (original v).val := by
    rw [hTarget]
    exact partialTypeAt_lReduct_eq_ofAgeModel
      A (ell+1) (original v).val
  exact hType.trans hReduct

/-- The actual numerical H and the real stage-eligible pool of M
originals give BOTH the fixed original labels needed for the I3
signature code and Lemma 6.53's exact generation information.
Unlike the earlier unfiltered statement, no hypothesis requires
every member of the original list to be eligible at this cut. -/
theorem finiteNumericH_failedStagePoolB3_generation
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N ell : Nat) (hEll : ell < N)
    (original : Fin M → Fin N)
    (hFamilyBound : ∀ bad, bad ∈ family →
      bad.patternCard ≤ k+1)
    (hFailure :
      ¬ (stagePoolPrescribedData (finiteNumericH K k N)
          ell original).CorrectedB3 family) :
    ∃ W : AgeTestModel db du dd,
      W.BoundedCarrier ∧
      SameInitialL W (finiteNumericHL K k N) ell ∧
      (∀ bad, bad ∈ family → bad.Avoids (W.withoutVertex ell)) ∧
      ∃ (t : Nat) (P : ForbiddenAtomicPattern t db du dd)
        (e : Fin t → Nat) (r : Nat)
        (hr : 0 < r) (hrt : r < t),
        P.Irreducible ∧
        W.Realizes P e ∧
        (∀ a : Fin t, a.val < r ↔ e a ≤ ell) ∧
        (∀ a : Fin t, r ≤ a.val ↔ ell < e a) ∧
        (∀ b : Fin t, r ≤ b.val →
          ∃ v : Fin M,
            ell+1 ≤ (finiteNumericH K k N).freeLevel
              (original v).val ∧
            RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
              RelationalPrefixType.ofAgeModel
                (finiteNumericHL K k N) (ell+1) (original v).val) ∧
        (∃ i : Nat,
          ell = hPosition k i (r-1) ∧
          ∀ b : Fin t, r ≤ b.val →
            ∃ j m : Nat, r-1 < m ∧ m ≤ k ∧
              ell < hPosition k j m ∧
              RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
                RelationalPrefixType.ofAgeModel
                  (finiteNumericHL K k N) (ell+1)
                    (hPosition k j m)) := by
  classical
  let A : EnumeratedPartialStructure db du dd :=
    finiteNumericH K k N
  have hEllA : ell < A.size := hEll
  obtain ⟨S0,hS0,W,hFinite,hSocle,hDelete,hUpper,bad,hMember,hBad⟩ :=
    stagePool_failedCorrectedB3_has_eligible_original_witness
      family A ell hEllA original hFailure
  have hSocleH :
      SameInitialL W (finiteNumericHL K k N) ell := hSocle
  have hAvoidA : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N) :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  obtain ⟨t,P,e,r,hr,hrt,hrk,hIrred,hCopy,hDeleteP,hLast,hLow,hHigh⟩ :=
    normalizedForbidden_bounded_I3_proper_cut
      (finiteNumericHL K k N) W ell k bad
      (hFamilyBound bad hMember) hSocleH
      (hAvoidA bad hMember) (hDelete bad hMember) hBad
  have hUpperNames : ∀ b : Fin t, r ≤ b.val →
      ∃ v : Fin M,
        ell+1 ≤ A.freeLevel (original v).val ∧
        RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (ell+1) (original v).val := by
    intro b hb
    have hAbove : ell < e b := (hHigh b).1 hb
    obtain ⟨v,hCut,hType⟩ :=
      hUpper (e b) (hCopy.2.1 b) hAbove
    exact ⟨v,hCut,hType⟩
  have hUpperNamed : ∀ b : Fin t, r ≤ b.val →
      ∃ originalAddress : Nat, ell < originalAddress ∧
        RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (ell+1)
              originalAddress := by
    intro b hb
    obtain ⟨v,hCut,hType⟩ := hUpperNames b hb
    have hAddress : A.freeLevel (original v).val ≤
        (original v).val :=
      A.freeLevel_le (original v).val
    have hAfter : ell < (original v).val := by omega
    exact ⟨(original v).val,hAfter,hType⟩
  obtain ⟨i,hGeneration,hStrictUpper⟩ :=
    numericI3_actual_witness_generation_conclusions
      K k N ell r hr hrt hrk W hSocleH
      P hIrred e hCopy hDeleteP hLast hUpperNamed
  exact ⟨W,hFinite,hSocleH,hDelete,t,P,e,r,hr,hrt,
    hIrred,hCopy,hLow,hHigh,hUpperNames,
    i,hGeneration,hStrictUpper⟩

end SuccessorTree.V10

import SuccessorTree.V10.I3HigherSignatureCapacity
import SuccessorTree.V10.I3ChosenOriginalGeneration
import SuccessorTree.V10.I3StageSignatureBound
import Mathlib.Tactic

/-!
# I3: construct higher-generation signatures from actual selected B3 failure

The exact forbidden pattern (including its finite-family index) must
be retained while Lemma 6.53 proves the strict-generation property
of the selected upper ORIGINAL LABELS. Merely producing a different
equivalent upper H-coordinate would not justify the bound R(M_r).

This module combines the finite L-only selected-stage age witness,
the real numerical H generation/relocation proof, and the indexed
signature construction. For all failed selected B3 stages of a fixed
generation r it produces signatures named ONLY by higher-generation
originals and hence the sharp R(M_r) bound.

Only the global connection to Algorithm 5.4's selected stages and
the inductive cardinal budget for higher originals remain outside
these theorems. No additional E on an arbitrary age witness.
-/

namespace SuccessorTree.V10

/-- The exact underlying normalized forbidden pattern has a
nonempty proper ordered lower cut in a failed finite L-age test.
The result keeps the ACTUAL pattern of the forbidden-family
entry, rather than replacing it by an unindexed pattern. -/
theorem normalizedForbidden_bounded_signature_cut
    {db du dd : Nat}
    (C W : AgeTestModel db du dd) (ell k : Nat)
    (bad : NormalizedForbidden db du dd)
    (hBound : bad.patternCard ≤ k+1)
    (hSocle : SameInitialL W C ell)
    (hAvoidC : bad.Avoids C)
    (hAvoidDelete : bad.Avoids (W.withoutVertex ell))
    (hViolation : ¬ bad.Avoids W) :
    ∃ (e : Fin bad.patternCard → Nat) (r : Nat)
      (hr : 0 < r) (hrt : r < bad.patternCard)
      (hrk : r ≤ k),
      bad.signaturePattern.Irreducible ∧
      W.Realizes bad.signaturePattern e ∧
      (¬ ∃ f : Fin bad.patternCard → Nat,
        (W.withoutVertex ell).Realizes bad.signaturePattern f) ∧
      e (⟨r-1, by omega⟩ : Fin bad.patternCard) = ell ∧
      (∀ a : Fin bad.patternCard, a.val < r ↔ e a ≤ ell) ∧
      (∀ a : Fin bad.patternCard, r ≤ a.val ↔ ell < e a) := by
  classical
  cases bad with
  | singleton P hNonNeutral =>
      change ¬ ∃ f : Fin 1 → Nat, C.Realizes P f at hAvoidC
      change ¬ ∃ f : Fin 1 → Nat,
        (W.withoutVertex ell).Realizes P f at hAvoidDelete
      change ¬ ¬ ∃ f : Fin 1 → Nat, W.Realizes P f at hViolation
      obtain ⟨e,hCopy⟩ := not_not.mp hViolation
      obtain ⟨a,ha⟩ :=
        forbiddenCopy_meets_tested_coordinate
          W ell P e hCopy hAvoidDelete
      obtain ⟨b,hb⟩ :=
        forbiddenCopy_has_upper_of_sameInitialL
          W C ell P e hSocle hAvoidC hCopy
      have hab : a = b := Subsingleton.elim _ _
      rw [←hab] at hb
      omega
  | nontrivial t P ht hIrred =>
      change t ≤ k+1 at hBound
      change ¬ ∃ f : Fin t → Nat, C.Realizes P f at hAvoidC
      change ¬ ∃ f : Fin t → Nat,
        (W.withoutVertex ell).Realizes P f at hAvoidDelete
      change ¬ ¬ ∃ f : Fin t → Nat, W.Realizes P f at hViolation
      obtain ⟨e,hCopy⟩ := not_not.mp hViolation
      have hAt : ∃ a : Fin t, e a = ell :=
        forbiddenCopy_meets_tested_coordinate
          W ell P e hCopy hAvoidDelete
      have hUpper : ∃ b : Fin t, ell < e b :=
        forbiddenCopy_has_upper_of_sameInitialL
          W C ell P e hSocle hAvoidC hCopy
      obtain ⟨r,hr,hrt,hLast,hLow,hHigh⟩ :=
        i3_forbidden_age_copy_lower_cut W P e hCopy ell hAt hUpper
      have hrk : r ≤ k := by omega
      exact ⟨e,r,hr,hrt,hrk,hIrred,hCopy,
        hAvoidDelete,hLast,hLow,hHigh⟩

/-- The same actual finite B3 witness whose forbidden pattern
determines its signature also has CHOSEN upper original names
of generation strictly above g. These names are taken from one
fixed original pool; the selected subset may vary by stage. -/
theorem numericH_failedSelectedB3_higher_signature_witness
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N ell g iGen : Nat)
    (hg : g < k)
    (hEll : ell < N)
    (hGeneration : ell = hPosition k iGen g)
    (original : Fin M → Fin N)
    (Selected : Fin M → Prop)
    (hFamilyBound : ∀ bad, bad ∈ family →
      bad.patternCard ≤ k+1)
    (hFailure :
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH K k N) ell original Selected).CorrectedB3 family) :
    ∃ w : I3OriginalSignatureWitness
      (fun i : Fin family.length => (family.get i).patternCard)
      (fun i => (family.get i).signaturePattern)
      (finiteNumericHL K k N) (fun v => (original v).val) ell,
      ∀ a : Fin ((family.get w.familyIndex).patternCard),
        ell < w.e a →
        ∃ v : Fin M,
          (∃ j m : Nat, g < m ∧ m ≤ k ∧
            (original v).val = hPosition k j m) ∧
          RelationalPrefixType.ofAgeModel w.W (ell+1) (w.e a) =
            RelationalPrefixType.ofAgeModel
              (finiteNumericHL K k N) (ell+1) (original v).val := by
  classical
  let A : EnumeratedPartialStructure db du dd :=
    finiteNumericH K k N
  have hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  obtain ⟨S0,hS0,W,hFinite,hSocle,hDelete,hUpper,bad,hMember,hBad⟩ :=
    selectedStagePool_failedCorrectedB3_has_selected_original_witness
      family A ell hEll original Selected hFailure
  obtain ⟨j,hj,hGet⟩ := List.getElem_of_mem hMember
  let i : Fin family.length := ⟨j,hj⟩
  have hIndex : family.get i = bad := hGet
  subst bad
  have hSocleH :
      SameInitialL W (finiteNumericHL K k N) ell := hSocle
  obtain ⟨e,r,hr,hrt,hrk,hIrred,hCopy,hDeleteP,hLast,hLow,hHigh⟩ :=
    normalizedForbidden_bounded_signature_cut
      (finiteNumericHL K k N) W ell k (family.get i)
      (hFamilyBound (family.get i) hMember)
      hSocleH (hAvoidA (family.get i) hMember)
      (hDelete (family.get i) hMember) hBad
  have hNamed : ∀ b : Fin (family.get i).patternCard, r ≤ b.val →
      ∃ v : Fin M,
        (Selected v ∧ ell+1 ≤ A.freeLevel (original v).val) ∧
        ell < (original v).val ∧
        RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (ell+1) (original v).val := by
    intro b hb
    have hAbove : ell < e b := (hHigh b).1 hb
    obtain ⟨v,hSel,hCut,hType⟩ :=
      hUpper (e b) (hCopy.2.1 b) hAbove
    have hAddress : A.freeLevel (original v).val ≤
        (original v).val :=
      A.freeLevel_le (original v).val
    have hAfter : ell < (original v).val := by omega
    exact ⟨v,⟨hSel,hCut⟩,hAfter,hType⟩
  have hUpperNamed : ∀ b : Fin (family.get i).patternCard, r ≤ b.val →
      ∃ originalAddress : Nat, ell < originalAddress ∧
        RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (ell+1) originalAddress := by
    intro b hb
    obtain ⟨v,_hSel,hAfter,hType⟩ := hNamed b hb
    exact ⟨(original v).val,hAfter,hType⟩
  obtain ⟨iH,hGenerationLast,_hStrictUpper⟩ :=
    numericI3_actual_witness_generation_conclusions
      K k N ell r hr hrt hrk W hSocleH
      (family.get i).signaturePattern hIrred e hCopy
      hDeleteP hLast hUpperNamed
  have hGenEq : g = r-1 := by
    obtain ⟨_hBase,hRank⟩ :=
      hPosition_injective_bounded k iGen g iH (r-1)
        (Nat.le_of_lt hg) (by omega) (hGeneration.symm.trans hGenerationLast)
    exact hRank
  have hChosenHigh :=
    numericI3_selected_named_originals_have_higher_generation
      K k N ell r hr hrt hrk W (family.get i).signaturePattern
      hIrred e hCopy hLast
      (fun v => (original v).val)
      (fun v => Selected v ∧ ell+1 ≤ A.freeLevel (original v).val)
      hNamed ⟨iH,hGenerationLast⟩
  have hUpperIndex : ∀ a : Fin (family.get i).patternCard,
      ell < e a → r ≤ a.val := by
    intro a ha
    exact (hHigh a).2 ha
  let w : I3OriginalSignatureWitness
      (fun i : Fin family.length => (family.get i).patternCard)
      (fun i => (family.get i).signaturePattern)
      (finiteNumericHL K k N) (fun v => (original v).val) ell := {
    familyIndex := i
    W := W
    e := e
    finite := hFinite
    copy := hCopy
    socle := hSocleH
    deleteAvoids := hDeleteP
    upperNames := by
      intro a ha
      obtain ⟨v,_j,_m,_hSel,_hReal,_hStrict,_hm,hType⟩ :=
        hChosenHigh a (hUpperIndex a ha)
      exact ⟨v,hType⟩
  }
  refine ⟨w,?_⟩
  intro a ha
  obtain ⟨v,j',m,hBoth,hReal,hStrict,hm,hType⟩ :=
    hChosenHigh a (hUpperIndex a ha)
  refine ⟨v,⟨j',m,?_,hm,hReal⟩,hType⟩
  omega

/-- Uniform at one fixed generation g: let isHigher name exactly
those fixed-pool originals whose REAL H-generation is >g.
Every selected-stage corrected-B3 failure at a real level of
generation g has an actual high-named I3 signature.  Thus only
the number of high originals controls the R(M_g) estimate. -/
theorem numericH_selectedB3_generation_levels_card_le_higher_budget
    {db du dd M H : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N g : Nat) (hg : g < k)
    (original : Fin M → Fin N)
    (Selected : Nat → Fin M → Prop)
    (levels : Finset Nat)
    (hGeneration : ∀ ell, ell ∈ levels →
      ell < N ∧ ∃ iGen : Nat, ell = hPosition k iGen g)
    (hFamilyBound : ∀ bad, bad ∈ family →
      bad.patternCard ≤ k+1)
    (hFailures : ∀ ell, ell ∈ levels →
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH K k N) ell original (Selected ell)).CorrectedB3 family)
    (higher : Fin H → Fin M)
    (hCover : ∀ v : Fin M,
      (∃ j m : Nat, g < m ∧ m ≤ k ∧
        (original v).val = hPosition k j m) →
      ∃ h : Fin H, higher h = v)
    (Mr : Nat) (hHigherBound : H ≤ Mr) :
    levels.card ≤
      ageSignatureCapacity
        (fun i : Fin family.length => (family.get i).patternCard) Mr := by
  classical
  let sizes : Fin family.length → Nat :=
    fun i => (family.get i).patternCard
  let patterns : (i : Fin family.length) →
      ForbiddenAtomicPattern (sizes i) db du dd :=
    fun i => (family.get i).signaturePattern
  let isHigher : Fin M → Prop :=
    fun v => ∃ j m : Nat, g < m ∧ m ≤ k ∧
      (original v).val = hPosition k j m
  have hInitial : ∀ ell, ell ∈ levels →
      ∀ x, x ≤ ell → x ∈ (finiteNumericHL K k N).carrier := by
    intro ell hMem x hx
    have hBound := (hGeneration ell hMem).1
    change x < N
    omega
  have hWitness : ∀ ell, ell ∈ levels →
      ∃ w : I3OriginalSignatureWitness sizes patterns
          (finiteNumericHL K k N) (fun v => (original v).val) ell,
        ∀ a : Fin (sizes w.familyIndex), ell < w.e a →
          ∃ v : Fin M, isHigher v ∧
            RelationalPrefixType.ofAgeModel w.W (ell+1) (w.e a) =
              RelationalPrefixType.ofAgeModel
                (finiteNumericHL K k N) (ell+1) (original v).val := by
    intro ell hMem
    obtain ⟨hCut,iGen,hPos⟩ := hGeneration ell hMem
    exact numericH_failedSelectedB3_higher_signature_witness
      family K hCarrier hAvoidK k N ell g iGen hg hCut hPos
      original (Selected ell) hFamilyBound (hFailures ell hMem)
  exact i3SelectedLevels_card_le_higherGenerationBudget
    sizes patterns (finiteNumericHL K k N)
    (fun v => (original v).val) isHigher higher hCover
    levels hInitial hWitness Mr hHigherBound

end SuccessorTree.V10

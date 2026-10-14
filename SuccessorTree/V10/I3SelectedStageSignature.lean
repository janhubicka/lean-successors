import SuccessorTree.V10.I3ChosenOriginalGeneration
import SuccessorTree.V10.I3StageSignatureBound
import Mathlib.Tactic

/-!
# Observation 6.52 for the ACTUAL variable selected closure sources

The original-name universe Fin M is fixed; at a given level ell
the actual Algorithm 5.4 closure has an arbitrary varying selected
subset of that universe. Its finite source may therefore be strictly
smaller than the whole ambient pool whose free cut reaches ell+1.

Every selected-pool B3 failure produces an actual finite induced
forbidden-copy signature with the selected original labels; the
existing collision argument proves that there are at most R(M)
distinct failed levels.  More importantly, if each manuscript
stage function f_ell has precisely this selected source and agrees
with the complete next type of every selected original, then the
same bound holds for failures of those ACTUAL functions.

The two source/target identification clauses remain explicit: they
must be derived from the closure invariant and the absence of (I2),
not asserted just because the ambient free cuts are long enough.
-/

namespace SuccessorTree.V10

/-- A failed selected-pool B3 test supplies the actual indexed
forbidden signature of Observation 6.52. Different selected
subsets at different levels still use names from the SAME Fin M. -/
theorem selectedStagePool_failedB3_has_signature_witness
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hEll : ell < A.size)
    (original : Fin M → Fin A.size)
    (Selected : Fin M → Prop)
    (hFailure :
      ¬ (selectedStagePoolPrescribedData
        A ell original Selected).CorrectedB3 family) :
    Nonempty (I3OriginalSignatureWitness
      (fun i : Fin family.length => (family.get i).patternCard)
      (fun i => (family.get i).signaturePattern)
      A.L (fun v => (original v).val) ell) := by
  classical
  obtain ⟨S0,hS0,W,hFinite,hSocle,hDelete,hUpper,bad,hMember,hBad⟩ :=
    selectedStagePool_failedCorrectedB3_has_selected_original_witness
      family A ell hEll original Selected hFailure
  obtain ⟨j,hj,hGet⟩ := List.getElem_of_mem hMember
  let i : Fin family.length := ⟨j,hj⟩
  have hIndex : family.get i = bad := hGet
  have hViolation : ¬ (family.get i).Avoids W := by
    rw [hIndex]
    exact hBad
  have hAvoidDelete : (family.get i).Avoids (W.withoutVertex ell) := by
    rw [hIndex]
    exact hDelete bad hMember
  obtain ⟨e,hCopy⟩ :=
    (family.get i).signaturePattern_copy_of_violation W hViolation
  have hNoCopyDelete :
      ¬ ∃ f : Fin (family.get i).patternCard → Nat,
        (W.withoutVertex ell).Realizes
          (family.get i).signaturePattern f :=
    ((family.get i).signaturePattern_avoids_iff
      (W.withoutVertex ell)).1 hAvoidDelete
  refine ⟨{
    familyIndex := i
    W := W
    e := e
    finite := hFinite
    copy := hCopy
    socle := hSocle
    deleteAvoids := hNoCopyDelete
    upperNames := ?_
  }⟩
  intro a hAbove
  obtain ⟨v,_hSelected,_hCut,hType⟩ :=
    hUpper (e a) (hCopy.2.1 a) hAbove
  exact ⟨v,hType⟩

/-- Sharp R(M) capacity for arbitrary stage-dependent selected
subsets of one fixed M-element original-name pool. No unconditional
signature witnesses or injection hypotheses occur in the statement. -/
theorem selectedStagePool_B3_failure_levels_card_le_signature_capacity
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (original : Fin M → Fin A.size)
    (Selected : Nat → Fin M → Prop)
    (levels : Finset Nat)
    (hFailures : ∀ ell, ell ∈ levels →
      ell < A.size ∧
      ¬ (selectedStagePoolPrescribedData
        A ell original (Selected ell)).CorrectedB3 family) :
    levels.card ≤
      ageSignatureCapacity
        (fun i : Fin family.length => (family.get i).patternCard) M := by
  classical
  have hInitial : ∀ ell, ell ∈ levels →
      ∀ x, x ≤ ell → x ∈ A.L.carrier := by
    intro ell hMem x hx
    apply (A.carrier_iff x).2
    have hBound := (hFailures ell hMem).1
    omega
  have hWitness : ∀ ell, ell ∈ levels →
      Nonempty (I3OriginalSignatureWitness
        (fun i : Fin family.length => (family.get i).patternCard)
        (fun i => (family.get i).signaturePattern)
        A.L (fun v => (original v).val) ell) := by
    intro ell hMem
    obtain ⟨hCut,hFailed⟩ := hFailures ell hMem
    exact selectedStagePool_failedB3_has_signature_witness
      family A ell hCut original (Selected ell) hFailed
  exact i3SelectedLevels_card_le_signature_capacity
    (fun i : Fin family.length => (family.get i).patternCard)
    (fun i => (family.get i).signaturePattern)
    A.L (fun v => (original v).val)
    levels hInitial hWitness

/-- Manuscript-facing form: if the actual f_ell source and complete
next-type graph agree with the level-dependent selected original
pool, then all actual I3 failed stages have at most R(M) levels.
This is a consequence of the EXPLICIT identification and the
verified signature collision, not a claim that an arbitrary ambient
pool magically represents the closure. -/
theorem actualSelectedStage_B3_failure_levels_card_le_signature_capacity
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (original : Fin M → Fin A.size)
    (Selected : Nat → Fin M → Prop)
    (F : (ell : Nat) → PrescribedBoringData ell db du dd)
    (levels : Finset Nat)
    (hFailed : ∀ ell, ell ∈ levels →
      ell < A.size ∧ ¬ (F ell).CorrectedB3 family)
    (hSource : ∀ ell, ell ∈ levels →
      ∀ T, T ∈ (F ell).source ↔
        T ∈ (selectedStagePoolPrescribedData
          A ell original (Selected ell)).source)
    (hGraph : ∀ ell, ell ∈ levels →
      ∀ v : Fin M, Selected ell v →
        ell+1 ≤ A.freeLevel (original v).val →
        (F ell).target (A.partialTypeAt ell (original v).val) =
          A.partialTypeAt (ell+1) (original v).val) :
    levels.card ≤
      ageSignatureCapacity
        (fun i : Fin family.length => (family.get i).patternCard) M := by
  apply selectedStagePool_B3_failure_levels_card_le_signature_capacity
    family A original Selected levels
  intro ell hMem
  obtain ⟨hEll,hBad⟩ := hFailed ell hMem
  have hB3Equiv :=
    selectedStagePool_B3_iff_of_source_and_graph
      family A ell original (Selected ell) (F ell)
      (hSource ell hMem) (hGraph ell hMem)
  exact ⟨hEll,fun hGood => hBad (hB3Equiv.mpr hGood)⟩

end SuccessorTree.V10

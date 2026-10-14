import SuccessorTree.V10.I3EligibleStageWitness
import SuccessorTree.V10.I3SignatureCardinality
import Mathlib.Tactic

/-!
# I3: automatic signature bound for real failed stage tests

For a fixed list of named originals, the concrete eligible stage
prescription varies with the tested cut.  A failed corrected B3 test
at any cut gives a finite original-labelled L-only forbidden witness
by I3EligibleStageWitness.  This file converts that witness into the
indexed-family signature records of Observation 6.52 and proves the
actual R(M) cardinal bound for EVERY finite set of such failure levels.

No independent signature-injectivity, abstract age-witness or
generation-rank hypothesis is added.  The remaining task is to prove
that the manuscript's selected I3 levels are exactly (or contained
in) these failed corrected-B3 stages in the global construction.
-/

namespace SuccessorTree.V10

/-- Extract the actual forbidden pattern, including the non-neutral
singleton case, from the normalized forbidden-family entry. -/
def NormalizedForbidden.signaturePattern
    {db du dd : Nat} (bad : NormalizedForbidden db du dd) :
    ForbiddenAtomicPattern bad.patternCard db du dd := by
  cases bad with
  | singleton P hNonNeutral => exact P
  | nontrivial t P ht hIrred => exact P

/-- Avoidance of a normalized forbidden entry is exactly the
nonexistence of an induced copy of its underlying pattern. -/
theorem NormalizedForbidden.signaturePattern_avoids_iff
    {db du dd : Nat}
    (bad : NormalizedForbidden db du dd)
    (W : AgeTestModel db du dd) :
    bad.Avoids W ↔
      ¬ ∃ e : Fin bad.patternCard → Nat,
        W.Realizes bad.signaturePattern e := by
  cases bad with
  | singleton P hNonNeutral => rfl
  | nontrivial t P ht hIrred => rfl

/-- A violation yields an actual induced copy; no positive-only
homomorphism or extra copy hypothesis is needed. -/
theorem NormalizedForbidden.signaturePattern_copy_of_violation
    {db du dd : Nat}
    (bad : NormalizedForbidden db du dd)
    (W : AgeTestModel db du dd)
    (h : ¬ bad.Avoids W) :
    ∃ e : Fin bad.patternCard → Nat,
      W.Realizes bad.signaturePattern e := by
  classical
  apply not_not.mp
  intro hNoCopy
  exact h ((bad.signaturePattern_avoids_iff W).2 hNoCopy)

/-- A failed corrected B3 at a genuine eligible stage supplies a
FULL indexed signature witness using the actual forbidden-family
index and the fixed original-name pool.  This includes all negative
L atoms on the upper crossing, the genuine finite age witness, and
avoidance of the copied forbidden pattern after deletion. -/
theorem stagePool_failedB3_has_signature_witness
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hEll : ell < A.size)
    (original : Fin M → Fin A.size)
    (hFailure :
      ¬ (stagePoolPrescribedData A ell original).CorrectedB3 family) :
    Nonempty (I3OriginalSignatureWitness
      (fun i : Fin family.length => (family.get i).patternCard)
      (fun i => (family.get i).signaturePattern)
      A.L (fun v => (original v).val) ell) := by
  classical
  obtain ⟨S0,hS0,W,hFinite,hSocle,hDelete,hUpper,bad,hMember,hBad⟩ :=
    stagePool_failedCorrectedB3_has_eligible_original_witness
      family A ell hEll original hFailure
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
  obtain ⟨v,_hCut,hType⟩ :=
    hUpper (e a) (hCopy.2.1 a) hAbove
  exact ⟨v,hType⟩

/-- The precise finite R(M) bound for ALL selected levels at which
the actual stage map fails corrected B3.  Here selection/failure
is a genuine hypothesis about the author's global construction;
the finite witnesses, signatures, injectivity and counting are
all derived rather than assumed.  Different cuts use eligible
SUBSETS of the SAME fixed original pool Fin M. -/
theorem stagePool_B3_failure_levels_card_le_signature_capacity
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (original : Fin M → Fin A.size)
    (levels : Finset Nat)
    (hFailures : ∀ ell, ell ∈ levels →
      ell < A.size ∧
      ¬ (stagePoolPrescribedData A ell original).CorrectedB3 family) :
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
    exact stagePool_failedB3_has_signature_witness
      family A ell hCut original hFailed
  exact i3SelectedLevels_card_le_signature_capacity
    (fun i : Fin family.length => (family.get i).patternCard)
    (fun i => (family.get i).signaturePattern)
    A.L (fun v => (original v).val)
    levels hInitial hWitness

end SuccessorTree.V10

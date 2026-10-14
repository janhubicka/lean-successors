import SuccessorTree.V10.ChosenAgeSignatures
import SuccessorTree.V10.Counting
import Mathlib.Tactic

/-!
# The finite signature code and injection used in Proposition 6.44

The manuscript's condition I3 selects a level only if a finite
forbidden L-age witness exists. Each such witness carries a
forbidden-family member and a map whose values are either bottom
(for the lower part of its copy) or an actual ambient original
(for the upper part).

The checked chosen-signature collision theorem proves that two
different tested levels with the same forbidden pattern cannot
carry the same original-valued signature. This module packages
that conclusion as an injective code into
  Σ i : Fin familySize, Fin (forbiddenSize i) → Option (Fin M),
whose cardinal is exactly
  Σ_i (M+1)^(forbiddenSize i) = R(M).

All geometry is explicit in the witness record; in particular
this module does NOT construct the selected I3 witnesses or prove
the generation estimate. It removes *signature injectivity* as a
standalone counting hypothesis once the genuine finite witnesses
are available, preserving the axioms of the frozen v10 manuscript.
-/

namespace SuccessorTree.V10

/-- One actual finite ordered forbidden-copy witness, with common
ambient initial L-socle, a forbidden-free deletion and original
labels on its upper vertices. The pattern belongs to an indexed
finite forbidden family whose sizes are part of the fixed signature.

There is no auxiliary E on W; all types are complete induced L
records, including negative directed, unary and diagonal atoms. -/
structure I3OriginalSignatureWitness
    {k M db du dd : Nat}
    (sizes : Fin k → Nat)
    (patterns : (i : Fin k) → ForbiddenAtomicPattern (sizes i) db du dd)
    (C : AgeTestModel db du dd)
    (original : Fin M → Nat)
    (ell : Nat) where
  familyIndex : Fin k
  W : AgeTestModel db du dd
  e : Fin (sizes familyIndex) → Nat
  finite : W.BoundedCarrier
  copy : W.Realizes (patterns familyIndex) e
  socle : SameInitialL W C ell
  deleteAvoids : ¬ ∃ f : Fin (sizes familyIndex) → Nat,
    (W.withoutVertex ell).Realizes (patterns familyIndex) f
  upperNames : ∀ a : Fin (sizes familyIndex), ell < e a →
    ∃ v : Fin M,
      RelationalPrefixType.ofAgeModel W (ell + 1) (e a) =
        RelationalPrefixType.ofAgeModel C (ell + 1) (original v)

/-- The actual code (F,f) of Observation 6.52: the forbidden-family
index is retained and every upper original is named, with bottom
at exactly the copy coordinates at or below ell. -/
noncomputable def I3OriginalSignatureWitness.code
    {k M db du dd : Nat}
    {sizes : Fin k → Nat}
    {patterns : (i : Fin k) → ForbiddenAtomicPattern (sizes i) db du dd}
    {C : AgeTestModel db du dd}
    {original : Fin M → Nat} {ell : Nat}
    (w : I3OriginalSignatureWitness sizes patterns C original ell) :
    (Σ i : Fin k, Fin (sizes i) → Option (Fin M)) :=
  ⟨w.familyIndex,
    chosenAgeSignature C w.W original ell w.e w.upperNames⟩

/-- A genuine finite forbidden age witness cannot share the exact
code with another witness at a strictly greater selected level.
No standalone signature-injectivity or full-type-equality
hypothesis is assumed: the code's chosen original labels supply
the type equations and the checked splice produces a contradiction. -/
theorem I3OriginalSignatureWitness.code_ne_of_lt
    {k M db du dd : Nat}
    (sizes : Fin k → Nat)
    (patterns : (i : Fin k) → ForbiddenAtomicPattern (sizes i) db du dd)
    (C : AgeTestModel db du dd)
    (original : Fin M → Nat)
    (ell0 ell1 : Nat) (hLevels : ell0 < ell1)
    (hInitial : ∀ x, x ≤ ell1 → x ∈ C.carrier)
    (w0 : I3OriginalSignatureWitness sizes patterns C original ell0)
    (w1 : I3OriginalSignatureWitness sizes patterns C original ell1) :
    w0.code ≠ w1.code := by
  classical
  intro hEq
  rcases w0 with ⟨i0,W0,e0,hFin0,hCopy0,hSocle0,hDel0,hOrig0⟩
  rcases w1 with ⟨i1,W1,e1,hFin1,hCopy1,hSocle1,hDel1,hOrig1⟩
  change
    (⟨i0,chosenAgeSignature C W0 original ell0 e0 hOrig0⟩ :
       Σ i : Fin k, Fin (sizes i) → Option (Fin M)) =
    ⟨i1,chosenAgeSignature C W1 original ell1 e1 hOrig1⟩ at hEq
  have hIndex : i0 = i1 := congrArg Sigma.fst hEq
  subst i1
  have hSame :
      chosenAgeSignature C W0 original ell0 e0 hOrig0 =
      chosenAgeSignature C W1 original ell1 e1 hOrig1 := by
    exact eq_of_heq (Sigma.mk.inj_iff.mp hEq).2
  exact chosenAgeSignature_distinct_of_ambient_age_witnesses
    (patterns i0) C W0 W1 original e0 e1 ell0 ell1
    hLevels hCopy0 hCopy1 hInitial hSocle0 hSocle1
    hOrig0 hOrig1 hDel1 hSame

/-- The I3-selected levels have at most R(M) members once each level
has its actual finite original-labelled witness from a common ambient
structure, with the ambient initial socle present through each
tested coordinate. No separate hSignatureInjective is required.

The arities are exactly those of the indexed forbidden family:
R(M) = Σ_i (M+1)^(sizes i). This is the cardinal term appearing
in the frozen manuscript's descending generation recurrence. -/
theorem i3SelectedLevels_card_le_signature_capacity
    {k M db du dd : Nat}
    (sizes : Fin k → Nat)
    (patterns : (i : Fin k) → ForbiddenAtomicPattern (sizes i) db du dd)
    (C : AgeTestModel db du dd)
    (original : Fin M → Nat)
    (levels : Finset Nat)
    (hInitial : ∀ ell, ell ∈ levels → ∀ x, x ≤ ell → x ∈ C.carrier)
    (hWitness : ∀ ell, ell ∈ levels →
      Nonempty (I3OriginalSignatureWitness sizes patterns C original ell)) :
    levels.card ≤ ageSignatureCapacity sizes M := by
  classical
  by_cases hNonempty : levels.Nonempty
  · obtain ⟨first,hFirst⟩ := hNonempty
    let witness (ell : Nat) (h : ell ∈ levels) :
        I3OriginalSignatureWitness sizes patterns C original ell :=
      Classical.choice (hWitness ell h)
    let defaultCode :
        (Σ i : Fin k, Fin (sizes i) → Option (Fin M)) :=
      (witness first hFirst).code
    let signature (ell : Nat) :
        (Σ i : Fin k, Fin (sizes i) → Option (Fin M)) :=
      if h : ell ∈ levels then (witness ell h).code else defaultCode
    have hInjective : Set.InjOn signature (levels : Set Nat) := by
      intro a ha b hb heq
      have haMem : a ∈ levels := Finset.mem_coe.mp ha
      have hbMem : b ∈ levels := Finset.mem_coe.mp hb
      have hSig :
          (witness a haMem).code = (witness b hbMem).code := by
        simpa only [signature, dif_pos haMem, dif_pos hbMem] using heq
      by_contra hne
      rcases lt_or_gt_of_ne hne with hab | hba
      · exact (I3OriginalSignatureWitness.code_ne_of_lt
          sizes patterns C original a b hab
          (hInitial b hbMem)
          (witness a haMem) (witness b hbMem)) hSig
      · exact (I3OriginalSignatureWitness.code_ne_of_lt
          sizes patterns C original b a hba
          (hInitial a haMem)
          (witness b hbMem) (witness a haMem)) hSig.symm
    have hImage :
        (levels.image signature).card = levels.card :=
      Finset.card_image_iff.mpr hInjective
    calc
      levels.card = (levels.image signature).card := hImage.symm
      _ ≤ (Finset.univ :
            Finset (Σ i : Fin k, Fin (sizes i) → Option (Fin M))).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = ageSignatureCapacity sizes M := by
          simp [ageSignatureCapacity, Fintype.card_sigma,
            Fintype.card_fun]
  · have hEmpty : levels = ∅ := Finset.not_nonempty_iff_eq_empty.mp hNonempty
    simp [hEmpty, ageSignatureCapacity]

end SuccessorTree.V10

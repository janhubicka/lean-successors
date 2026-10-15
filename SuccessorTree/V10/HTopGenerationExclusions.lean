import SuccessorTree.V10.I3ActualHigherSignature
import SuccessorTree.V10.HClosureCharge
import Mathlib.Tactic

/-!
# V10: no new I2 meet and no failed B3 at the highest generation

The base case a_k=q+1 of Proposition 6.44 cannot be justified
only by counting the q+1 initial seed nodes. One must show
there are no new top-generation events.

A strict closure meet at a real top-generation coordinate would
give a NumericHMeetCharge of generation k. Such a charge has an
original of generation n>k while every original generation is
at most k, contradiction.

For I3, take the genuine finite L-only age witness of failed
corrected B3, preserve its selected original upper labels and
apply the full forbidden-copy relocation theorem. The last
lower generation is r-1<k. Thus the tested real coordinate
cannot have generation k by injectivity of iota.

The actual top-generation node (I1) classification and run
base a_k<=q+1 are composed with these two exclusions later.
-/

namespace SuccessorTree.V10

/-- In the actual finite H closure, a genuinely nontrivial meet
cannot have real generation k. No arbitrary charge function is
assumed: the numerical H meet charge follows from the existing
complete Kpt prefixes of the represented closure. -/
theorem numericH_no_strict_closure_meet_at_top_generation
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat) (hk : 0 < k)
    (U : Set (Fin N)) (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family (finiteNumericH K k N)
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK) U)
    (s t : AdmissibleKptNode family)
    (hs : s ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X)
    (ht : t ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X)
    (hSame : SMTree.Envelope.SameComponent s t)
    (hStrictS : LevelTree.meet s t ≠ s)
    (hStrictT : LevelTree.meet s t ≠ t)
    (p : Nat)
    (hLevel : LevelTree.lev (LevelTree.meet s t) =
      hPosition k p k) : False := by
  obtain ⟨v,w,_hv,_hw,hCharge⟩ :=
    forbiddenFreeH_closure_meet_charge
      family K hCarrier k N hk hAvoidK U I X hX
      s t hs ht hSame hStrictS hStrictT p k hk le_rfl hLevel
  rcases numericHMeetCharge_higher_original
      K.binary k v.val w.val p k hCharge with hv | hw
  · obtain ⟨_i,n,hn,_hRep,hHigher,_hFirst⟩ := hv
    omega
  · obtain ⟨_i,n,hn,_hRep,hHigher,_hFirst⟩ := hw
    omega

/-- No selected ambient-original partial map can fail the
corrected B3 test at a real coordinate in top generation k.
The proof uses the actual L-only failed test, not an auxiliary
E-expansion of its finite forbidden age witness. -/
theorem numericH_top_generation_selectedB3_holds
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N ell p : Nat) (hk : 0 < k)
    (hEll : ell < N)
    (hTop : ell = hPosition k p k)
    (original : Fin M → Fin N)
    (Selected : Fin M → Prop)
    (hFamilyBound : ∀ bad, bad ∈ family →
      bad.patternCard ≤ k+1) :
    (selectedStagePoolPrescribedData
      (finiteNumericH K k N) ell original Selected).CorrectedB3
      family := by
  classical
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  have hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  by_contra hFailure
  obtain ⟨_S0,_hS0,W,_hFinite,hSocle,hDelete,hUpper,bad,hMem,hBad⟩ :=
    selectedStagePool_failedCorrectedB3_has_selected_original_witness
      family A ell hEll original Selected hFailure
  obtain ⟨e,r,hr,hrt,hrk,hIrred,hCopy,hDeleteP,hLast,
    _hLow,hHigh⟩ :=
    normalizedForbidden_bounded_signature_cut
      (finiteNumericHL K k N) W ell k bad
      (hFamilyBound bad hMem) hSocle
      (hAvoidA bad hMem) (hDelete bad hMem) hBad
  have hUpperNamed :
      ∀ b : Fin bad.patternCard, r ≤ b.val →
        ∃ orig : Nat, ell < orig ∧
          RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
            RelationalPrefixType.ofAgeModel
              (finiteNumericHL K k N) (ell+1) orig := by
    intro b hb
    have hAbove : ell < e b := (hHigh b).1 hb
    obtain ⟨v,_hSelected,hCut,hType⟩ :=
      hUpper (e b) (hCopy.2.1 b) hAbove
    have hLe : A.freeLevel (original v).val ≤ (original v).val :=
      A.freeLevel_le (original v).val
    have hAfter : ell < (original v).val := by omega
    exact ⟨(original v).val,hAfter,hType⟩
  obtain ⟨i,hGeneration,_hUpperGen⟩ :=
    numericI3_actual_witness_generation_conclusions
      K k N ell r hr hrt hrk W hSocle
      bad.signaturePattern hIrred e hCopy
      hDeleteP hLast hUpperNamed
  have hPositionEq :
      hPosition k p k = hPosition k i (r-1) :=
    hTop.symm.trans hGeneration
  obtain ⟨_hi,hGenEq⟩ :=
    hPosition_injective_bounded k p k i (r-1)
      le_rfl (by omega) hPositionEq
  omega

end SuccessorTree.V10

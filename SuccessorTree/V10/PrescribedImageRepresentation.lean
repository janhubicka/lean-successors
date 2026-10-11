import SuccessorTree.V10.PrescribedKptSkip
import Mathlib.Tactic

/-!
# Compute the selected matching image in any finite representation

The existential age theorem supplies some valid inserted E cut. The
ordinary-socle uniqueness theorem identifies it with every given valid
cut, so the actual constructor at that cut is forbidden-free. Consequently
the selected matching image may be computed using any source realization,
not only the witness hidden in its choice-based definition.

This adapter is intended for the prefix-replica argument. It does not
assume or assert the predecessor or successor preservation still needed.
-/

namespace SuccessorTree.V10

/-- Corrected B3 gives avoidance for EVERY valid canonical insertion cut.
The cut equality is derived, not supplied as an additional hypothesis. -/
theorem PrescribedBoringData.matching_constructor_avoids_of_valid_cut
    {ell db du dd : Nat} (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (A : EnumeratedPartialStructure db du dd)
    (base : Nat) (S0 : PartialTypeWithE ell db du dd)
    (hS0 : S0 ∈ F.source)
    (hComp : SameOrdinaryAtCut S0 (A.partialTypeAt ell base))
    (hell : ell ≤ A.size) (hPos : 0 < ell)
    (hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hTargetAd : IsAdmissibleRawType family
      (⟨ell+1,F.target S0⟩ : RawPartialTypeNode db du dd))
    (d : Nat) (hValid : ValidNewOrdinaryColumn (F.target S0) d)
    (hd : d ≤ ell) (hGate : d = 0 ∨ d < ell) :
    ∀ bad, bad ∈ family → bad.Avoids
      (prescribedInsertPartial A (F.target S0) d hValid hell hPos hd hGate
        (F.upperIncoming A) (F.upperOutgoing A)).L := by
  obtain ⟨e,he,hGateE,hValidE,hAvoidB,hInsertion,hFree⟩ :=
    F.matching_constructor_of_correctedB3 family hB3 A base S0 hS0
      hComp hell hPos hAvoidA hTargetAd
  have hEq : d = e := lowerInsertedCut_eq_of_sameSocle
    (sameOrdinarySocle_refl (F.target S0)) d e hd he hValid hValidE
  subst e
  exact hAvoidB

/-- Compute the selected matching image in an arbitrary genuine finite
source representation and at any valid canonical inserted cut. -/
theorem PrescribedBoringData.matchingKptImage_raw_eq_of_representation
    {ell db du dd : Nat} (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a : AdmissibleKptNode family) (hlev : ell ≤ a.1.1)
    (hMatch : F.HasCompatibleSource (a.1.2.restrict hlev))
    (A : EnumeratedPartialStructure db du dd) (v : Nat)
    (hv : v < A.size)
    (hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hRawA : a.1 = A.rawTypeAtFree v)
    (S0 : PartialTypeWithE ell db du dd) (hS0 : S0 ∈ F.source)
    (hComp : SameOrdinaryAtCut S0 (A.partialTypeAt ell v))
    (d : Nat) (hell : ell ≤ A.size)
    (hValid : ValidNewOrdinaryColumn (F.target S0) d)
    (hd : d ≤ ell) (hGate : d = 0 ∨ d < ell) :
    (F.matchingKptImage family hB3 hTargets hPos a hlev hMatch).1 =
      (prescribedInsertPartial A (F.target S0) d hValid hell hPos hd hGate
        (F.upperIncoming A) (F.upperOutgoing A)).rawTypeAtFree
          (insertAddress ell v) := by
  let B := prescribedInsertPartial A (F.target S0) d hValid hell hPos hd hGate
    (F.upperIncoming A) (F.upperOutgoing A)
  have hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L :=
    F.matching_constructor_avoids_of_valid_cut family hB3 A v S0 hS0 hComp
      hell hPos hAvoidA (hTargets S0 hS0) d hValid hd hGate
  have hFree : ell ≤ A.freeLevel v := by
    have h := congrArg Sigma.fst hRawA
    omega
  have hEllV : ell ≤ v := hFree.trans (A.freeLevel_le v)
  have hvB : insertAddress ell v < B.size := by
    change insertAddress ell v < A.size+1
    rw [insertAddress_above ell v hEllV]
    omega
  let b : AdmissibleKptNode family :=
    ⟨B.rawTypeAtFree (insertAddress ell v),
      ⟨B,insertAddress ell v,hvB,hAvoidB,rfl⟩⟩
  have hb : F.IsMatchingKptImage family hPos a b :=
    ⟨A,v,S0,d,hell,hValid,hd,hGate,hv,hAvoidA,hRawA,hS0,hComp,rfl⟩
  exact congrArg Subtype.val
    (F.matchingKptImage_eq_of_isImage family hB3 hTargets hPos a hlev hMatch b hb)

end SuccessorTree.V10

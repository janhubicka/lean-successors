import SuccessorTree.V10.PrescribedB3Finite
import SuccessorTree.V10.PrescribedAdmissibleCut
import Mathlib.Tactic

/-!
# Existence of a genuine F-free matching-socle prescribed insertion

The previous theorem built a finite prescribed L+ insertion once one
actual forbidden-free witness W of f(S0), and its canonical E-cut d, had
been named. Here BOTH are extracted from the original hypothesis that
f(S0) is a genuinely admissible level-(ell+1) Kpt node.

No extra E-column or age-avoidance hypotheses are required. The real
partial-structure witness supplies a valid new-ordinary E cut and the
strict d=0 or d<ell gate. The f-target's L+ record supplies its
identification with the witness. The finite B3 no-age-change assumption
for that common socle then makes the matching insertion forbidden-free.

We retain the exact original L-atom embedding and transported E-cuts in
the conclusion, so this lemma is suitable for subsequent uniform type
insertion. It is still a FINITE construction for one A and one matching
S0, not yet the global Kpt ShapeMap.
-/

namespace SuccessorTree.V10

/-- Every genuine prescribed admissible Kpt output and the B3 local
no-age-change assumption provide a real forbidden-free finite insertion,
with full old L embedding and canonical transport of each old free cut.
Both the structural E validity and forbidden age are derived. -/
theorem PrescribedBoringData.matching_prescribed_insertion_exists
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (base : Nat)
    (S0 : PartialTypeWithE ell db du dd)
    (hS0 : S0 ∈ F.source)
    (hComp : SameOrdinaryAtCut S0 (A.partialTypeAt ell base))
    (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hTargetAd : IsAdmissibleRawType family
      (⟨ell+1, F.target S0⟩ : RawPartialTypeNode db du dd))
    (hB3 : ∀ (W : EnumeratedPartialStructure db du dd) (w : Nat),
      F.target S0 = W.partialTypeAt (ell+1) w →
      (∀ bad, bad ∈ family → bad.Avoids W.L) →
      CommonSocleAgeTest family W.L ell F.PrescribedUpperLType) :
    ∃ B : EnumeratedPartialStructure db du dd,
      (∀ bad, bad ∈ family → bad.Avoids B.L) ∧
      IsLInsertion A B ell ∧
      (∀ u, u < A.size →
        B.freeLevel (insertAddress ell u) =
          if A.freeLevel u < ell then A.freeLevel u
          else A.freeLevel u + 1) := by
  let b : AdmissibleKptNode family :=
    ⟨⟨ell+1, F.target S0⟩, hTargetAd⟩
  have hb : b.1.1 = ell+1 := rfl
  obtain ⟨d,hd,hGate,hValid⟩ :=
    admissiblePrescribedCut_exists family ell b hb
  have hValidQ : ValidNewOrdinaryColumn (F.target S0) d := by
    change ValidNewOrdinaryColumn
      (admissiblePrescribedRecord ell b hb) d at hValid
    simpa [admissiblePrescribedRecord, b] using hValid
  obtain ⟨W,w,hw,hAvoidW,hRaw⟩ := hTargetAd
  have hFreeW : W.freeLevel w = ell + 1 := by
    have hh := congrArg Sigma.fst hRaw
    change ell + 1 = W.freeLevel w at hh
    omega
  have hWsize : ell < W.size := by
    have hc := W.freeLevel_le w
    omega
  have hWtype : F.target S0 = W.partialTypeAt (ell + 1) w := by
    have hPair :
        (⟨ell+1,F.target S0⟩ : RawPartialTypeNode db du dd) =
        (⟨ell+1,W.partialTypeAt (ell+1) w⟩ :
          RawPartialTypeNode db du dd) := by
      calc
        (⟨ell+1,F.target S0⟩ : RawPartialTypeNode db du dd) =
          W.rawTypeAtFree w := hRaw
        _ = (⟨ell+1,W.partialTypeAt (ell+1) w⟩ :
          RawPartialTypeNode db du dd) := by
          change
            (⟨W.freeLevel w,
               W.partialTypeAt (W.freeLevel w) w⟩ :
              RawPartialTypeNode db du dd) =
            (⟨ell+1,W.partialTypeAt (ell+1) w⟩ :
              RawPartialTypeNode db du dd)
          rw [hFreeW]
    exact eq_of_heq (Sigma.mk.inj_iff.mp hPair).2
  let B := prescribedInsertPartial A (F.target S0) d hValidQ
    hell hellPos hd hGate (F.upperIncoming A) (F.upperOutgoing A)
  have hAge : CommonSocleAgeTest family W.L ell
      F.PrescribedUpperLType :=
    hB3 W w hWtype hAvoidW
  have hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L :=
    F.prescribedInsertion_avoids_of_witness family A W base w S0 hS0
      hComp hell hellPos hAvoidA hAvoidW hWsize hWtype d hValidQ
      hd hGate hAge
  refine ⟨B,hAvoidB,?_,?_⟩
  · exact prescribedInsertPartial_isLInsertion A (F.target S0)
      d hValidQ hell hellPos hd hGate
      (F.upperIncoming A) (F.upperOutgoing A)
  · intro u hu
    exact prescribedInsertPartial_old_freeLevel A (F.target S0)
      d hValidQ hell hellPos hd hGate
      (F.upperIncoming A) (F.upperOutgoing A) u hu

end SuccessorTree.V10

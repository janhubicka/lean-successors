import SuccessorTree.V10.NonedgePaddingFullTypes
import SuccessorTree.V10.PrescribedBoringData
import Mathlib.Tactic

/-!
# Simultaneous padded realization of a selected family of genuine source types

Only the finitely many selected upper slots carry prescribed Kpt types.
The remaining dense source slots may be neutral placeholders: no spurious
admissibility or compatibility obligation is imposed on them.

The ordinary L model already retains *all* upper--upper relations. The
common initial E socle is obtained from one genuine source type and is
then shared by every selected type. No E structure on the original L
model is assumed.
-/

namespace SuccessorTree.V10

/-- If an L-only finite source model has the complete L-types of a
selected family of mutually compatible admissible source types, the
whole family is realized in ONE admissible nonedge-padded witness.
The choice of E-socle comes from the single anchor type, whereas
unselected vertices require no admissible type at all. -/
theorem compatibleSelectedTypes_joint_padded
    {n db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (anchor : PartialTypeWithE n db du dd)
    (hAnchor : IsAdmissibleRawType family
      (⟨n,anchor⟩ : RawPartialTypeNode db du dd))
    (A : AgeTestModel db du dd) (N : Nat)
    (hn : n ≤ N)
    (hCarrier : ∀ x, x ∈ A.carrier ↔ x < N)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A)
    (hInitial : ∀ (x y : Nat) (hx : x < n) (hy : y < n)
      (t : Fin db), A.binary x y t =
        anchor.lReduct.binary (some ⟨x,hx⟩) (some ⟨y,hy⟩) t)
    (selected : Nat → Prop)
    (T : Nat → PartialTypeWithE n db du dd)
    (hAd : ∀ i, n ≤ i → i < N → selected i →
      IsAdmissibleRawType family
        (⟨n,T i⟩ : RawPartialTypeNode db du dd))
    (hComp : ∀ i, n ≤ i → i < N → selected i →
      SameOrdinaryAtCut anchor (T i))
    (hType : ∀ i, n ≤ i → i < N → selected i →
      RelationalPrefixType.ofAgeModel A n i = (T i).lReduct) :
    ∃ B : EnumeratedPartialStructure db du dd,
      (∀ bad, bad ∈ family → bad.Avoids B.L) ∧
      B.size = NonedgePadding.size n N ∧
      ∀ i, n ≤ i → i < N → selected i →
        B.partialTypeAt n (NonedgePadding.address n i) = T i := by
  obtain ⟨C,v,hv,_hAvoidC,hRaw⟩ := hAnchor
  have hCut : n = C.freeLevel v := congrArg Sigma.fst hRaw
  have hC : n ≤ C.size := by
    have hFree := C.freeLevel_le v
    omega
  have hAnchorType : anchor = C.partialTypeAt n v := by
    have hRaw' :
        (⟨n,anchor⟩ : RawPartialTypeNode db du dd) =
          (⟨n,C.partialTypeAt n v⟩ : RawPartialTypeNode db du dd) := by
      calc
        (⟨n,anchor⟩ : RawPartialTypeNode db du dd) =
          C.rawTypeAtFree v := hRaw
        _ = (⟨n,C.partialTypeAt n v⟩ : RawPartialTypeNode db du dd) := by
          change (⟨C.freeLevel v,
            C.partialTypeAt (C.freeLevel v) v⟩ :
              RawPartialTypeNode db du dd) = _
          rw [← hCut]
    exact eq_of_heq (Sigma.mk.inj_iff.mp hRaw').2
  have hSocle : ∀ x y, x < n → y < n → ∀ t : Fin db,
      A.binary x y t = C.L.binary x y t := by
    intro x y hx hy t
    rw [hInitial x y hx hy t,hAnchorType]
    rfl
  let B := NonedgePadding.partialStructure C A n N hC hSocle
  refine ⟨B,?_,rfl,?_⟩
  · intro bad hbad
    exact NonedgePadding.partial_preserves_avoidance C A n N
      hC hSocle hn hCarrier bad (hAvoid bad hbad)
  · intro i hni hi hsel
    have hE : ∀ j k : Fin n,
        C.E j.val k.val = (T i).eRelation (some j) (some k) := by
      intro j k
      calc
        C.E j.val k.val = anchor.eRelation (some j) (some k) := by
          rw [hAnchorType]
          rfl
        _ = (T i).eRelation (some j) (some k) :=
          (hComp i hni hi hsel).2.2.2 j k
    exact NonedgePadding.upper_type_eq_prescribed family C A n N
      hC hSocle i hi hni (T i) (hAd i hni hi hsel)
      (hType i hni hi hsel) hE

end SuccessorTree.V10

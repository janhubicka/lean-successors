import SuccessorTree.V10.NonedgePaddingTypes
import Mathlib.Tactic

/-!
# Simultaneous realization of prescribed full source types by non-edge padding

The input types share one specified ordinary E-socle. They may have
arbitrary different singleton facts and links to that socle. Every
upper-upper L-relation is retained, and the neutral fillers introduce
no forbidden copy. The resulting SINGLE forbidden-free partial
structure realizes all the full prescribed L+ records simultaneously.

Compatibility of the prescribed ordinary E-socles is retained explicitly;
no E-expansion on the original consecutive upper addresses is assumed.
-/

namespace SuccessorTree.V10
namespace NonedgePadding

/-- An admissible record has all type-vertex E-incidences forced by
its level. The ordinary E-socle is the only variable part of E. -/
theorem admissible_type_E {n db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (T : PartialTypeWithE n db du dd)
    (hAd : IsAdmissibleRawType family
      (⟨n,T⟩ : RawPartialTypeNode db du dd)) :
    (∀ j : Fin n, T.eRelation (some j) none = true) ∧
    (∀ j : Fin n, T.eRelation none (some j) = false) ∧
    T.eRelation none none = false := by
  obtain ⟨W,w,_hw,_hAvoid,hRaw⟩ := hAd
  have hCut : n = W.freeLevel w := congrArg Sigma.fst hRaw
  have hPair : (⟨n,T⟩ : RawPartialTypeNode db du dd) =
      (⟨W.freeLevel w,W.partialTypeAt (W.freeLevel w) w⟩ :
        RawPartialTypeNode db du dd) := hRaw
  have hHEq := (Sigma.mk.inj_iff.mp hPair).2
  rw [←hCut] at hHEq
  have hT : T = W.partialTypeAt n w := eq_of_heq hHEq
  rw [hT]
  exact ⟨W.partialTypeAt_fullESocle n w (by omega),
    W.partialTypeAt_no_reverseE n w (by omega),
    W.partialTypeAt_no_typeE_loop n w⟩

/-- One padded witness realizes every prescribed compatible upper
type as its COMPLETE L+ record, not just as its L-reduct. -/
theorem upper_type_eq_prescribed {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (C : EnumeratedPartialStructure db du dd)
    (A : AgeTestModel db du dd) (n N : Nat)
    (hC : n ≤ C.size)
    (hSocle : ∀ x y, x < n → y < n → ∀ t : Fin db,
      A.binary x y t = C.L.binary x y t)
    (i : Nat) (hi : i < N) (hni : n ≤ i)
    (T : PartialTypeWithE n db du dd)
    (hAd : IsAdmissibleRawType family
      (⟨n,T⟩ : RawPartialTypeNode db du dd))
    (hL : RelationalPrefixType.ofAgeModel A n i = T.lReduct)
    (hE : ∀ j k : Fin n, C.E j.val k.val = T.eRelation (some j) (some k)) :
    (partialStructure C A n N hC hSocle).partialTypeAt n (address n i) = T := by
  let B := partialStructure C A n N hC hSocle
  have hReach : n ≤ B.freeLevel (address n i) :=
    upper_cut_le_free C A n N hC hSocle i hi hni
  have hTE := admissible_type_E family T hAd
  apply PartialTypeWithE.eq_of_atoms
  · exact (upper_type_lReduct C A n N hC hSocle i).trans hL
  · intro x y
    cases x with
    | none =>
      cases y with
      | none => exact (B.partialTypeAt_no_typeE_loop n (address n i)).trans hTE.2.2.symm
      | some k => exact (B.partialTypeAt_no_reverseE n (address n i) hReach k).trans
          (hTE.2.1 k).symm
    | some j =>
      cases y with
      | none => exact (B.partialTypeAt_fullESocle n (address n i) hReach j).trans
          (hTE.1 j).symm
      | some k =>
        change B.E j.val k.val = T.eRelation (some j) (some k)
        exact (partial_E_socle C A n N hC hSocle j.val k.val k.isLt).trans (hE j k)

/-- Every finite compatible family is realized simultaneously in the
SAME padded forbidden-free partial structure. Upper-upper relations
are the originally prescribed ones, not newly chosen non-edges. -/
theorem simultaneous_full_types {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (C : EnumeratedPartialStructure db du dd)
    (A : AgeTestModel db du dd) (n N : Nat)
    (hC : n ≤ C.size)
    (hSocle : ∀ x y, x < n → y < n → ∀ t : Fin db,
      A.binary x y t = C.L.binary x y t)
    (hn : n ≤ N) (hCarrier : ∀ x, x ∈ A.carrier ↔ x < N)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A)
    (T : Nat → PartialTypeWithE n db du dd)
    (hAd : ∀ i, n ≤ i → i < N → IsAdmissibleRawType family
      (⟨n,T i⟩ : RawPartialTypeNode db du dd))
    (hL : ∀ i, n ≤ i → i < N →
      RelationalPrefixType.ofAgeModel A n i = (T i).lReduct)
    (hE : ∀ i, n ≤ i → i < N → ∀ j k : Fin n,
      C.E j.val k.val = (T i).eRelation (some j) (some k)) :
    (∀ bad, bad ∈ family →
      bad.Avoids (partialStructure C A n N hC hSocle).L) ∧
    ∀ i, n ≤ i → i < N →
      (partialStructure C A n N hC hSocle).partialTypeAt n (address n i) = T i := by
  constructor
  · intro bad hbad
    exact partial_preserves_avoidance C A n N hC hSocle hn hCarrier bad (hAvoid bad hbad)
  · intro i hni hi
    exact upper_type_eq_prescribed family C A n N hC hSocle i hi hni (T i)
      (hAd i hni hi) (hL i hni hi) (hE i hni hi)

end NonedgePadding
end SuccessorTree.V10

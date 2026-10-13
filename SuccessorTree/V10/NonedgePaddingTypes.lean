import SuccessorTree.V10.NonedgePadding
import Mathlib.Tactic

/-!
# The padded L-witness supplies genuine admissible source types

The non-edge padding leaves the entire L-type over the original
initial socle unchanged. Its upper E-columns cover that socle, so
these records are actual prefixes of admissible Kpt nodes, not
merely arbitrary Boolean records. This is a finite source-side
statement and does not assume any property of a map F.
-/

namespace SuccessorTree.V10
namespace NonedgePadding

/-- Decoding an upper type coordinate commutes with padding, since
padding fixes every coordinate of the initial socle. -/
theorem prefix_index_address (n i : Nat) (x : Option (Fin n)) :
    prefixVertexIndex (address n i) x =
      address n (prefixVertexIndex i x) := by
  cases x with
  | none => rfl
  | some x => simp [prefixVertexIndex,address,x.isLt]

/-- All positive and negative L-atoms of every upper type are retained
literally over the unchanged initial socle. -/
theorem model_upper_type {db du dd : Nat}
    (A : AgeTestModel db du dd) (n N i : Nat) :
    RelationalPrefixType.ofAgeModel (model A n N) n (address n i) =
      RelationalPrefixType.ofAgeModel A n i := by
  apply RelationalPrefixType.eq_of_atoms
  · intro x y t
    simp [RelationalPrefixType.ofAgeModel,model,
      prefix_index_address,address_real,project_address]
  · intro x t
    simp [RelationalPrefixType.ofAgeModel,model,
      prefix_index_address,address_real,project_address]
  · intro x t
    simp [RelationalPrefixType.ofAgeModel,model,
      prefix_index_address,address_real,project_address]

/-- Padding supplies the E-incidences needed to regard the original
cut n as a genuine type cut of every real upper vertex. -/
theorem upper_cut_le_free {db du dd : Nat}
    (C : EnumeratedPartialStructure db du dd)
    (A : AgeTestModel db du dd) (n N : Nat)
    (hC : n ≤ C.size)
    (hSocle : ∀ x y, x < n → y < n → ∀ t : Fin db,
      A.binary x y t = C.L.binary x y t)
    (i : Nat) (hi : i < N) (hni : n ≤ i) :
    n ≤ (partialStructure C A n N hC hSocle).freeLevel (address n i) := by
  by_cases hn : n = 0
  · simp [hn]
  · have hE := partial_upper_full_socle C A n N hC hSocle
      i (n-1) hi hni (by omega)
    have hlt :=
      ((partialStructure C A n N hC hSocle).E_iff_freeLevel
        (n-1) (address n i)).1 hE
    omega

/-- The padded witness gives an admissible Kpt node at exactly the
original cut, not just a forbidden-free ordinary L-structure. -/
theorem upper_type_admissible {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (C : EnumeratedPartialStructure db du dd)
    (A : AgeTestModel db du dd) (n N : Nat)
    (hC : n ≤ C.size)
    (hSocle : ∀ x y, x < n → y < n → ∀ t : Fin db,
      A.binary x y t = C.L.binary x y t)
    (hn : n ≤ N) (hCarrier : ∀ x, x ∈ A.carrier ↔ x < N)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A)
    (i : Nat) (hi : i < N) (hni : n ≤ i) :
    IsAdmissibleRawType family
      (⟨n,(partialStructure C A n N hC hSocle).partialTypeAt
        n (address n i)⟩ : RawPartialTypeNode db du dd) := by
  let B := partialStructure C A n N hC hSocle
  have hAd : IsAdmissibleRawType family (B.rawTypeAtFree (address n i)) := by
    refine ⟨B,address n i,address_lt_size n N i hi,?_,rfl⟩
    intro bad hbad
    exact partial_preserves_avoidance C A n N hC hSocle
      hn hCarrier bad (hAvoid bad hbad)
  have hCut : n ≤ B.freeLevel (address n i) :=
    upper_cut_le_free C A n N hC hSocle i hi hni
  have hPrefix := admissibleRawType_closed_under_prefix family hAd n hCut
  change IsAdmissibleRawType family
    (⟨n,(B.partialTypeAt (B.freeLevel (address n i)) (address n i)).restrict
      hCut⟩ : RawPartialTypeNode db du dd) at hPrefix
  rw [B.partialTypeAt_restrict n (B.freeLevel (address n i))
    (address n i) hCut] at hPrefix
  exact hPrefix

/-- This is the exact L-reduct of the admissible node just constructed;
no singleton, directed atom, negative atom or socle relation is lost. -/
theorem upper_type_lReduct {db du dd : Nat}
    (C : EnumeratedPartialStructure db du dd)
    (A : AgeTestModel db du dd) (n N : Nat)
    (hC : n ≤ C.size)
    (hSocle : ∀ x y, x < n → y < n → ∀ t : Fin db,
      A.binary x y t = C.L.binary x y t)
    (i : Nat) :
    ((partialStructure C A n N hC hSocle).partialTypeAt
      n (address n i)).lReduct = RelationalPrefixType.ofAgeModel A n i :=
  model_upper_type A n N i

end NonedgePadding
end SuccessorTree.V10

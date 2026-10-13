import SuccessorTree.V10.M2TwoTypeLTypes
import SuccessorTree.V10.NonedgePaddingFullTypes
import Mathlib.Tactic

/-!
# Joint source witness for two compatible admissible types

The entire upper-upper L record is retained in a finite forbidden-free
free amalgam; only *afterwards* nonedge padding adds E and realizes both
complete source types in one admissible partial structure.
-/

namespace SuccessorTree.V10

/-- Add the common ordinary E socle and pad the two new vertices. -/
theorem twoTypeFreeAge_padded_types
    {n db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (T U : PartialTypeWithE n db du dd)
    (hT : IsAdmissibleRawType family
      (⟨n,T⟩ : RawPartialTypeNode db du dd))
    (hU : IsAdmissibleRawType family
      (⟨n,U⟩ : RawPartialTypeNode db du dd))
    (hComp : SameOrdinaryAtCut T U)
    (C : EnumeratedPartialStructure db du dd)
    (hC : n ≤ C.size)
    (hSocle : ∀ x y, x < n → y < n → ∀ t : Fin db,
      (twoTypeFreeAge T U).binary x y t = C.L.binary x y t)
    (hE : ∀ j k : Fin n,
      C.E j.val k.val = T.eRelation (some j) (some k)) :
    ∃ B : EnumeratedPartialStructure db du dd,
      (∀ bad, bad ∈ family → bad.Avoids B.L) ∧
      B.partialTypeAt n (NonedgePadding.address n n) = T ∧
      B.partialTypeAt n (NonedgePadding.address n (n+1)) = U := by
  let A := twoTypeFreeAge T U
  have hN : n ≤ n+2 := by omega
  have hCarrier : ∀ x, x ∈ A.carrier ↔ x < n+2 := by
    intro x
    rfl
  have hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A :=
    twoTypeFreeAge_avoids family T U hT hU hComp
  let B := NonedgePadding.partialStructure C A n (n+2) hC hSocle
  have hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L := by
    intro bad hbad
    exact NonedgePadding.partial_preserves_avoidance C A n (n+2)
      hC hSocle hN hCarrier bad (hAvoidA bad hbad)
  have hFirst : B.partialTypeAt n (NonedgePadding.address n n) = T := by
    exact NonedgePadding.upper_type_eq_prescribed family C A n (n+2)
      hC hSocle n (by omega) (by omega) T hT
      (twoTypeFreeAge_first_type T U) hE
  have hSecond : B.partialTypeAt n
      (NonedgePadding.address n (n+1)) = U := by
    have hE2 : ∀ j k : Fin n,
        C.E j.val k.val = U.eRelation (some j) (some k) := by
      intro j k
      exact (hE j k).trans (hComp.2.2.2 j k)
    exact NonedgePadding.upper_type_eq_prescribed family C A n (n+2)
      hC hSocle (n+1) (by omega) (by omega) U hU
      (twoTypeFreeAge_second_type T U hComp) hE2
  exact ⟨B,hAvoidB,hFirst,hSecond⟩

/-- Two compatible admissible types are jointly realizable in one
forbidden-free partial structure, after introducing neutral nonedges.
No E expansion of the original two-vertex free amalgam is assumed. -/
theorem twoCompatibleTypes_joint_padded
    {n db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (T U : PartialTypeWithE n db du dd)
    (hT : IsAdmissibleRawType family
      (⟨n,T⟩ : RawPartialTypeNode db du dd))
    (hU : IsAdmissibleRawType family
      (⟨n,U⟩ : RawPartialTypeNode db du dd))
    (hComp : SameOrdinaryAtCut T U) :
    ∃ B : EnumeratedPartialStructure db du dd,
      (∀ bad, bad ∈ family → bad.Avoids B.L) ∧
      B.partialTypeAt n (NonedgePadding.address n n) = T ∧
      B.partialTypeAt n (NonedgePadding.address n (n+1)) = U := by
  obtain ⟨C,v,hv,hAvoidC,hRaw⟩ := hT
  have hCut : n = C.freeLevel v := congrArg Sigma.fst hRaw
  have hC : n ≤ C.size := by
    have hnV : n ≤ v := by
      have hfl := C.freeLevel_le v
      omega
    omega
  have hTtype : T = C.partialTypeAt n v := by
    have hRaw' :
        (⟨n,T⟩ : RawPartialTypeNode db du dd) =
          (⟨n,C.partialTypeAt n v⟩ : RawPartialTypeNode db du dd) := by
      calc
        (⟨n,T⟩ : RawPartialTypeNode db du dd) = C.rawTypeAtFree v := hRaw
        _ = (⟨n,C.partialTypeAt n v⟩ : RawPartialTypeNode db du dd) := by
          change (⟨C.freeLevel v,
            C.partialTypeAt (C.freeLevel v) v⟩ : RawPartialTypeNode db du dd) = _
          rw [← hCut]
    exact eq_of_heq (Sigma.mk.inj_iff.mp hRaw').2
  have hSocle : ∀ x y, x < n → y < n → ∀ t : Fin db,
      (twoTypeFreeAge T U).binary x y t = C.L.binary x y t := by
    intro x y hx hy t
    have hxNe : x ≠ n+1 := by omega
    have hyNe : y ≠ n+1 := by omega
    have hxy : (twoTypeFreeAge T U).binary x y t =
        T.lReduct.binary (some (⟨x,hx⟩ : Fin n))
          (some (⟨y,hy⟩ : Fin n)) t := by
      simp [twoTypeFreeAge,typeAgeIndex,hx,hy,hxNe,hyNe]
    rw [hxy,hTtype]
    rfl
  have hE : ∀ j k : Fin n,
      C.E j.val k.val = T.eRelation (some j) (some k) := by
    intro j k
    rw [hTtype]
    rfl
  exact twoTypeFreeAge_padded_types family T U
    ⟨C,v,hv,hAvoidC,hRaw⟩ hU hComp C hC hSocle hE

end SuccessorTree.V10
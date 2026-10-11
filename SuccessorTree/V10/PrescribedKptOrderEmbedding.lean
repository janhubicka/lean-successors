import SuccessorTree.V10.PrescribedKptFullPrefix
import SuccessorTree.V10.PrescribedKptInjective
import SuccessorTree.V10.AdmissibleKptLevelTree
import Mathlib.Tactic

/-!
# Order embedding and exact ancestor transport for prescribed insertion

Use the concrete all-prefix theorem, not an abstract monotonicity premise.
Injectivity and the strictly increasing level map reflect the prefix order.
The actual admissible predecessor at cut n is carried to the predecessor
at cut n below the gap and n+1 at or above it.

The full-prefix implementation is inherited from PR217 rather than copied
from the independently developed alternative in PR216. None of these results
asserts agreement with the prescribed f or a successor-parameter identity.
-/

namespace SuccessorTree.V10

/-- Every transported predecessor level lies below the image's level. -/
theorem PrescribedBoringData.prescribedKptSkip_ancestor_level_bound
    {ell db du dd : Nat} (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell) (a : AdmissibleKptNode family)
    (n : Nat) (hn : n ≤ a.1.1) :
    (if ell ≤ n then n+1 else n) ≤
      (F.prescribedKptSkip family hB3 hTargets hPos a).1.1 := by
  rw [F.prescribedKptSkip_level family hB3 hTargets hPos]
  split_ifs <;> omega

/-- Exact commutation with genuine admissible predecessors, including n=0
and both sides of the skipped level. No choice of representatives remains. -/
theorem PrescribedBoringData.prescribedKptSkip_ancestor
    {ell db du dd : Nat} (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell) (a : AdmissibleKptNode family)
    (n : Nat) (hn : n ≤ a.1.1) :
    F.prescribedKptSkip family hB3 hTargets hPos (admissibleKptAncestor a n hn) =
      admissibleKptAncestor (F.prescribedKptSkip family hB3 hTargets hPos a)
        (if ell ≤ n then n+1 else n)
        (F.prescribedKptSkip_ancestor_level_bound family hB3 hTargets hPos a n hn) := by
  let b := admissibleKptAncestor a n hn
  let c := admissibleKptAncestor (F.prescribedKptSkip family hB3 hTargets hPos a)
    (if ell ≤ n then n+1 else n)
    (F.prescribedKptSkip_ancestor_level_bound family hB3 hTargets hPos a n hn)
  have hb : b ≤ a := admissibleKptAncestor_le a n hn
  have hGb := F.prescribedKptSkip_prefix family hB3 hTargets hPos a b hb
  have hGc : c ≤ F.prescribedKptSkip family hB3 hTargets hPos a :=
    admissibleKptAncestor_le _ _ _
  have hGbRaw : (F.prescribedKptSkip family hB3 hTargets hPos b).1 ≤
      (F.prescribedKptSkip family hB3 hTargets hPos a).1 := hGb
  have hGcRaw : c.1 ≤ (F.prescribedKptSkip family hB3 hTargets hPos a).1 := hGc
  have hLevel : (F.prescribedKptSkip family hB3 hTargets hPos b).1.1 = c.1.1 :=
    F.prescribedKptSkip_level family hB3 hTargets hPos b
  apply Subtype.ext
  rcases rawPartialType_lower_linear hGbRaw hGcRaw with h | h
  · exact rawPartialTypePrefix_eq_of_same_level h hLevel
  · exact (rawPartialTypePrefix_eq_of_same_level h hLevel.symm).symm

/-- Together with injectivity and the strict level map, predecessor
preservation reflects the prefix order. No successor law is used. -/
theorem PrescribedBoringData.prescribedKptSkip_prefix_iff
    {ell db du dd : Nat} (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell) (a b : AdmissibleKptNode family) :
    F.prescribedKptSkip family hB3 hTargets hPos b ≤
      F.prescribedKptSkip family hB3 hTargets hPos a ↔ b ≤ a := by
  constructor
  · intro hImage
    have hImageRaw : (F.prescribedKptSkip family hB3 hTargets hPos b).1 ≤
        (F.prescribedKptSkip family hB3 hTargets hPos a).1 := hImage
    have hbaLevel : b.1.1 ≤ a.1.1 := by
      by_contra h
      have hStrict := F.prescribedKptSkip_strict_level family hB3 hTargets hPos
        a b (Nat.lt_of_not_ge h)
      have hle := hImageRaw.1
      omega
    let c : AdmissibleKptNode family :=
      ⟨rawPartialTypeAncestor a.1 b.1.1 hbaLevel,
        admissibleRawType_closed_under_prefix family a.2 b.1.1 hbaLevel⟩
    have hca : c ≤ a := rawPartialTypeAncestor_le a.1 b.1.1 hbaLevel
    have hcLevel : c.1.1 = b.1.1 := rfl
    have hImageC := F.prescribedKptSkip_prefix family hB3 hTargets hPos a c hca
    have hImageCRaw : (F.prescribedKptSkip family hB3 hTargets hPos c).1 ≤
        (F.prescribedKptSkip family hB3 hTargets hPos a).1 := hImageC
    have hEqualLevel := F.prescribedKptSkip_preserves_equal_level family hB3
      hTargets hPos c b hcLevel
    have hEqualRaw : (F.prescribedKptSkip family hB3 hTargets hPos c).1 =
        (F.prescribedKptSkip family hB3 hTargets hPos b).1 := by
      rcases rawPartialType_lower_linear hImageCRaw hImageRaw with h | h
      · exact rawPartialTypePrefix_eq_of_same_level h hEqualLevel
      · exact (rawPartialTypePrefix_eq_of_same_level h hEqualLevel.symm).symm
    have hcb : c = b := F.prescribedKptSkip_injective family hB3 hTargets hPos
      (Subtype.ext hEqualRaw)
    rw [← hcb]
    exact hca
  · intro hba
    exact F.prescribedKptSkip_prefix family hB3 hTargets hPos a b hba

/-- The actual total insertion, packaged as an order embedding. This is not
an SMTree ShapeMap: the successor decomposition laws are still separate. -/
noncomputable def PrescribedBoringData.prescribedKptOrderEmbedding
    {ell db du dd : Nat} (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell) : AdmissibleKptNode family ↪o AdmissibleKptNode family where
  toFun := F.prescribedKptSkip family hB3 hTargets hPos
  inj' := F.prescribedKptSkip_injective family hB3 hTargets hPos
  map_rel_iff' := by
    intro a b
    exact F.prescribedKptSkip_prefix_iff family hB3 hTargets hPos b a

end SuccessorTree.V10

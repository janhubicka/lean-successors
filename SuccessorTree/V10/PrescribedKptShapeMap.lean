import SuccessorTree.V10.PrescribedUpperSuccUnmatched
import SuccessorTree.V10.ConcreteKptM1
import Mathlib.Tactic

/-!
# Concrete global prescribed boring-extension ShapeMap

The actual total prescribed-or-neutral node map was already shown
injective, level-preserving, order-preserving and order-reflecting.
The lower/crossing weak successor law and both exact above-gap
branches are now combined. No successor law is postulated.

As with the neutral map, a separate every-level existence argument
is needed for SkipsOnly, but omission of ell follows immediately
from the level formula. Global M2/M3 remain separate.
-/

namespace SuccessorTree.V10

theorem PrescribedBoringData.prescribedKptSkip_weak_succ
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : AdmissibleKptSigma family}
    (hSucc : (admissibleKptSTree family).succ a p c = some b) :
    ∃ d : AdmissibleKptNode family,
      (admissibleKptSTree family).succ
        (F.prescribedKptSkip family hB3 hTargets hPos a)
        (p.map (F.prescribedKptSkip family hB3 hTargets hPos)) c = some d ∧
      d ≤ F.prescribedKptSkip family hB3 hTargets hPos b := by
  by_cases haLow : a.1.1 < ell
  · exact F.prescribedKptSkip_weak_succ_below_gap family
      hB3 hTargets hPos hSucc haLow
  · have haHigh : ell ≤ a.1.1 := by omega
    have hbHigh : ell ≤ b.1.1 := by
      have hCover := (admissibleKptSTree family).covBy_of_succ_eq_some hSucc
      have hh : a.1.1 ≤ b.1.1 := hCover.le.1
      omega
    by_cases hMatch : F.HasCompatibleSource (b.1.2.restrict hbHigh)
    · exact ⟨F.prescribedKptSkip family hB3 hTargets hPos b,
        F.prescribedKptSkip_succ_matching_above family hB3 hTargets
          hPos hSucc haHigh hMatch, le_rfl⟩
    · exact ⟨F.prescribedKptSkip family hB3 hTargets hPos b,
        F.prescribedKptSkip_succ_unmatched_above family hB3 hTargets
          hPos hSucc haHigh hMatch, le_rfl⟩

/-- Full concrete shape map extending the prescribed f, using its
actual total candidate rather than an abstract map axiom. -/
noncomputable def PrescribedBoringData.prescribedKptShapeMap
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell) :
    SuccessorTree.ShapeMap (admissibleKptSTree family) where
  toFun := F.prescribedKptSkip family hB3 hTargets hPos
  injective' := F.prescribedKptSkip_injective family hB3 hTargets hPos
  level_preserving' := by
    intro a b h
    exact F.prescribedKptSkip_preserves_equal_level family hB3 hTargets
      hPos a b h
  weak_succ' := by
    intro a b p c h
    exact F.prescribedKptSkip_weak_succ family hB3 hTargets hPos h
  root_le' := by
    intro a ha
    have hLow : a.1.1 < ell := by
      change a.1.1 = 0 at ha
      omega
    change a ≤ F.prescribedKptSkip family hB3 hTargets hPos a
    rw [F.prescribedKptSkip_fixed_below family hB3 hTargets hPos a hLow]

theorem PrescribedBoringData.prescribedKptShapeMap_mem_KptM
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell) :
    F.prescribedKptShapeMap family hB3 hTargets hPos ∈ KptM family := by
  intro a ha
  change (F.prescribedKptSkip family hB3 hTargets hPos a).1.1 = 0
  have hLow : a.1.1 < ell := by
    change a.1.1 = 0 at ha
    omega
  rw [F.prescribedKptSkip_fixed_below family hB3 hTargets hPos a hLow]
  exact ha

theorem PrescribedBoringData.prescribedKptShapeMap_skips
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell) :
    (F.prescribedKptShapeMap family hB3 hTargets hPos).Skips ell := by
  intro h
  obtain ⟨a,ha⟩ := h
  exact F.prescribedKptSkip_omits_level family hB3 hTargets hPos a ha

end SuccessorTree.V10

import SuccessorTree.V10.PrescribedImageRepresentation
import Mathlib.Tactic

/-!
# Prefix-case reductions for the total prescribed Kpt insertion

Comparable upper nodes share the same complete ell-prefix, so they
make the SAME prescribed/neutral branch decision. This is derived
from the genuine prefix relation; it is not an extra hypothesis on
the candidate map.

The below-gap and both-neutral predecessor cases are then immediate
from the actual map. The matching/matching case still needs a
constructor-level prefix theorem; no ShapeMap claim is made here.
-/

namespace SuccessorTree.V10

/-- A genuine Kpt prefix has exactly the same full ell-record as its
ancestor, once both levels reach ell. In particular the compatibility
test is constant along every upper predecessor chain. -/
theorem PrescribedBoringData.compatibleSource_iff_of_Kpt_prefix
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    {family : List (NormalizedForbidden db du dd)}
    (a b : AdmissibleKptNode family)
    (hba : b ≤ a) (hlevB : ell ≤ b.1.1) :
    F.HasCompatibleSource (b.1.2.restrict hlevB) ↔
      F.HasCompatibleSource
        (a.1.2.restrict (hlevB.trans
          (show b.1.1 ≤ a.1.1 from (show b.1 ≤ a.1 from hba).1))) := by
  have hraw : b.1 ≤ a.1 := hba
  have hEq : b.1.2.restrict hlevB =
      a.1.2.restrict (hlevB.trans hraw.1) := by
    rw [hraw.2]
    exact PartialTypeWithE.restrict_trans a.1.2 hlevB hraw.1
  rw [hEq]

/-- Source prefixes entirely below the inserted level are fixed and
therefore remain prefixes, including their complete auxiliary E data. -/
theorem PrescribedBoringData.prescribedKptSkip_prefix_below
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a b : AdmissibleKptNode family)
    (hba : b ≤ a) (haLow : a.1.1 < ell) :
    F.prescribedKptSkip family hB3 hTargets hPos b ≤
      F.prescribedKptSkip family hB3 hTargets hPos a := by
  have hraw : b.1 ≤ a.1 := hba
  have hbLow : b.1.1 < ell := lt_of_le_of_lt hraw.1 haLow
  rw [F.prescribedKptSkip_fixed_below family hB3 hTargets hPos b hbLow,
    F.prescribedKptSkip_fixed_below family hB3 hTargets hPos a haLow]
  exact hba

/-- If an upper prefix has no compatible prescribed source, neither
does any upper extension. Both images therefore use the *verified*
neutral construction, which already preserves all complete prefixes. -/
theorem PrescribedBoringData.prescribedKptSkip_prefix_unmatched
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a b : AdmissibleKptNode family)
    (hba : b ≤ a) (hlevB : ell ≤ b.1.1)
    (hNoneB : ¬ F.HasCompatibleSource (b.1.2.restrict hlevB)) :
    F.prescribedKptSkip family hB3 hTargets hPos b ≤
      F.prescribedKptSkip family hB3 hTargets hPos a := by
  have hraw : b.1 ≤ a.1 := hba
  have hlevA : ell ≤ a.1.1 := hlevB.trans hraw.1
  have hNoneA : ¬ F.HasCompatibleSource (a.1.2.restrict hlevA) := by
    intro ha
    exact hNoneB
      ((F.compatibleSource_iff_of_Kpt_prefix a b hba hlevB).2 ha)
  rw [F.prescribedKptSkip_neutral family hB3 hTargets hPos b hlevB hNoneB,
    F.prescribedKptSkip_neutral family hB3 hTargets hPos a hlevA hNoneA]
  exact neutralKptImage_prefix_le family ell hPos a b hba hlevB

end SuccessorTree.V10

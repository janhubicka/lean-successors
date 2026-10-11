import SuccessorTree.V10.PrescribedKptShapeMap
import SuccessorTree.V10.PrescribedSourceFullValue
import SuccessorTree.V10.LocalAgeAllLevels
import Mathlib.Tactic

/-!
# One-gap prescribed boring extension, with exact range and source values

The actual finite/model constructions establish a single total map of
admissible Kpt nodes. Its ShapeMap structure, prescribed values,
membership in KptM, and level range are now gathered here.

SkipsOnly requires NO further finite insertion argument: every Kpt
level is inhabited by the already checked pure-neutral witness, and
the map has the literal level formula n ↦ n (n<ell), n ↦ n+1 (n≥ell).

This is the normalized finite unary/binary implementation of the
one-gap conclusion. It does not discharge M2, M3, the original-language
adapter, or the final big-Ramsey upper bound.
-/

namespace SuccessorTree.V10

/-- The actual prescribed map misses exactly level ell, not merely
ell among possibly many missing levels. This uses the independent
all-level admissibility witnesses and the exact uniform shift. -/
theorem PrescribedBoringData.prescribedKptShapeMap_skipsOnly
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell) :
    (F.prescribedKptShapeMap family hB3 hTargets hPos).SkipsOnly ell := by
  unfold SuccessorTree.ShapeMap.SkipsOnly
  ext q
  constructor
  · rintro ⟨a, ha⟩
    intro heq
    have hIn : ell ∈
        (F.prescribedKptShapeMap family hB3 hTargets hPos).levelRange := by
      refine ⟨a, ?_⟩
      exact ha.trans heq
    exact (F.prescribedKptShapeMap_skips family hB3 hTargets hPos) hIn
  · intro hq
    have hqne : q ≠ ell := by
      simpa only [Set.mem_setOf_eq] using hq
    by_cases hlt : q < ell
    · obtain ⟨a,ha⟩ := admissibleKptLevel_nonempty family q
      refine ⟨a, ?_⟩
      change (F.prescribedKptSkip family hB3 hTargets hPos a).1.1 = q
      rw [F.prescribedKptSkip_level family hB3 hTargets hPos, ha]
      simp [Nat.not_le.mpr hlt]
    · have hgt : ell < q := by omega
      obtain ⟨a,ha⟩ := admissibleKptLevel_nonempty family (q-1)
      refine ⟨a, ?_⟩
      change (F.prescribedKptSkip family hB3 hTargets hPos a).1.1 = q
      rw [F.prescribedKptSkip_level family hB3 hTargets hPos, ha]
      have hge : ell ≤ q-1 := by omega
      simp [hge]
      omega

/-- At every genuinely admissible prescribed source S, the concrete
ShapeMap realizes the complete f(S) node, including all E atoms.
The existence of a finite representative is part of admissibility. -/
theorem PrescribedBoringData.prescribedKptShapeMap_agrees_on_source
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (S : PartialTypeWithE ell db du dd)
    (hSrc : S ∈ F.source)
    (hAdS : IsAdmissibleRawType family
      (⟨ell,S⟩ : RawPartialTypeNode db du dd)) :
    ((F.prescribedKptShapeMap family hB3 hTargets hPos)
      (⟨⟨ell,S⟩,hAdS⟩ : AdmissibleKptNode family)).1 =
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd) := by
  change (F.prescribedKptSkip family hB3 hTargets hPos
    (⟨⟨ell,S⟩,hAdS⟩ : AdmissibleKptNode family)).1 =
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd)
  exact F.prescribedKptSkip_agrees_on_source family hB3 hTargets
    hPos S hSrc hAdS

/-- One endpoint for the full one-gap prescribed conclusion in the
normalized Kpt setting. No arbitrary shape map or preservation law
is postulated: the witness is the selected prescribed-or-neutral map
constructed from B1/B2, corrected B3 and admissible prescribed targets. -/
theorem PrescribedBoringData.prescribedKpt_boring_extension_exists
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell) :
    ∃ Φ : SuccessorTree.ShapeMap (admissibleKptSTree family),
      Φ ∈ KptM family ∧ Φ.SkipsOnly ell ∧
      ∀ (S : PartialTypeWithE ell db du dd)
        (hSrc : S ∈ F.source)
        (hAdS : IsAdmissibleRawType family
          (⟨ell,S⟩ : RawPartialTypeNode db du dd)),
        (Φ (⟨⟨ell,S⟩,hAdS⟩ : AdmissibleKptNode family)).1 =
          (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd) := by
  refine ⟨F.prescribedKptShapeMap family hB3 hTargets hPos,
    F.prescribedKptShapeMap_mem_KptM family hB3 hTargets hPos,
    F.prescribedKptShapeMap_skipsOnly family hB3 hTargets hPos, ?_⟩
  intro S hSrc hAdS
  exact F.prescribedKptShapeMap_agrees_on_source family hB3 hTargets
    hPos S hSrc hAdS

end SuccessorTree.V10

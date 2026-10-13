import SuccessorTree.V10.PrescribedCompatibleB3
import SuccessorTree.V10.OneGapSocleGluing
import Mathlib.Tactic

/-!
# Global boring extension from the compatibility-restricted age test

Restrict the prescribed data separately to each ordinary L+ socle.
The old fully checked boring extension applies to each restriction.
OneGapSocleGluing combines these into a single total ShapeMap, since
all high parameters of a genuine successor have its ordinary socle
and every low parameter is fixed by all one-gap maps.

This proves the global extension theorem under CompatibleB3, not just
a finite insertion or one class. The derivation of CompatibleB3 for
the boundary restoration of an arbitrary F remains the M2 task.
-/

namespace SuccessorTree.V10

/-- Restrict to the class specified by its ordinary record, allowing
empty classes without choosing a representative or a witness. -/
def PrescribedBoringData.restrictToSocle {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (C : OrdinarySocleRecord ell db du dd) : PrescribedBoringData ell db du dd where
  source := {T | T ∈ F.source ∧ T.ordinarySocleRecord = C}
  target := F.target
  extendsSource := fun T hT => F.extendsSource T hT.1
  preservesCompatibility := fun T U hT hU hTU =>
    F.preservesCompatibility T U hT.1 hU.1 hTU

/-- No E-lift is imposed on an age witness. The compatibility
information comes from the selected original source records. -/
theorem PrescribedBoringData.restrictToSocle_correctedB3
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CompatibleB3 family)
    (C : OrdinarySocleRecord ell db du dd) :
    (F.restrictToSocle C).CorrectedB3 family := by
  intro S0 hS0 W hFinite hSame hUpper hDelete
  have hUpper' : UpperTypesPrescribed W ell (F.CompatibleUpperLType S0) := by
    intro x hx hxell
    obtain ⟨T, hT, hType⟩ := hUpper x hx hxell
    exact ⟨T, hT.1,
      (ordinarySocleRecord_eq_iff T S0).1 (hT.2.trans hS0.2.symm), hType⟩
  exact hB3 S0 hS0.1 W hFinite hSame hUpper' hDelete

/-- The concrete old construction for a single ordinary-socle class. -/
noncomputable def PrescribedBoringData.compatibleClassShapeMap
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CompatibleB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1, F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell) (C : OrdinarySocleRecord ell db du dd) :
    SuccessorTree.ShapeMap (admissibleKptSTree family) :=
  (F.restrictToSocle C).prescribedKptShapeMap family
    (F.restrictToSocle_correctedB3 family hB3 C)
    (fun S hS => hTargets S hS.1) hPos

theorem PrescribedBoringData.compatibleClassShapeMap_skipsOnly
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CompatibleB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1, F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell) (C : OrdinarySocleRecord ell db du dd) :
    (F.compatibleClassShapeMap family hB3 hTargets hPos C).SkipsOnly ell :=
  (F.restrictToSocle C).prescribedKptShapeMap_skipsOnly family
    (F.restrictToSocle_correctedB3 family hB3 C)
    (fun S hS => hTargets S hS.1) hPos

/-- A single total one-gap map realizes ALL prescribed source types
under the weaker compatible-class age condition. The conclusion has
no remaining classwise-gluing premise or successor-preservation axiom. -/
theorem PrescribedBoringData.compatible_boring_extension_exists
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CompatibleB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1, F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell) :
    ∃ G : SuccessorTree.ShapeMap (admissibleKptSTree family),
      G ∈ KptM family ∧ G.SkipsOnly ell ∧
      ∀ (S : PartialTypeWithE ell db du dd)
        (hS : S ∈ F.source)
        (hAdS : IsAdmissibleRawType family
          (⟨ell, S⟩ : RawPartialTypeNode db du dd)),
        (G (⟨⟨ell, S⟩, hAdS⟩ : AdmissibleKptNode family)).1 =
          (⟨ell+1, F.target S⟩ : RawPartialTypeNode db du dd) := by
  let Phi := F.compatibleClassShapeMap family hB3 hTargets hPos
  have hSkip : ∀ C : OrdinarySocleRecord ell db du dd, (Phi C).SkipsOnly ell :=
    F.compatibleClassShapeMap_skipsOnly family hB3 hTargets hPos
  refine ⟨oneGapSocleShapeMap family ell Phi hSkip,
    oneGapSocleShapeMap_mem_KptM family ell Phi hSkip hPos,
    oneGapSocleShapeMap_skipsOnly family ell Phi hSkip, ?_⟩
  intro S hS hAdS
  let a : AdmissibleKptNode family := ⟨⟨ell, S⟩, hAdS⟩
  have hKey : ordinarySocleAt family ell a = S.ordinarySocleRecord := by
    simp only [ordinarySocleAt, a, dif_pos le_rfl, PartialTypeWithE.restrict_self]
  change (Phi (ordinarySocleAt family ell a) a).1 =
    (⟨ell+1, F.target S⟩ : RawPartialTypeNode db du dd)
  rw [hKey]
  exact (F.restrictToSocle S.ordinarySocleRecord).prescribedKptShapeMap_agrees_on_source
    family (F.restrictToSocle_correctedB3 family hB3 S.ordinarySocleRecord)
    (fun T hT => hTargets T hT.1) hPos S ⟨hS, rfl⟩ hAdS

end SuccessorTree.V10

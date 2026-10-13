import SuccessorTree.V10.PrescribedCompatibleCompletion
import SuccessorTree.V10.LevelRemovalM2ExactExtension
import Mathlib.Tactic

/-!
# Final M2 factorization from actual compatible prescribed boundary data

The global boring-extension theorem now uses only CompatibleB3,
restricted separately to each ordinary L+ source socle; its one-gap
maps are glued without a cross-class coherence assumption.

Here we join that checked theorem to the existing intrinsic deletion
ShapeMap and its sharp first-boundary equality. No abstract M2 axiom,
unverified global G, or stronger CorrectedB3 assumption is introduced.

The remaining obligations for concrete M2 are exactly to construct
the canonical partial boundary data P (with B1/B2), and derive
CompatibleB3 using the non-edge padded finite forbidden-copy source.
-/

namespace SuccessorTree.V10

/-- The genuine one-gap factorization follows from a concrete finite
prescription whose source contains EVERY deleted boundary image,
whose target is the actual F-image there, and whose compatible-class
age condition holds. No abstract extension ShapeMap G is an input:
its existence follows from the proved global gluing theorem. -/
theorem uniformGapDeletedShapeMap_factorization_of_compatibleB3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hFM : F ∈ KptM family)
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (P : PrescribedBoringData
      (LevelTree.lev (F a₀) - 1) db du dd)
    (hB3 : P.CompatibleB3 family)
    (hTargets : ∀ S, S ∈ P.source → IsAdmissibleRawType family
      (⟨(LevelTree.lev (F a₀) - 1) + 1, P.target S⟩ :
        RawPartialTypeNode db du dd))
    (hPos : 0 < LevelTree.lev (F a₀) - 1)
    (hBoundary :
      ∀ x : AdmissibleKptNode family,
        LevelTree.lev x = LevelTree.lev a₀ →
        ∃ (S : PartialTypeWithE
             (LevelTree.lev (F a₀) - 1) db du dd)
          (hS : S ∈ P.source)
          (hAd : IsAdmissibleRawType family
            (⟨LevelTree.lev (F a₀) - 1,S⟩ :
              RawPartialTypeNode db du dd)),
          uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x =
            (⟨⟨LevelTree.lev (F a₀) - 1,S⟩,hAd⟩ :
              AdmissibleKptNode family) ∧
          (F x).1 =
            (⟨(LevelTree.lev (F a₀) - 1) + 1,P.target S⟩ :
              RawPartialTypeNode db du dd)) :
    ∃ F1 F2 : SuccessorTree.ShapeMap (admissibleKptSTree family),
      F1 ∈ KptM family ∧
      F2 ∈ KptM family ∧
      F2.SkipsOnly (LevelTree.lev (F a₀) - 1) ∧
      ∀ x : AdmissibleKptNode family,
        LevelTree.lev x ≤ LevelTree.lev a₀ →
        F2 (F1 x) = F x := by
  obtain ⟨G,hGM,hSkip,hAgreement⟩ :=
    P.compatible_boring_extension_exists
      family hB3 hTargets hPos
  apply uniformGapDeletedShapeMap_factorization_of_boundary_extension
    family F hFM q₀ a₀ hprev hgap G hGM hSkip
  intro x hx
  obtain ⟨S,hS,hAd,hD,hT⟩ := hBoundary x hx
  rw [hD]
  apply Subtype.ext
  calc
    (G (⟨⟨LevelTree.lev (F a₀) - 1,S⟩,hAd⟩ :
      AdmissibleKptNode family)).1 =
      (⟨(LevelTree.lev (F a₀) - 1) + 1,P.target S⟩ :
        RawPartialTypeNode db du dd) := hAgreement S hS hAd
    _ = (F x).1 := hT.symm

end SuccessorTree.V10

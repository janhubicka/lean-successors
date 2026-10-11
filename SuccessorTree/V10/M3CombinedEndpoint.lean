import SuccessorTree.V10.M3ActualDuplicateStep
import Mathlib.Tactic

/-!
# M3: one genuine boring extension duplicates an earlier Kpt successor

This combines two independently specified endpoints of the SAME selected
finite E3-gated insertion: the corrected-B3 prescribed one-gap ShapeMap
and the actual canonical Kpt step whose inputs repeat an earlier crossing.

No abstract M3 axiom is assumed. The theorem is for the normalized
finite unary/directed-binary/diagonal language, not yet the manuscript's
full arbitrary relational-language presentation.
-/

namespace SuccessorTree.V10

/-- The selected genuine one-gap ShapeMap realizes the *actual* canonical
successor inputs of the earlier n-th crossing at every level-ell
admissible Kpt type. Both the old crossing and the new output are
genuine admissible Kpt nodes.

The source-dependent free cut is implicit in the canonical old step;
there is no globally fixed cut or auxiliary E-condition on age
witnesses. -/
theorem m3OneGapShapeMap_repeats_old_step
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell) :
    ∃ Φ : SuccessorTree.ShapeMap (admissibleKptSTree family),
      Φ ∈ KptM family ∧ Φ.SkipsOnly ell ∧
      ∀ (T : PartialTypeWithE ell db du dd)
        (hAd : IsAdmissibleRawType family
          (⟨ell,T⟩ : RawPartialTypeNode db du dd)),
        let aNew : AdmissibleKptNode family :=
          ⟨⟨ell,T⟩,hAd⟩
        ∃ (aOld bOld : AdmissibleKptNode family)
          (p : List (AdmissibleKptNode family))
          (c : AdmissibleKptSigma family),
          IsCanonicalKptStep family aOld p c.1 bOld ∧
          bOld.1 =
            (⟨n+1,T.restrict (Nat.succ_le_of_lt hn)⟩ :
              RawPartialTypeNode db du dd) ∧
          (admissibleKptSTree family).succ aNew p c =
            some (Φ aNew) := by
  obtain ⟨Φ,hM,hSkip,hAgreement⟩ :=
    m3TotalBoringData_boring_extension_exists family n hn
  refine ⟨Φ,hM,hSkip,?_⟩
  intro T hAd
  let aNew : AdmissibleKptNode family := ⟨⟨ell,T⟩,hAd⟩
  have hSrc : T ∈ (m3TotalBoringData family ell n hn).source := by
    change IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd)
    exact hAd
  have hΦ :
      (Φ aNew).1 =
        (⟨ell+1,(m3TotalBoringData family ell n hn).target T⟩ :
          RawPartialTypeNode db du dd) :=
    hAgreement T hSrc hAd
  obtain ⟨aOld,bOld,bNew,p,c,hOldStep,hOldRaw,hNewSucc,hNewRaw⟩ :=
    m3TotalBoringData_uses_old_canonical_step family n hn T hAd
  have hb : bNew = Φ aNew :=
    Subtype.ext (hNewRaw.trans hΦ.symm)
  let cAd : AdmissibleKptSigma family :=
    ⟨c,canonicalKptStep_letter_admissible family hOldStep⟩
  refine ⟨aOld,bOld,p,cAd,hOldStep,hOldRaw,?_⟩
  change canonicalKptSucc family aNew p c = some (Φ aNew)
  rw [← hb]
  exact hNewSucc

end SuccessorTree.V10

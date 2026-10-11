import SuccessorTree.V10.M3ActualB3
import SuccessorTree.V10.PrescribedBoringCompletion
import Mathlib.Tactic

/-!
# A concrete M3 one-gap shape map from the actual total prescription

The preceding modules define F on ALL admissible level-ell source
records by genuine finite E3-gated duplication of old n<ell. B1/B2
and admissibility of every F(T) are proved without extra assumptions;
M3ActualB3 proves the manuscript's corrected finite L-only B3 for
this same selected F, with arbitrary source-dependent free cuts.

Apply the ALREADY VERIFIED prescribed boring-extension theorem to
this specific data. The result is a real ShapeMap in KptM omitting
exactly ell, agreeing with the actual finite cloned outputs on
every admissible source record.

The remaining identification with the exact canonical M3 input
parameter and terminal Sigma letter is a separate endpoint; the
present theorem does not silently postulate it.
-/

namespace SuccessorTree.V10

/-- One-level M3 map from the ACTUAL source-selected finite clone:
no extra corrected-B3 hypothesis, no global free-cut assumption,
and no assumed existence of a shape-preserving duplication. -/
theorem m3OneGapShapeMap_exists
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell n : Nat) (hn : n < ell) :
    ∃ Φ : SuccessorTree.ShapeMap (admissibleKptSTree family),
      Φ ∈ KptM family ∧
      Φ.SkipsOnly ell ∧
      ∀ (T : PartialTypeWithE ell db du dd)
        (hT : IsAdmissibleRawType family
          (⟨ell,T⟩ : RawPartialTypeNode db du dd)),
        (Φ (⟨⟨ell,T⟩,hT⟩ : AdmissibleKptNode family)).1 =
          (⟨ell+1,m3FiniteTarget family n hn T hT⟩ :
            RawPartialTypeNode db du dd) := by
  let F := m3TotalBoringData family ell n hn
  have hB3 : F.CorrectedB3 family :=
    m3TotalBoringData_correctedB3 family n hn
  have hTargets : ∀ T, T ∈ F.source →
      IsAdmissibleRawType family
        (⟨ell+1,F.target T⟩ : RawPartialTypeNode db du dd) := by
    intro T hT
    exact m3TotalBoringData_target_admissible family n hn T hT
  have hPos : 0 < ell := by omega
  obtain ⟨Φ,hM,hOnly,hExtend⟩ :=
    F.prescribedKpt_boring_extension_exists family hB3 hTargets hPos
  refine ⟨Φ,hM,hOnly,?_⟩
  intro T hT
  have hSrc : T ∈ F.source := hT
  have hh := hExtend T hSrc hT
  rw [m3TotalBoringData_target_eq family n hn T hSrc] at hh
  exact hh

end SuccessorTree.V10

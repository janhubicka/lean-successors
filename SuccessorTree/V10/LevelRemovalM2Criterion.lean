import SuccessorTree.V10.LevelRemovalUniformShapeMap
import SuccessorTree.V10.PrescribedBoringCompletion
import Mathlib.Tactic

/-!
# Exact remaining prescribed-insertion obligation in the M2 gap argument

The intrinsic deletion map is a shape map once the full weak-successor
theorem is available.  To complete paper M2 through a chosen source
boundary, it suffices to provide ONE corrected-B3 prescribed insertion
whose actual Kpt shape map agrees with F on every source at that
boundary, after intrinsic deletion.  All earlier source values then
agree automatically because the deletion map is unchanged there and
the prescribed insertion is the identity below its skipped level.

This is an explicitly CONDITIONAL reduction, not an implementation of
the missing finite L-only B3 necessity nor the full M2 axiom.
-/

namespace SuccessorTree.V10

/-- M2 through the first affected source level, assuming the remaining
finite corrected-B3 prescribed insertion data and its boundary agreement.

No abstract M2 hypothesis is used.  The two witnesses are the genuine
intrinsic deletion ShapeMap and the already constructed prescribed
one-gap insertion ShapeMap; on lower source levels the composition
identity follows from the proved strict gap. -/
theorem uniformGapDeletedShapeMap_factorization_if_prescribed
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hFM : F ∈ KptM family)
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (P : PrescribedBoringData (LevelTree.lev (F a₀) - 1) db du dd)
    (hB3 : P.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ P.source → IsAdmissibleRawType family
      (⟨(LevelTree.lev (F a₀) - 1) + 1, P.target S⟩ :
        RawPartialTypeNode db du dd))
    (hPos : 0 < LevelTree.lev (F a₀) - 1)
    (hBoundary :
      ∀ (x : AdmissibleKptNode family),
        LevelTree.lev x = LevelTree.lev a₀ →
        (P.prescribedKptShapeMap family hB3 hTargets hPos)
          (uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x) =
          F x) :
    ∃ F1 F2 : SuccessorTree.ShapeMap (admissibleKptSTree family),
      F1 ∈ KptM family ∧
      F2 ∈ KptM family ∧
      F2.SkipsOnly (LevelTree.lev (F a₀) - 1) ∧
      ∀ x : AdmissibleKptNode family,
        LevelTree.lev x ≤ LevelTree.lev a₀ →
        F2 (F1 x) = F x := by
  refine ⟨uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap,
    P.prescribedKptShapeMap family hB3 hTargets hPos,
    uniformGapDeletedShapeMap_mem_KptM family F hFM q₀ a₀ hprev hgap,
    P.prescribedKptShapeMap_mem_KptM family hB3 hTargets hPos,
    P.prescribedKptShapeMap_skipsOnly family hB3 hTargets hPos, ?_⟩
  intro x hx
  rcases lt_or_eq_of_le hx with hLow | hEq
  · rw [uniformGapDeletedShapeMap_below family F q₀ a₀
      hprev hgap x hLow]
    exact P.prescribedKptSkip_fixed_below family hB3 hTargets hPos
      (F x)
      (by
        have hXQ : LevelTree.lev x ≤ LevelTree.lev q₀ := by omega
        have hFBound := shapeMap_level_le_of_level_le family F hXQ
        change LevelTree.lev (F x) < LevelTree.lev (F a₀) - 1
        omega)
  · exact hBoundary x hEq

end SuccessorTree.V10

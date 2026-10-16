import SuccessorTree.V10.KptE1ActualParameterTransport
import SuccessorTree.EnvelopePullback
import SuccessorTree.V10.KptCompleteSMTree
import Mathlib.Tactic

/-!
# The normalized Kpt tree satisfies the genuine one-level pullback E1

A defined target successor `succ (F a) (p.map F) c` has a canonical
complete L+ type Q, literal old predecessor F(a), admissible letter
and empty/singleton canonical E-cut parameter.

The actual monoid fixes level zero. Strictly increasing shape levels
therefore reflect the canonical target E-cut to a source cut. The
retained L+ source Q is genuinely admissible by the padded neutral
witness; its predecessor, parameter and terminal letter are exactly
a, p and c. The canonical source successor is consequently defined.

This asserts **existence** of a source successor, as required by
Section 5 (E1), not that the displayed target successor b lies in
the range of F. No relation arity beyond the normalized finite
unary/directed-binary/diagonal setting is claimed.
-/

namespace SuccessorTree.V10

/-- For every shape map in the actual root-preserving normalized
Kpt monoid, a genuine defined target successor pulls back to a
defined source successor. This is E1 at the precise `PullbackDefined`
interface used by the finite envelope construction. -/
theorem normalizedKpt_oneLevelPullback
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hF : F ∈ KptM family) :
    SuccessorTree.SMTree.Envelope.PullbackDefined
      (admissibleKptSTree family) F := by
  intro a p c hDefined
  obtain ⟨b, hTargetSucc⟩ := hDefined
  have hRaw :
      canonicalKptSucc family (F a) (p.map F) c.1 = some b := by
    simpa only [admissibleKptSTree_succ_eq] using hTargetSucc
  obtain ⟨ell, g, hg, Q, hBase, hTarget, hLetter,
    hValid, hParam, hGate⟩ :=
      canonicalKptSucc_spec family hRaw
  have hEll : ell = (F a).1.1 := by
    have he := congrArg Sigma.fst hBase
    exact he.symm
  subst ell
  have hTargetPred :
      Q.restrict (Nat.le_succ (F a).1.1) = (F a).1.2 := by
    exact (eq_of_heq (Sigma.mk.inj_iff.mp hBase).2).symm
  have hTargetAd :
      IsAdmissibleRawType family
        (⟨(F a).1.1 + 1, Q⟩ :
          RawPartialTypeNode db du dd) := by
    rw [← hTarget]
    exact b.2
  have hImageLevel :
      (F a).1.1 = kptShapeLevelMap family F (LevelTree.lev a) :=
    (kptShapeLevelMap_eq family F a).symm
  obtain ⟨hp, hgZero⟩ | ⟨x, hp, hgSource, hxPos, hxLt⟩ :=
    kptE1_image_parameter_cases family F hF a Q g hg p
      hImageLevel hGate hParam
  · subst p
    have hSourceColumn :
        ValidNewOrdinaryColumn Q (kptShapeLevelMap family F 0) := by
      rw [← hgZero]
      exact hValid
    have hSourceParameter :
        (([] : List (AdmissibleKptNode family)).map (fun x => x.1)) =
          ((Q.reindexOrdinary
            (kptShapeLastIndexAtNode family F a)).canonicalParameterRecord 0 (Nat.zero_le a.1.1)).toList := by
      simp [PartialTypeWithE.canonicalParameterRecord]
    exact kptE1_source_successor_of_parameter_record
      family F a [] c Q hTargetPred hTargetAd hLetter
      0 (Nat.zero_le a.1.1) (Or.inl rfl)
      hSourceColumn hSourceParameter
  · subst p
    have hf : LevelTree.lev x ≤ LevelTree.lev a :=
      Nat.le_of_lt hxLt
    have hSourceColumn :
        ValidNewOrdinaryColumn Q
          (kptShapeLevelMap family F (LevelTree.lev x)) := by
      rw [← hgSource]
      exact hValid
    have hgParameter :
        kptShapeLevelMap family F (LevelTree.lev x) ≤ (F a).1.1 := by
      have hmon :=
        (kptShapeLevelMap_strictMono family F).monotone hf
      rw [kptShapeLevelMap_eq family F a] at hmon
      exact hmon
    have hgNonzero : g ≠ 0 := by
      intro hg0
      have hnil :=
        (kptImageParameter_empty_iff_cut_zero
          family F Q g hg [x] hParam).mpr hg0
      simp at hnil
    have hRawParameter :
        (F x).1 = (⟨g, Q.lastOrdinaryParameter g hg⟩ :
          RawPartialTypeNode db du dd) := by
      simpa [PartialTypeWithE.canonicalParameterRecord, hgNonzero]
        using hParam
    have hImageParameter :
        (F x).1 =
          (⟨kptShapeLevelMap family F (LevelTree.lev x),
            Q.lastOrdinaryParameter
              (kptShapeLevelMap family F (LevelTree.lev x))
              hgParameter⟩ : RawPartialTypeNode db du dd) := by
      rw [hgSource] at hRawParameter
      simpa using hRawParameter
    have hRecovered :
        (Q.reindexOrdinary
          (kptShapeLastIndexAtNode family F a)).lastOrdinaryParameter
            (LevelTree.lev x) hf = x.1.2 :=
      kptShapeReindex_parameter_recovers_atNode
        family F a x hf Q hgParameter hImageParameter
    have hSourceParameter :
        ([x] : List (AdmissibleKptNode family)).map
          (fun y => y.1) =
          ((Q.reindexOrdinary
            (kptShapeLastIndexAtNode family F a)).canonicalParameterRecord (LevelTree.lev x) hf).toList := by
      have hxNonzero : LevelTree.lev x ≠ 0 :=
        Nat.ne_of_gt hxPos
      simp [PartialTypeWithE.canonicalParameterRecord,
        hxNonzero, hRecovered]
    exact kptE1_source_successor_of_parameter_record
      family F a [x] c Q hTargetPred hTargetAd hLetter
      (LevelTree.lev x) hf (Or.inr hxLt)
      hSourceColumn hSourceParameter

/-- The one-level pullback hypothesis consumed by the envelope
algorithm holds for the assembled normalized Kpt `SMTree`. -/
theorem normalizedKptSMTree_oneLevelPullback
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    ∀ F ∈ (normalizedKptSMTree family).M,
      SuccessorTree.SMTree.Envelope.PullbackDefined
        (admissibleKptSTree family) F := by
  intro F hF
  exact normalizedKpt_oneLevelPullback family F hF

end SuccessorTree.V10

import SuccessorTree.V10.KptE1SourceAdmissibility
import SuccessorTree.V10.CanonicalRawSTree

/-!
# Assemble the actual Kpt source successor from retained target data

This step does not assume that an arbitrary source extension is admissible.
The source is the literal L+ pullback of a genuine admissible target
successor and is admissible by the neutral-spacer construction.

The only premise not yet derived from the genuine target canonical step is
the equality between the source parameter list and the canonical parameter
record of that literal pullback. The next theorem will discharge it using
the retained shape-level parameter identity and full type recovery.
-/

namespace SuccessorTree.V10

/-- Concrete one-level source successor, provided the genuine source
parameter record has been recovered. Every other source condition
(admissibility, predecessor, letter, valid E/L column) follows from
actual Kpt target data and the full-record shape map. -/
theorem kptE1_source_successor_of_parameter_record
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (a : AdmissibleKptNode family)
    (p : List (AdmissibleKptNode family))
    (c : AdmissibleKptSigma family)
    (Q : PartialTypeWithE ((F a).1.1 + 1) db du dd)
    (hTargetPred :
      Q.restrict (Nat.le_succ (F a).1.1) = (F a).1.2)
    (hTargetAd : IsAdmissibleRawType family
      (⟨(F a).1.1 + 1, Q⟩ : RawPartialTypeNode db du dd))
    (hTargetLetter : c.1 = Q.terminalLetter)
    (f : Nat) (hf : f ≤ a.1.1)
    (hGate : f = 0 ∨ f < a.1.1)
    (hTargetColumn : ValidNewOrdinaryColumn Q
      (kptShapeLevelMap family F f))
    (hParameter :
      p.map (fun x => x.1) =
      ((Q.reindexOrdinary
        (kptShapeLastIndexAtNode family F a)).canonicalParameterRecord f hf).toList) :
    ∃ b : AdmissibleKptNode family,
      (admissibleKptSTree family).succ a p c = some b := by
  let rho := kptShapeLastIndexAtNode family F a
  let R : PartialTypeWithE (a.1.1 + 1) db du dd :=
    Q.reindexOrdinary rho
  have hAd : IsAdmissibleRawType family
      (⟨a.1.1 + 1, R⟩ : RawPartialTypeNode db du dd) :=
    kptE1_reindexed_target_admissible
      family F a Q hTargetPred hTargetAd f hGate hTargetColumn
  let b : AdmissibleKptNode family :=
    ⟨⟨a.1.1 + 1, R⟩, hAd⟩
  have hOld :
      R.restrict (Nat.le_succ a.1.1) = a.1.2 :=
    kptShapeReindex_recovers_old_predecessor family F a Q hTargetPred
  have hLetter : c.1 = R.terminalLetter := by
    change c.1 =
      (Q.reindexOrdinary
        (kptShapeLastIndexAtNode family F a)).terminalLetter
    rw [kptShapeReindex_terminalLetter_atNode family F a Q]
    exact hTargetLetter
  have hMono : StrictMono rho := by
    intro i j hij
    change kptShapeLevelMap family F i.val <
      kptShapeLevelMap family F j.val
    exact (kptShapeLevelMap_strictMono family F) hij
  have hLast : rho (Fin.last a.1.1) = Fin.last (F a).1.1 :=
    kptShapeLastIndexAtNode_last family F a
  have hCut (i : Fin a.1.1) :
      (rho i.castSucc).val < kptShapeLevelMap family F f ↔
        i.val < f := by
    change kptShapeLevelMap family F i.val <
      kptShapeLevelMap family F f ↔ i.val < f
    constructor
    · intro h
      by_contra hnot
      have hle : f ≤ i.val := Nat.le_of_not_gt hnot
      have himage :=
        (kptShapeLevelMap_strictMono family F).monotone hle
      omega
    · intro h
      exact (kptShapeLevelMap_strictMono family F) h
  have hValid : ValidNewOrdinaryColumn R f :=
    Q.reindexOrdinary_validNewColumn rho hMono hLast
      (kptShapeLevelMap family F f) hTargetColumn f hCut
  have hStep : IsCanonicalKptStep family a p c.1 b := by
    refine ⟨a.1.1, f, hf, R, ?_, rfl, hLetter, hValid, ?_, hGate⟩
    · change a.1 = (⟨a.1.1,
        R.restrict (Nat.le_succ a.1.1)⟩ :
          RawPartialTypeNode db du dd)
      rw [hOld]
    · exact hParameter
  refine ⟨b, ?_⟩
  rw [admissibleKptSTree_succ_eq]
  exact canonicalKptSucc_eq_some_of_step family hStep

end SuccessorTree.V10

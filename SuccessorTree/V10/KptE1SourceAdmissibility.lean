import SuccessorTree.V10.KptE1ParameterReindex
import SuccessorTree.V10.KptE1FiniteAgePullback

/-!
# Concrete admissibility of a retained Kpt successor candidate

This is the actual finite source-witness assembly, not another
axiomatically admissible successor. A target admissible complete L+ type
has a genuine finite forbidden-free L-age witness. Restrict to the
source shape-level coordinates and preserve the last ordinary vertex.
If the target new E cut comes from the source cut, then:

* the old source type is recovered exactly by shape-map reflection;
* the source old E columns and binary linkedness come from its genuine
  enumerated partial-structure witness;
* the new E/L column comes from the actual target column;
* the distinguished type-vertex socle and last ordinary E loop are
  inherited from genuine target admissibility; and
* forbidden L-age avoidance passes to the induced finite type-age
  pullback, with no E added to a forbidden witness.

The existing neutral-spacer construction then proves genuine source
admissibility. Identifying the source canonical parameter and invoking
its exact successor operation remain separate next steps.
-/

namespace SuccessorTree.V10

/-- The final ordinary E diagonal bit of an admissible Kpt type
vanishes. The ordinary vertex is literal in the representing
partial structure, so its E loop is ruled out by the canonical free
cut, without any independent loop hypothesis. -/
theorem PartialTypeWithE.admissible_lastOrdinary_noLoop
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (hAd : IsAdmissibleRawType family
      (⟨ell + 1, Q⟩ : RawPartialTypeNode db du dd)) :
    Q.eRelation (some (Fin.last ell)) (some (Fin.last ell)) = false := by
  obtain ⟨A, w, hw, hAvoid, hRaw⟩ := hAd
  have hCut : ell + 1 = A.freeLevel w :=
    congrArg Sigma.fst hRaw
  have hRecord : Q = A.partialTypeAt (ell + 1) w := by
    have hSigma :
        (⟨ell + 1, Q⟩ : RawPartialTypeNode db du dd) =
          (⟨ell + 1, A.partialTypeAt (ell + 1) w⟩ :
            RawPartialTypeNode db du dd) := by
      calc
        (⟨ell + 1, Q⟩ : RawPartialTypeNode db du dd) =
            A.rawTypeAtFree w := hRaw
        _ = (⟨ell + 1, A.partialTypeAt (ell + 1) w⟩ :
              RawPartialTypeNode db du dd) := by
          change
            (⟨A.freeLevel w,
              A.partialTypeAt (A.freeLevel w) w⟩ :
              RawPartialTypeNode db du dd) =
            (⟨ell + 1, A.partialTypeAt (ell + 1) w⟩ :
              RawPartialTypeNode db du dd)
          rw [← hCut]
    exact eq_of_heq (Sigma.mk.inj_iff.mp hSigma).2
  rw [hRecord]
  change A.E ell ell = false
  cases hE : A.E ell ell with
  | false => rfl
  | true =>
      have hImpossible : ell < A.freeLevel ell :=
        (A.E_iff_freeLevel ell ell).mp hE
      exact False.elim ((Nat.not_lt.mpr (A.freeLevel_le ell)) hImpossible)

/-- The genuine target successor has an admissible full L+ source
pullback once the source-level cut f has been identified. There is
no arbitrary source E-expansion, linkedness axiom, or forbidden-age
transport premise. The only cut condition is the actual equation
g=levelMap(f), which is supplied by the target's canonical image
parameter in the next assembly step. -/
theorem kptE1_reindexed_target_admissible
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (a : AdmissibleKptNode family)
    (Q : PartialTypeWithE ((F a).1.1 + 1) db du dd)
    (hTargetPred :
      Q.restrict (Nat.le_succ (F a).1.1) = (F a).1.2)
    (hTargetAd : IsAdmissibleRawType family
      (⟨(F a).1.1 + 1, Q⟩ : RawPartialTypeNode db du dd))
    (f : Nat) (hGate : f = 0 ∨ f < a.1.1)
    (hValid : ValidNewOrdinaryColumn Q
      (kptShapeLevelMap family F f)) :
    IsAdmissibleRawType family
      (⟨a.1.1 + 1,
        Q.reindexOrdinary (kptShapeLastIndexAtNode family F a)⟩ :
        RawPartialTypeNode db du dd) := by
  let n := a.1.1
  let rho := kptShapeLastIndexAtNode family F a
  let Qsource : PartialTypeWithE (n + 1) db du dd :=
    Q.reindexOrdinary rho
  have hMono : StrictMono rho := by
    intro i j hij
    change kptShapeLevelMap family F i.val <
      kptShapeLevelMap family F j.val
    exact (kptShapeLevelMap_strictMono family F) hij
  have hLast : rho (Fin.last n) = Fin.last (F a).1.1 :=
    kptShapeLastIndexAtNode_last family F a
  have hCutIff (i : Fin n) :
      (rho i.castSucc).val < kptShapeLevelMap family F f ↔
        i.val < f := by
    change kptShapeLevelMap family F i.val <
      kptShapeLevelMap family F f ↔ i.val < f
    constructor
    · intro h
      by_contra hnot
      have hle : f ≤ i.val := Nat.le_of_not_gt hnot
      have himageLe :=
        (kptShapeLevelMap_strictMono family F).monotone hle
      omega
    · intro h
      exact (kptShapeLevelMap_strictMono family F) h
  have hValidSource : ValidNewOrdinaryColumn Qsource f :=
    Q.reindexOrdinary_validNewColumn rho hMono hLast
      (kptShapeLevelMap family F f) hValid f hCutIff
  obtain ⟨A, w, hw, hAvoidA, hRawA⟩ := a.2
  have hFree : n = A.freeLevel w := congrArg Sigma.fst hRawA
  have hRecord : a.1.2 = A.partialTypeAt n w := by
    have hSigma :
        a.1 = (⟨n, A.partialTypeAt n w⟩ :
          RawPartialTypeNode db du dd) := by
      calc
        a.1 = A.rawTypeAtFree w := hRawA
        _ = (⟨n, A.partialTypeAt n w⟩ :
              RawPartialTypeNode db du dd) := by
          change
            (⟨A.freeLevel w,
              A.partialTypeAt (A.freeLevel w) w⟩ :
              RawPartialTypeNode db du dd) =
            (⟨n, A.partialTypeAt n w⟩ :
              RawPartialTypeNode db du dd)
          rw [← hFree]
    exact eq_of_heq (Sigma.mk.inj_iff.mp hSigma).2
  have hPrefix :
      Qsource.restrict (Nat.le_succ n) = A.partialTypeAt n w := by
    change
      (Q.reindexOrdinary (kptShapeLastIndexAtNode family F a)).restrict
        (Nat.le_succ a.1.1) = A.partialTypeAt a.1.1 w
    rw [kptShapeReindex_recovers_old_predecessor
      family F a Q hTargetPred]
    exact hRecord
  obtain ⟨hType, hReverse, hTypeLoop⟩ :=
    Q.reindexOrdinary_typeESocle family hTargetAd rho
  have hTargetLoop :
      Q.eRelation (some (Fin.last (F a).1.1))
        (some (Fin.last (F a).1.1)) = false :=
    Q.admissible_lastOrdinary_noLoop family hTargetAd
  have hNewLoop :
      Qsource.eRelation (some (Fin.last n)) (some (Fin.last n)) = false := by
    change Q.eRelation (some (rho (Fin.last n)))
      (some (rho (Fin.last n))) = false
    rw [hLast]
    exact hTargetLoop
  have hOld : ∀ v, v < n →
      A.freeLevel v = 0 ∨ A.freeLevel v < v :=
    e1OldPrefix_freeCut_spaced A n
  obtain ⟨hLinked, hColumns⟩ :=
    e1PaddedOldNew_from_admissible_prefix
      A w hw (le_of_eq hFree) Qsource hPrefix
      f hGate hValidSource hNewLoop
  have hAvoid :
      ∀ bad, bad ∈ family → bad.Avoids Qsource.ageModel :=
    PartialTypeWithE.reindexOrdinary_age_avoids family Q
      (n + 1) rho hMono hTargetAd
  exact e1PaddedSourceStructure_isAdmissible
    family Qsource A.freeLevel f hOld hGate
    hLinked hColumns hType hReverse hTypeLoop hAvoid

end SuccessorTree.V10

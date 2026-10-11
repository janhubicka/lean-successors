import SuccessorTree.V10.M3OneGapShapeMap
import SuccessorTree.V10.M3MiddleCanonicalStep
import SuccessorTree.V10.AdmissibleSigmaSTree
import Mathlib.Tactic

/-!
# M3: the actual one-gap map repeats the nth canonical successor input

The total source-selected finite M3 prescription is now extended by a
genuine ShapeMap in KptM skipping precisely ell. This file identifies
its source-level values with the manuscript's duplication rule:

At each level-ell source T and earlier ordinary coordinate n<ell,
take the canonical parameter list and terminal Sigma letter of the
(n+1)-prefix of T. The new value F(T) is exactly the canonical Kpt
successor of T with THESE SAME inputs, not merely any admissible
one-step extension.

The earlier free cut is computed in a finite representative of T.
The source's complete ordinary E-socle determines it uniquely
(the separate checked ordinary-coherence theorem). No single free
cut is assumed across distinct source types.

The statements below use the actual admissible Kpt STree, not the
temporary raw-letter graph or an abstract successor postulate.
-/

namespace SuccessorTree.V10

/-- For every admissible source T, the finite chosen middle clone
is a genuine canonical one-step successor of T whose exact
empty/singleton parameter list and terminal letter are those of
its old nth crossing. The bound d=freeLevel_A(n) is source-dependent. -/
theorem m3FiniteTarget_canonicalDuplication
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell)
    (T : PartialTypeWithE ell db du dd)
    (hT : IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd)) :
    let W := chooseM3Witness family T hT
    ∃ (a b : AdmissibleKptNode family)
      (p : List (AdmissibleKptNode family))
      (c : RawKptLetter db du dd),
      a.1 = (⟨ell,T⟩ : RawPartialTypeNode db du dd) ∧
      b.1 =
        (⟨ell+1,m3FiniteTarget family n hn T hT⟩ :
          RawPartialTypeNode db du dd) ∧
      IsCanonicalKptStep family a p c b ∧
      p.map Subtype.val =
        ((T.restrict (Nat.succ_le_of_lt hn)).canonicalParameterRecord
          (W.A.freeLevel n) (W.A.freeLevel_le n)).toList ∧
      c = (T.restrict (Nat.succ_le_of_lt hn)).terminalLetter := by
  let W := chooseM3Witness family T hT
  let B := middleCloneInsertPartial W.A ell n W.ell_le_size hn
  have hIns : IsLInsertion W.A B ell :=
    middleCloneInsertPartial_isLInsertion W.A ell n
      W.ell_le_size hn
  have hvB : insertAddress ell W.v < B.size := by
    rw [hIns.size_eq]
    by_cases hlt : W.v < ell
    · rw [insertAddress_below ell W.v hlt]
      omega
    · rw [insertAddress_above ell W.v (by omega)]
      omega
  have hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L :=
    middleCloneInsertPartial_preserves_avoidance family W.A ell n
      W.ell_le_size hn W.avoids
  let a : AdmissibleKptNode family :=
    ⟨W.A.rawTypeAtFree W.v,
      ⟨W.A,W.v,W.hv,W.avoids,rfl⟩⟩
  let b : AdmissibleKptNode family :=
    ⟨B.rawTypeAtFree (insertAddress ell W.v),
      ⟨B,insertAddress ell W.v,hvB,hAvoidB,rfl⟩⟩
  obtain ⟨p,c,hStep,hPar,hLetter⟩ :=
    middleCloneInsertPartial_canonicalStep family W.A ell n
      W.ell_le_size hn W.v W.hv W.freeLevel_eq W.avoids
  have haRaw : a.1 =
      (⟨ell,T⟩ : RawPartialTypeNode db du dd) :=
    W.raw_eq.symm
  have hBFree : B.freeLevel (insertAddress ell W.v) = ell+1 :=
    middleCloneInsertPartial_prescribed_vertex_freeLevel W.A
      ell n W.ell_le_size hn W.v W.hv W.freeLevel_eq
  have hbRaw : b.1 =
      (⟨ell+1,m3FiniteTarget family n hn T hT⟩ :
        RawPartialTypeNode db du dd) := by
    change B.rawTypeAtFree (insertAddress ell W.v) =
      (⟨ell+1,B.partialTypeAt (ell+1)
        (insertAddress ell W.v)⟩ : RawPartialTypeNode db du dd)
    change
      (⟨B.freeLevel (insertAddress ell W.v),
        B.partialTypeAt (B.freeLevel (insertAddress ell W.v))
          (insertAddress ell W.v)⟩ : RawPartialTypeNode db du dd) = _
    rw [hBFree]
  have hSource : T = W.A.partialTypeAt ell W.v :=
    record_eq_of_rawTypeAtFree T W.A W.v W.raw_eq
  have hEarlier : T.restrict (Nat.succ_le_of_lt hn) =
      W.A.partialTypeAt (n+1) W.v := by
    rw [hSource]
    exact W.A.partialTypeAt_restrict (n+1) ell W.v
      (Nat.succ_le_of_lt hn)
  have hExactPar : p.map Subtype.val =
      ((T.restrict (Nat.succ_le_of_lt hn)).canonicalParameterRecord
        (W.A.freeLevel n) (W.A.freeLevel_le n)).toList := by
    rw [hEarlier]
    exact hPar
  have hExactLetter : c =
      (T.restrict (Nat.succ_le_of_lt hn)).terminalLetter := by
    rw [hEarlier]
    exact hLetter
  exact ⟨a,b,p,c,haRaw,hbRaw,hStep,hExactPar,hExactLetter⟩

/-- The actual shape map of M3 *duplicates* the earlier nth canonical
successor input, not just the lower ordinary clone column. This is
the exact S-tree operation with an ADMISSIBLE Sigma letter, complete
empty/singleton parameter list and full L+ output value. -/
theorem m3OneGapShapeMap_duplicates
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell n : Nat) (hn : n < ell) :
    ∃ Φ : SuccessorTree.ShapeMap (admissibleKptSTree family),
      Φ ∈ KptM family ∧
      Φ.SkipsOnly ell ∧
      ∀ (T : PartialTypeWithE ell db du dd)
        (hT : IsAdmissibleRawType family
          (⟨ell,T⟩ : RawPartialTypeNode db du dd)),
        let W := chooseM3Witness family T hT
        ∃ (p : List (AdmissibleKptNode family))
          (c : AdmissibleKptSigma family),
          (admissibleKptSTree family).succ
            (⟨⟨ell,T⟩,hT⟩ : AdmissibleKptNode family) p c =
            some (Φ (⟨⟨ell,T⟩,hT⟩ : AdmissibleKptNode family)) ∧
          p.map Subtype.val =
            ((T.restrict (Nat.succ_le_of_lt hn)).canonicalParameterRecord
              (W.A.freeLevel n) (W.A.freeLevel_le n)).toList ∧
          c.1 =
            (T.restrict (Nat.succ_le_of_lt hn)).terminalLetter := by
  obtain ⟨Φ,hM,hSkip,hAgreement⟩ :=
    m3OneGapShapeMap_exists family ell n hn
  refine ⟨Φ,hM,hSkip,?_⟩
  intro T hT
  obtain ⟨a,b,p,c,haRaw,hbRaw,hStep,hPar,hLetter⟩ :=
    m3FiniteTarget_canonicalDuplication family n hn T hT
  have ha : a = (⟨⟨ell,T⟩,hT⟩ : AdmissibleKptNode family) :=
    Subtype.ext haRaw
  have hb : b = Φ (⟨⟨ell,T⟩,hT⟩ : AdmissibleKptNode family) :=
    Subtype.ext (hbRaw.trans (hAgreement T hT).symm)
  have hExactStep : IsCanonicalKptStep family
      (⟨⟨ell,T⟩,hT⟩ : AdmissibleKptNode family)
      p c (Φ (⟨⟨ell,T⟩,hT⟩ : AdmissibleKptNode family)) := by
    simpa only [ha,hb] using hStep
  let cAd : AdmissibleKptSigma family :=
    ⟨c,canonicalKptStep_letter_admissible family hExactStep⟩
  refine ⟨p,cAd,?_,hPar,hLetter⟩
  change canonicalKptSucc family
    (⟨⟨ell,T⟩,hT⟩ : AdmissibleKptNode family) p c =
    some (Φ (⟨⟨ell,T⟩,hT⟩ : AdmissibleKptNode family))
  exact canonicalKptSucc_eq_some_of_step family hExactStep

end SuccessorTree.V10

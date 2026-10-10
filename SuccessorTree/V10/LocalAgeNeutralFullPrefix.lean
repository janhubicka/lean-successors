import SuccessorTree.V10.LocalAgeNeutralSkip
import Mathlib.Tactic

/-!
# The neutral Kpt gap insertion preserves ALL actual prefix relations

The same old-atom transport calculation has a simpler form strictly below
the inserted coordinate: no new socle vertex occurs, so the entire extracted
L+ type through such a cut stays identical. This proves the crossing-gap
case: a short prefix below ell is unchanged and remains an actual prefix
of the neutral image of a longer source node.

Together with the independently checked above-gap prefix-replica argument
and the trivial below-gap identity, this proves that the total neutral
insertion is monotone on the actual admissible Kpt forest, with no omitted
case at the gap. Injectivity and weak successor preservation are still
required before calling this total function a ShapeMap.
-/

namespace SuccessorTree.V10

/-- Neutral insertion changes no induced L+ type AT OR BELOW the inserted
level, since its new coordinate has not entered the socle yet. -/
theorem neutralInsert_type_below_gap
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (v d : Nat) (hv : v < A.size) (hd : d ≤ ell) :
    (neutralInsert A ell hell hellPos).partialTypeAt d
        (insertAddress ell v) = A.partialTypeAt d v := by
  have hIns := neutralInsert_isLInsertion A ell hell hellPos
  have hCut : d ≤ A.size := hd.trans hell
  have hCoord : ∀ a : Option (Fin d),
      prefixVertexIndex (insertAddress ell v) a =
        insertAddress ell (prefixVertexIndex v a) := by
    intro a
    cases a with
    | none => rfl
    | some a =>
        change a.val = insertAddress ell a.val
        exact (insertAddress_below ell a.val
          (lt_of_lt_of_le a.isLt hd)).symm
  have hIn : ∀ a : Option (Fin d), prefixVertexIndex v a < A.size :=
    fun a => prefixVertexIndex_inside v A.size hv hCut a
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      change (neutralInsert A ell hell hellPos).L.binary
          (prefixVertexIndex (insertAddress ell v) a)
          (prefixVertexIndex (insertAddress ell v) b) r =
        A.L.binary (prefixVertexIndex v a) (prefixVertexIndex v b) r
      rw [hCoord a, hCoord b]
      exact hIns.binary _ _ (hIn a) (hIn b) r
    · intro a r
      change (neutralInsert A ell hell hellPos).L.unary
          (prefixVertexIndex (insertAddress ell v) a) r =
        A.L.unary (prefixVertexIndex v a) r
      rw [hCoord a]
      exact hIns.unary _ (hIn a) r
    · intro a r
      change (neutralInsert A ell hell hellPos).L.diagonal
          (prefixVertexIndex (insertAddress ell v) a) r =
        A.L.diagonal (prefixVertexIndex v a) r
      rw [hCoord a]
      exact hIns.diagonal _ (hIn a) r
  · intro a b
    change (neutralInsert A ell hell hellPos).E
        (prefixVertexIndex (insertAddress ell v) a)
        (prefixVertexIndex (insertAddress ell v) b) =
      A.E (prefixVertexIndex v a) (prefixVertexIndex v b)
    rw [hCoord a, hCoord b]
    exact neutralInsert_old_E_eq A ell hell hellPos
      _ _ (hIn a) (hIn b)

/-- Prefix compatibility across the skipped level: the smaller type lies
below ell and is therefore fixed, but the larger type is shifted upward.
The copied low socle gives their genuine Kpt prefix relationship. -/
theorem neutralKptSkip_prefix_crossing
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a b : AdmissibleKptNode family)
    (hba : b ≤ a)
    (hbLow : b.1.1 < ell) (haHigh : ell ≤ a.1.1) :
    neutralKptSkip family ell hellPos b ≤
      neutralKptSkip family ell hellPos a := by
  have hRawBA : b.1 ≤ a.1 := hba
  let d : Nat := b.1.1
  have hda : d ≤ a.1.1 := hRawBA.1
  obtain ⟨A, v, hellA, hv, hAvoidA, hRawA, hImgA⟩ :=
    neutralKptImage_isImage family ell hellPos a haHigh
  have hSourceLev : a.1.1 = A.freeLevel v :=
    congrArg Sigma.fst hRawA
  have hOldCut : ell ≤ A.freeLevel v := by omega
  have hSigmaA :
      (⟨a.1.1, a.1.2⟩ : RawPartialTypeNode db du dd) =
      (⟨A.freeLevel v, A.partialTypeAt (A.freeLevel v) v⟩ :
        RawPartialTypeNode db du dd) := hRawA
  have hHEq : HEq a.1.2 (A.partialTypeAt (A.freeLevel v) v) :=
    (Sigma.mk.inj_iff.mp hSigmaA).2
  have hAType : a.1.2 = A.partialTypeAt a.1.1 v := by
    rw [← hSourceLev] at hHEq
    exact eq_of_heq hHEq
  have hBType : b.1.2 = A.partialTypeAt d v := by
    calc
      b.1.2 = a.1.2.restrict hda := hRawBA.2
      _ = (A.partialTypeAt a.1.1 v).restrict hda := by rw [hAType]
      _ = A.partialTypeAt d v :=
        A.partialTypeAt_restrict d a.1.1 v hda
  have hBNode :
      b.1 = (⟨d, A.partialTypeAt d v⟩ : RawPartialTypeNode db du dd) := by
    calc
      b.1 = (⟨d, b.1.2⟩ : RawPartialTypeNode db du dd) :=
        (Sigma.eta b.1).symm
      _ = (⟨d, A.partialTypeAt d v⟩ : RawPartialTypeNode db du dd) :=
        congrArg (Sigma.mk d) hBType
  let B := neutralInsert A ell hellA hellPos
  have hBFree : B.freeLevel (insertAddress ell v) =
      A.freeLevel v + 1 := by
    have h := neutralInsert_freeLevel_old A ell hellA hellPos v hv
    simpa only [B, if_neg (Nat.not_lt.mpr hOldCut)] using h
  have hLowType : B.partialTypeAt d (insertAddress ell v) =
      A.partialTypeAt d v :=
    neutralInsert_type_below_gap A ell hellA hellPos v d hv
      (Nat.le_of_lt hbLow)
  have hBImage :
      b.1 = (⟨d, B.partialTypeAt d (insertAddress ell v)⟩ :
        RawPartialTypeNode db du dd) := by
    calc
      b.1 = (⟨d, A.partialTypeAt d v⟩ :
        RawPartialTypeNode db du dd) := hBNode
      _ = (⟨d, B.partialTypeAt d (insertAddress ell v)⟩ :
        RawPartialTypeNode db du dd) :=
          congrArg (Sigma.mk d) hLowType.symm
  have hInsideCut : d ≤ B.freeLevel (insertAddress ell v) := by
    rw [hBFree]
    omega
  have hPrefix :
      b.1 ≤ B.rawTypeAtFree (insertAddress ell v) := by
    rw [hBImage]
    exact rawPartialType_prefix_of_cut B (insertAddress ell v) d hInsideCut
  change
    (neutralKptSkip family ell hellPos b).1 ≤
      (neutralKptSkip family ell hellPos a).1
  rw [neutralKptSkip_fixed_below family ell hellPos b hbLow,
    neutralKptSkip_above family ell hellPos a haHigh, hImgA]
  exact hPrefix

/-- The total neutral insertion preserves every actual Kpt prefix relation,
including the crossing-gap case. This is still weaker than ShapeMap:
injectivity and weak successor preservation remain to be constructed. -/
theorem neutralKptSkip_prefix
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a b : AdmissibleKptNode family)
    (hba : b ≤ a) :
    neutralKptSkip family ell hellPos b ≤
      neutralKptSkip family ell hellPos a := by
  by_cases haLow : a.1.1 < ell
  · exact neutralKptSkip_prefix_below family ell hellPos a b hba haLow
  · by_cases hbHigh : ell ≤ b.1.1
    · exact neutralKptSkip_prefix_above family ell hellPos a b hba hbHigh
    · have hbLow : b.1.1 < ell := by omega
      have haHigh : ell ≤ a.1.1 := by omega
      exact neutralKptSkip_prefix_crossing family ell hellPos
        a b hba hbLow haHigh

end SuccessorTree.V10

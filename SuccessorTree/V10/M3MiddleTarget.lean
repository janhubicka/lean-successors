import SuccessorTree.V10.M3MiddleFreeCut
import SuccessorTree.V10.PrescribedETransport
import SuccessorTree.V10.AdmissibleKptPrefix
import Mathlib.Tactic

/-!
# Actual M3 middle-clone target is an admissible one-step type

The genuine gated insertion retains every atom in the source
L+ partial type through ell, including all E pairs and both directed
positive/absent binary atoms. Its shifted type vertex acquires
free cut ell+1. The separately verified finite forbidden-age theorem
therefore provides an admissible Kpt successor target, not just a
formally legal next L+ record.

This is a finite existence theorem. Agreement of its actual parameter
and terminal Sigma letter with the earlier n-th crossing, and
choice-independence of the target over source representations, remain
separate parts of the global M3 proof.
-/

namespace SuccessorTree.V10

/-- Every complete source L+ type at a cut d≤ell is retained
literally in the actual middle-clone insertion. This includes the
distinguished type vertex, all old E entries, and absent L-atoms. -/
theorem middleCloneInsertPartial_type_below_gap
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell)
    (v d : Nat) (hv : v < A.size) (hd : d ≤ ell) :
    (middleCloneInsertPartial A ell n hell hn).partialTypeAt d
      (insertAddress ell v) = A.partialTypeAt d v := by
  let B := middleCloneInsertPartial A ell n hell hn
  have hIns : IsLInsertion A B ell :=
    middleCloneInsertPartial_isLInsertion A ell n hell hn
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
  have hIn : ∀ a : Option (Fin d),
      prefixVertexIndex v a < A.size :=
    fun a => prefixVertexIndex_inside v A.size hv hCut a
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      change B.L.binary
          (prefixVertexIndex (insertAddress ell v) a)
          (prefixVertexIndex (insertAddress ell v) b) r =
        A.L.binary (prefixVertexIndex v a)
          (prefixVertexIndex v b) r
      rw [hCoord a,hCoord b]
      exact hIns.binary _ _ (hIn a) (hIn b) r
    · intro a r
      change B.L.unary (prefixVertexIndex (insertAddress ell v) a) r =
        A.L.unary (prefixVertexIndex v a) r
      rw [hCoord a]
      exact hIns.unary _ (hIn a) r
    · intro a r
      change B.L.diagonal (prefixVertexIndex (insertAddress ell v) a) r =
        A.L.diagonal (prefixVertexIndex v a) r
      rw [hCoord a]
      exact hIns.diagonal _ (hIn a) r
  · intro a b
    change B.E (prefixVertexIndex (insertAddress ell v) a)
        (prefixVertexIndex (insertAddress ell v) b) =
      A.E (prefixVertexIndex v a) (prefixVertexIndex v b)
    rw [hCoord a,hCoord b,
      middleCloneInsertPartial_E_eq A ell n hell hn]
    have hPos : 0 < ell := by omega
    exact insertE_old_pair_eq A ell (A.freeLevel n) hell hPos
      (prefixVertexIndex v a) (prefixVertexIndex v b)
      (hIn a) (hIn b)

/-- The inserted target node is genuinely admissible in the same
normalized forbidden-free Kpt family, using the checked finite
forbidden-age preservation of the actual gated constructor. -/
theorem middleCloneInsertPartial_target_admissible
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell)
    (v : Nat) (hv : v < A.size)
    (hOldFree : A.freeLevel v = ell)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    IsAdmissibleRawType family
      (⟨ell+1,
        (middleCloneInsertPartial A ell n hell hn).partialTypeAt (ell+1)
          (insertAddress ell v)⟩ : RawPartialTypeNode db du dd) := by
  let B := middleCloneInsertPartial A ell n hell hn
  have hIns : IsLInsertion A B ell :=
    middleCloneInsertPartial_isLInsertion A ell n hell hn
  have hV : insertAddress ell v < B.size := by
    rw [hIns.size_eq]
    by_cases hlt : v < ell
    · rw [insertAddress_below ell v hlt]
      omega
    · rw [insertAddress_above ell v (by omega)]
      omega
  have hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L :=
    middleCloneInsertPartial_preserves_avoidance
      family A ell n hell hn hAvoid
  have hNewFree : B.freeLevel (insertAddress ell v) = ell+1 :=
    middleCloneInsertPartial_prescribed_vertex_freeLevel
      A ell n hell hn v hv hOldFree
  refine ⟨B,insertAddress ell v,hV,hAvoidB,?_⟩
  change (⟨ell+1,B.partialTypeAt (ell+1) (insertAddress ell v)⟩ :
      RawPartialTypeNode db du dd) =
    (⟨B.freeLevel (insertAddress ell v),
      B.partialTypeAt (B.freeLevel (insertAddress ell v))
        (insertAddress ell v)⟩ : RawPartialTypeNode db du dd)
  rw [hNewFree]

/-- B1 for the actual candidate: its complete one-step output type
restricts to the original complete source type at level ell. -/
theorem middleCloneInsertPartial_target_restrict
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell)
    (v : Nat) (hv : v < A.size) :
    ((middleCloneInsertPartial A ell n hell hn).partialTypeAt (ell+1)
      (insertAddress ell v)).restrict (Nat.le_succ ell) =
        A.partialTypeAt ell v := by
  let B := middleCloneInsertPartial A ell n hell hn
  calc
    (B.partialTypeAt (ell+1) (insertAddress ell v)).restrict
        (Nat.le_succ ell) =
      B.partialTypeAt ell (insertAddress ell v) :=
        B.partialTypeAt_restrict ell (ell+1)
          (insertAddress ell v) (Nat.le_succ ell)
    _ = A.partialTypeAt ell v :=
      middleCloneInsertPartial_type_below_gap
        A ell n hell hn v ell hv le_rfl

end SuccessorTree.V10

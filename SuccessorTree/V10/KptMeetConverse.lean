import SuccessorTree.V10.KptMeetBridge
import SuccessorTree.V10.SocleBound

/-!
# Recovering first binary disagreement from a nontrivial Kpt meet

Lemma 6.49 starts with a nontrivial meet of actual partial types,
rather than with a chosen binary trace mismatch. The Kpt forest now
has its genuine induced L+ ancestor and meet operations, so we can
derive the first mismatch and the necessary free-cut inequalities
directly from the meet's strict position below both original nodes.

Both original vertices are taken in the SAME enumerated finite
partial structure. The remaining H-specific step is to prove the
exact numerical L-model has the full traces used by the mixed-
generation classifier, including odd fake vertices and the reverse
binary orientation. Neither that identification nor the ultimate
positive-generation classification is assumed below.
-/

namespace SuccessorTree.V10

/-- The genuine nontrivial meet of two represented Kpt originals
induces a first binary discrepancy at its own level, before both
free E cuts. Equality of the complete roots and the preceding
binary cross-atoms is DERIVED from the common meet, not assumed.

Unlike the converse, the hypothesis is exactly the genuine
LevelTree meet and its two strict inequalities, as in Lemma 6.49. -/
theorem admissibleKpt_nontrivial_meet_recovers_binary
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (v w : Nat)
    (hAdV : IsAdmissibleRawType family (A.rawTypeAtFree v))
    (hAdW : IsAdmissibleRawType family (A.rawTypeAtFree w))
    (hCommon : ∃ c : AdmissibleKptNode family,
      c ≤ (⟨A.rawTypeAtFree v, hAdV⟩ : AdmissibleKptNode family) ∧
      c ≤ (⟨A.rawTypeAtFree w, hAdW⟩ : AdmissibleKptNode family))
    (hStrictV :
      LevelTree.meet
        (⟨A.rawTypeAtFree v, hAdV⟩ : AdmissibleKptNode family)
        (⟨A.rawTypeAtFree w, hAdW⟩ : AdmissibleKptNode family) ≠
      (⟨A.rawTypeAtFree v, hAdV⟩ : AdmissibleKptNode family))
    (hStrictW :
      LevelTree.meet
        (⟨A.rawTypeAtFree v, hAdV⟩ : AdmissibleKptNode family)
        (⟨A.rawTypeAtFree w, hAdW⟩ : AdmissibleKptNode family) ≠
      (⟨A.rawTypeAtFree w, hAdW⟩ : AdmissibleKptNode family)) :
    ∃ d : Nat,
      LevelTree.lev (LevelTree.meet
        (⟨A.rawTypeAtFree v, hAdV⟩ : AdmissibleKptNode family)
        (⟨A.rawTypeAtFree w, hAdW⟩ : AdmissibleKptNode family)) = d ∧
      d + 1 ≤ A.freeLevel v ∧
      d + 1 ≤ A.freeLevel w ∧
      SameAmbientCrossType A v w d ∧
      ((∃ r : Fin db, A.L.binary d v r ≠ A.L.binary d w r) ∨
       (∃ r : Fin db, A.L.binary v d r ≠ A.L.binary w d r)) := by
  let a : AdmissibleKptNode family := ⟨A.rawTypeAtFree v, hAdV⟩
  let b : AdmissibleKptNode family := ⟨A.rawTypeAtFree w, hAdW⟩
  let d := LevelTree.lev (LevelTree.meet a b)
  have hma : LevelTree.meet a b ≤ a :=
    LevelTree.meet_le_left hCommon
  have hmb : LevelTree.meet a b ≤ b :=
    LevelTree.meet_le_right hCommon
  have haStrict : LevelTree.meet a b < a :=
    lt_of_le_of_ne hma hStrictV
  have hbStrict : LevelTree.meet a b < b :=
    lt_of_le_of_ne hmb hStrictW
  have hv : d + 1 ≤ A.freeLevel v := by
    have h := LevelTree.lt_level_lt haStrict
    change d < A.freeLevel v at h
    omega
  have hw : d + 1 ≤ A.freeLevel w := by
    have h := LevelTree.lt_level_lt hbStrict
    change d < A.freeLevel w at h
    omega
  have hdav : d ≤ LevelTree.lev a := by
    change d ≤ A.freeLevel v
    omega
  have hdaw : d ≤ LevelTree.lev b := by
    change d ≤ A.freeLevel w
    omega
  have hnav : d + 1 ≤ LevelTree.lev a := by
    change d + 1 ≤ A.freeLevel v
    exact hv
  have hnaw : d + 1 ≤ LevelTree.lev b := by
    change d + 1 ≤ A.freeLevel w
    exact hw
  have hPrevAnc :
      LevelTree.ancestor a d hdav =
        LevelTree.ancestor b d hdaw := by
    have hLevMeet : LevelTree.lev (LevelTree.meet a b) = d := rfl
    have hToA : LevelTree.meet a b =
        LevelTree.ancestor a d hdav :=
      LevelTree.eq_ancestor_of_le hma hLevMeet hdav
    have hToB : LevelTree.meet a b =
        LevelTree.ancestor b d hdaw :=
      LevelTree.eq_ancestor_of_le hmb hLevMeet hdaw
    exact hToA.symm.trans hToB
  have hNextAnc :
      LevelTree.ancestor a (d + 1) hnav ≠
        LevelTree.ancestor b (d + 1) hnaw := by
    intro heq
    have hxA : LevelTree.ancestor a (d + 1) hnav ≤ a :=
      LevelTree.ancestor_le a (d + 1) hnav
    have hxB : LevelTree.ancestor a (d + 1) hnav ≤ b := by
      rw [heq]
      exact LevelTree.ancestor_le b (d + 1) hnaw
    have hxMeet : LevelTree.ancestor a (d + 1) hnav ≤
        LevelTree.meet a b := LevelTree.le_meet hxA hxB
    have hLev := LevelTree.level_le_of_le hxMeet
    have hAncLev : LevelTree.lev
        (LevelTree.ancestor a (d + 1) hnav) = d + 1 :=
      LevelTree.level_ancestor a (d + 1) hnav
    rw [hAncLev] at hLev
    change d + 1 ≤ d at hLev
    omega
  have hPrev :
      A.partialTypeAt d v = A.partialTypeAt d w :=
    (admissibleKpt_original_ancestors_eq_iff family A v w d
      hAdV hAdW (by omega) (by omega)).1 hPrevAnc
  have hNext :
      A.partialTypeAt (d + 1) v ≠ A.partialTypeAt (d + 1) w := by
    intro heq
    exact hNextAnc
      ((admissibleKpt_original_ancestors_eq_iff family A v w
          (d + 1) hAdV hAdW hv hw).2 heq)
  have hRoot : A.partialTypeAt 0 v = A.partialTypeAt 0 w :=
    fullPartialType_eq_at_smaller A v w 0 d (Nat.zero_le d) hPrev
  have hBefore : SameAmbientCrossType A v w d :=
    (sameAmbient_partialType_eq_iff_cross A v w d
      (by omega) (by omega) hRoot).1 hPrev
  have hMismatch :=
    binary_witness_of_first_fullPrefix_difference
      A v w d hv hw hRoot hPrev hNext
  exact ⟨d, rfl, hv, hw, hBefore, hMismatch⟩

/-- The sharp non-top-generation domain guard is a geometric
CONSEQUENCE of a genuine nontrivial meet, not an extra combinatorial
hypothesis. A meet at iota(p,m) can occur below a lower-generation
type with free level iota(j-1,m-1)+1 only if p+1<j.

This closes the precise off-by-one check raised by the v10 review. -/
theorem admissibleKpt_nontrivial_meet_sharp_nonTop_guard
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (a b : AdmissibleKptNode family)
    (hCommon : ∃ c : AdmissibleKptNode family, c ≤ a ∧ c ≤ b)
    (hStrictA : LevelTree.meet a b ≠ a)
    (k p j m : Nat)
    (hm : 0 < m) (hmk : m < k) (hj : 0 < j)
    (haLevel : LevelTree.lev a = nonTopFreeCut k j m)
    (hMeetLevel : LevelTree.lev (LevelTree.meet a b) =
      hPosition k p m) :
    p + 1 < j := by
  have hMeetLt : LevelTree.meet a b < a :=
    lt_of_le_of_ne (LevelTree.meet_le_left hCommon) hStrictA
  have hLevLt := LevelTree.lt_level_lt hMeetLt
  rw [haLevel, hMeetLevel] at hLevLt
  exact (positivePosition_below_free_iff k p j m hm hmk hj).1 hLevLt

end SuccessorTree.V10

import SuccessorTree.V10.LocalAgeNeutralAdmissible
import Mathlib.Tactic

/-!
# The neutral Kpt image has no dependence on the chosen ambient witness

The existence theorem in LocalAgeNeutralAdmissible obtains an image by
choosing one forbidden-free finite partial structure representing its source
type. A priori the choice may vary. We show that it cannot change the image.

First, equality of actual RawPartialTypeNode sigma pairs gives equality of
both canonical E free cuts and complete L+ record values at the common cut.
Then the representation-independence theorem proves equality of the two
inserted complete records; the exact E-cut transport matches their levels.
Thus the neutral-image relation is functional and the Classical.choice
selector has a proved source-independent result.

This is the first actual *well-defined* insertion operation on the upper
part of the admissible Kpt type tree, not merely a numerical insertion
on ambient structures. The levels below ell, injectivity and weak successor
preservation remain to be proved before installing it as a ShapeMap.
-/

namespace SuccessorTree.V10

/-- Equal complete original type nodes have the same determined free level
and the same induced full L+ type at that level, even when their ambient
partial structures differ. -/
theorem rawTypeAtFree_eq_data
    {db du dd : Nat}
    (A C : EnumeratedPartialStructure db du dd)
    (v w : Nat)
    (h : A.rawTypeAtFree v = C.rawTypeAtFree w) :
    A.freeLevel v = C.freeLevel w ∧
      A.partialTypeAt (A.freeLevel v) v =
        C.partialTypeAt (A.freeLevel v) w := by
  have hlev : A.freeLevel v = C.freeLevel w :=
    congrArg Sigma.fst h
  have hpair :
      (⟨A.freeLevel v, A.partialTypeAt (A.freeLevel v) v⟩ :
        RawPartialTypeNode db du dd) =
      (⟨C.freeLevel w, C.partialTypeAt (C.freeLevel w) w⟩ :
        RawPartialTypeNode db du dd) := h
  have hHEq : HEq (A.partialTypeAt (A.freeLevel v) v)
      (C.partialTypeAt (C.freeLevel w) w) :=
    (Sigma.mk.inj_iff.mp hpair).2
  have hEq : A.partialTypeAt (A.freeLevel v) v =
      C.partialTypeAt (A.freeLevel v) w := by
    rw [← hlev] at hHEq
    exact eq_of_heq hHEq
  exact ⟨hlev, hEq⟩

/-- The neutral-image relation on ACTUAL admissible Kpt nodes is functional.
Different representing finite structures and different original vertices do
not change the image. -/
theorem neutralKptImage_graph_unique
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a : AdmissibleKptNode family)
    (hlev : ell ≤ a.1.1)
    (b c : AdmissibleKptNode family)
    (hb : IsNeutralKptImage family ell hellPos a b)
    (hc : IsNeutralKptImage family ell hellPos a c) :
    b = c := by
  obtain ⟨A, v, hellA, hv, hAvoidA, hRawA, hImgA⟩ := hb
  obtain ⟨C, w, hellC, hw, hAvoidC, hRawC, hImgC⟩ := hc
  have hRaw : A.rawTypeAtFree v = C.rawTypeAtFree w :=
    hRawA.symm.trans hRawC
  obtain ⟨hCutEq, hTypeEq⟩ := rawTypeAtFree_eq_data A C v w hRaw
  let cut : Nat := A.freeLevel v
  have hOrigLev : a.1.1 = A.freeLevel v :=
    congrArg Sigma.fst hRawA
  have hEllCut : ell ≤ cut := by omega
  have hCutA : cut ≤ A.size := by
    have h := A.freeLevel_le v
    omega
  have hCutC : cut ≤ C.size := by
    have h := C.freeLevel_le w
    omega
  let B := neutralInsert A ell hellA hellPos
  let D := neutralInsert C ell hellC hellPos
  have hFreeA : B.freeLevel (insertAddress ell v) = cut + 1 := by
    have h := neutralInsert_freeLevel_old A ell hellA hellPos v hv
    have hn : ¬ A.freeLevel v < ell := Nat.not_lt.mpr hEllCut
    simpa only [B, cut, hn, ite_false] using h
  have hFreeC : D.freeLevel (insertAddress ell w) = cut + 1 := by
    have h := neutralInsert_freeLevel_old C ell hellC hellPos w hw
    have hn : ¬ C.freeLevel w < ell := by omega
    rw [if_neg hn, ←hCutEq] at h
    exact h
  have hT :
      B.partialTypeAt (cut + 1) (insertAddress ell v) =
        D.partialTypeAt (cut + 1) (insertAddress ell w) :=
    neutralInsert_partialType_independent A C ell cut v w
      hellA hellC hellPos hEllCut hCutA hCutC hv hw hTypeEq
  have hImageRaw :
      B.rawTypeAtFree (insertAddress ell v) =
        D.rawTypeAtFree (insertAddress ell w) := by
    change
      (⟨B.freeLevel (insertAddress ell v),
         B.partialTypeAt (B.freeLevel (insertAddress ell v))
           (insertAddress ell v)⟩ : RawPartialTypeNode db du dd) =
      (⟨D.freeLevel (insertAddress ell w),
         D.partialTypeAt (D.freeLevel (insertAddress ell w))
           (insertAddress ell w)⟩ : RawPartialTypeNode db du dd)
    rw [hFreeA, hFreeC]
    exact congrArg (Sigma.mk (cut+1)) hT
  have hbc : b.1 = c.1 := by
    calc
      b.1 = B.rawTypeAtFree (insertAddress ell v) := hImgA
      _ = D.rawTypeAtFree (insertAddress ell w) := hImageRaw
      _ = c.1 := hImgC.symm
  exact Subtype.ext hbc

/-- The Classically chosen Kpt image is exactly the image obtained from
ANY forbidden-free ambient witness of its original type. This removes
the hidden representation choice from the uniform map construction. -/
theorem neutralKptImage_eq_of_representation
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a : AdmissibleKptNode family) (hlev : ell ≤ a.1.1)
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (hv : v < A.size)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hRaw : a.1 = A.rawTypeAtFree v)
    (hell : ell ≤ A.size) :
    (neutralKptImage family ell hellPos a hlev).1 =
      (neutralInsert A ell hell hellPos).rawTypeAtFree
        (insertAddress ell v) := by
  have hvGE : ell ≤ v := by
    have hSrc : a.1.1 = A.freeLevel v :=
      congrArg Sigma.fst hRaw
    have hbound := A.freeLevel_le v
    omega
  have hvB :
      insertAddress ell v < (neutralInsert A ell hell hellPos).size := by
    change insertAddress ell v < A.size+1
    rw [insertAddress_above ell v hvGE]
    omega
  have hAvoidB : ∀ bad, bad ∈ family →
      bad.Avoids (neutralInsert A ell hell hellPos).L :=
    neutralInsert_preserves_avoidance family A ell hell hellPos hAvoid
  let b : AdmissibleKptNode family :=
    ⟨(neutralInsert A ell hell hellPos).rawTypeAtFree (insertAddress ell v),
      ⟨neutralInsert A ell hell hellPos, insertAddress ell v,
        hvB, hAvoidB, rfl⟩⟩
  have hCandidate : IsNeutralKptImage family ell hellPos a b :=
    ⟨A, v, hell, hv, hAvoid, hRaw, rfl⟩
  have hEqual :
      neutralKptImage family ell hellPos a hlev = b :=
    neutralKptImage_graph_unique family ell hellPos a hlev
      _ b (neutralKptImage_isImage family ell hellPos a hlev)
      hCandidate
  exact congrArg Subtype.val hEqual

end SuccessorTree.V10

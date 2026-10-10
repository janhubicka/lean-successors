import SuccessorTree.V10.LocalAgeNeutralFullPrefix
import Mathlib.Tactic

/-!
# Injectivity of the total neutral insertion on genuine admissible types

All old L+ atoms survive insertion. Thus equality of complete inserted
types implies equality of the ORIGINAL complete types when restricted
to the shifted old coordinates. This reflection result is the reverse of
the representation-independence theorem and includes absent directed
binary facts, every singleton atom, and every auxiliary E pair.

The total neutral Kpt map preserves each source level by the explicit
strictly increasing one-gap function. Comparing image levels forces the
original levels to agree. Nodes below the gap are fixed. Above it,
using the actual ambient witnesses of the two selected Kpt images,
the reflection theorem forces their original full raw records to agree.
Hence the total candidate gap map is injective on ACTUAL Kpt nodes.

Only weak successor preservation, with exact parameter list and terminal
letter, is left before this neutral map qualifies as a ShapeMap.
-/

namespace SuccessorTree.V10

/-- Equality of full inserted types reflects equality of EVERY original
L+ atom at the shorter source cut. No loss occurs on the old coordinates. -/
theorem neutralInsert_partialType_reflects
    {db du dd : Nat}
    (A C : EnumeratedPartialStructure db du dd)
    (ell cut v w : Nat)
    (hellA : ell ≤ A.size) (hellC : ell ≤ C.size) (hellPos : 0 < ell)
    (hCutA : cut ≤ A.size) (hCutC : cut ≤ C.size)
    (hv : v < A.size) (hw : w < C.size)
    (hAfter :
      (neutralInsert A ell hellA hellPos).partialTypeAt
          (cut+1) (insertAddress ell v) =
        (neutralInsert C ell hellC hellPos).partialTypeAt
          (cut+1) (insertAddress ell w)) :
    A.partialTypeAt cut v = C.partialTypeAt cut w := by
  let B := neutralInsert A ell hellA hellPos
  let D := neutralInsert C ell hellC hellPos
  have hOldA := neutralInsert_partialType_old_atoms
    A ell hellA hellPos cut v hCutA hv
  have hOldC := neutralInsert_partialType_old_atoms
    C ell hellC hellPos cut w hCutC hw
  have hLA :
      (B.partialTypeAt (cut+1) (insertAddress ell v)).lReduct =
        (D.partialTypeAt (cut+1) (insertAddress ell w)).lReduct :=
    congrArg PartialTypeWithE.lReduct hAfter
  have hEA :
      (B.partialTypeAt (cut+1) (insertAddress ell v)).eRelation =
        (D.partialTypeAt (cut+1) (insertAddress ell w)).eRelation :=
    congrArg PartialTypeWithE.eRelation hAfter
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b t
      calc
        (A.partialTypeAt cut v).lReduct.binary a b t =
          (B.partialTypeAt (cut+1) (insertAddress ell v)).lReduct.binary
            (insertedTypeCoordinate ell a) (insertedTypeCoordinate ell b) t :=
              (hOldA.1 a b t).symm
        _ = (D.partialTypeAt (cut+1) (insertAddress ell w)).lReduct.binary
            (insertedTypeCoordinate ell a) (insertedTypeCoordinate ell b) t := by
              rw [hLA]
        _ = (C.partialTypeAt cut w).lReduct.binary a b t :=
              hOldC.1 a b t
    · intro a t
      calc
        (A.partialTypeAt cut v).lReduct.unary a t =
          (B.partialTypeAt (cut+1) (insertAddress ell v)).lReduct.unary
            (insertedTypeCoordinate ell a) t := (hOldA.2.1 a t).symm
        _ = (D.partialTypeAt (cut+1) (insertAddress ell w)).lReduct.unary
            (insertedTypeCoordinate ell a) t := by rw [hLA]
        _ = (C.partialTypeAt cut w).lReduct.unary a t :=
          hOldC.2.1 a t
    · intro a t
      calc
        (A.partialTypeAt cut v).lReduct.diagonal a t =
          (B.partialTypeAt (cut+1) (insertAddress ell v)).lReduct.diagonal
            (insertedTypeCoordinate ell a) t := (hOldA.2.2.1 a t).symm
        _ = (D.partialTypeAt (cut+1) (insertAddress ell w)).lReduct.diagonal
            (insertedTypeCoordinate ell a) t := by rw [hLA]
        _ = (C.partialTypeAt cut w).lReduct.diagonal a t :=
          hOldC.2.2.1 a t
  · intro a b
    calc
      (A.partialTypeAt cut v).eRelation a b =
        (B.partialTypeAt (cut+1) (insertAddress ell v)).eRelation
          (insertedTypeCoordinate ell a) (insertedTypeCoordinate ell b) :=
            (hOldA.2.2.2 a b).symm
      _ = (D.partialTypeAt (cut+1) (insertAddress ell w)).eRelation
          (insertedTypeCoordinate ell a) (insertedTypeCoordinate ell b) := by rw [hEA]
      _ = (C.partialTypeAt cut w).eRelation a b :=
        hOldC.2.2.2 a b

/-- The entire actual admissible neutral insertion is injective on the
normalized Kpt type forest, including the crossing of the gap. -/
theorem neutralKptSkip_injective
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell) :
    Function.Injective (neutralKptSkip family ell hellPos) := by
  intro a b hImage
  have hImageLev :
      (neutralKptSkip family ell hellPos a).1.1 =
        (neutralKptSkip family ell hellPos b).1.1 :=
    congrArg (fun x : AdmissibleKptNode family => x.1.1) hImage
  have hLev : a.1.1 = b.1.1 := by
    rw [neutralKptSkip_level, neutralKptSkip_level] at hImageLev
    by_cases ha : ell ≤ a.1.1
    · by_cases hb : ell ≤ b.1.1
      · simp [ha, hb] at hImageLev
        omega
      · simp [ha, hb] at hImageLev
        omega
    · by_cases hb : ell ≤ b.1.1
      · simp [ha, hb] at hImageLev
        omega
      · simp [ha, hb] at hImageLev
        omega
  by_cases haLow : a.1.1 < ell
  · have hbLow : b.1.1 < ell := by omega
    rw [neutralKptSkip_fixed_below family ell hellPos a haLow,
      neutralKptSkip_fixed_below family ell hellPos b hbLow] at hImage
    exact hImage
  · have ha : ell ≤ a.1.1 := by omega
    have hb : ell ≤ b.1.1 := by omega
    have hHighImage :
        neutralKptImage family ell hellPos a ha =
          neutralKptImage family ell hellPos b hb := by
      simpa only [neutralKptSkip_above family ell hellPos a ha,
        neutralKptSkip_above family ell hellPos b hb] using hImage
    obtain ⟨A, v, hellA, hv, hAvoidA, hRawA, hImgA⟩ :=
      neutralKptImage_isImage family ell hellPos a ha
    obtain ⟨C, w, hellC, hw, hAvoidC, hRawC, hImgC⟩ :=
      neutralKptImage_isImage family ell hellPos b hb
    have hSourceLevA : a.1.1 = A.freeLevel v :=
      congrArg Sigma.fst hRawA
    have hSourceLevC : b.1.1 = C.freeLevel w :=
      congrArg Sigma.fst hRawC
    let cut : Nat := a.1.1
    have hCutA : cut ≤ A.size := by
      have hbound := A.freeLevel_le v
      omega
    have hCutC : cut ≤ C.size := by
      have hbound := C.freeLevel_le w
      omega
    let B := neutralInsert A ell hellA hellPos
    let D := neutralInsert C ell hellC hellPos
    have hFreeA : B.freeLevel (insertAddress ell v) = cut+1 := by
      have h := neutralInsert_freeLevel_old A ell hellA hellPos v hv
      have hn : ¬ A.freeLevel v < ell := by omega
      have he : B.freeLevel (insertAddress ell v) =
          A.freeLevel v + 1 := by simpa only [B, if_neg hn] using h
      omega
    have hFreeC : D.freeLevel (insertAddress ell w) = cut+1 := by
      have h := neutralInsert_freeLevel_old C ell hellC hellPos w hw
      have hn : ¬ C.freeLevel w < ell := by omega
      have he : D.freeLevel (insertAddress ell w) =
          C.freeLevel w + 1 := by simpa only [D, if_neg hn] using h
      omega
    have hRawImage :
        B.rawTypeAtFree (insertAddress ell v) =
          D.rawTypeAtFree (insertAddress ell w) := by
      calc
        B.rawTypeAtFree (insertAddress ell v) =
          (neutralKptImage family ell hellPos a ha).1 := hImgA.symm
        _ = (neutralKptImage family ell hellPos b hb).1 :=
          congrArg Subtype.val hHighImage
        _ = D.rawTypeAtFree (insertAddress ell w) := hImgC
    have hAfter :
        B.partialTypeAt (cut+1) (insertAddress ell v) =
          D.partialTypeAt (cut+1) (insertAddress ell w) := by
      have h := (rawTypeAtFree_eq_data B D _ _ hRawImage).2
      rw [hFreeA] at h
      exact h
    have hBefore : A.partialTypeAt cut v = C.partialTypeAt cut w :=
      neutralInsert_partialType_reflects A C ell cut v w
        hellA hellC hellPos hCutA hCutC hv hw hAfter
    have hSources :
        A.rawTypeAtFree v = C.rawTypeAtFree w := by
      change
        (⟨A.freeLevel v, A.partialTypeAt (A.freeLevel v) v⟩ :
          RawPartialTypeNode db du dd) =
        (⟨C.freeLevel w, C.partialTypeAt (C.freeLevel w) w⟩ :
          RawPartialTypeNode db du dd)
      rw [← hSourceLevA, ← hSourceLevC, ← hLev]
      exact congrArg (Sigma.mk cut) hBefore
    exact Subtype.ext (hRawA.trans (hSources.trans hRawC.symm))

end SuccessorTree.V10

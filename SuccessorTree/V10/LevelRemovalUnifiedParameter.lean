import SuccessorTree.V10.LevelRemovalCanonicalParameter
import Mathlib.Tactic

/-!
# Unified transport of the genuine optional successor parameter under deletion

For an ordinary deletion coordinate m>0 lying before the last
ordinary vertex of a complete successor record Q, the canonical
parameter after deleting m is exactly the image of the old
empty-or-singleton parameter under the intrinsic coordinate
deletion map:
* a parameter with free cut f≤m is unchanged;
* a parameter with f>m is the complete L+ type with ordinary m removed.

The two cases were checked independently in
LevelRemovalCanonicalParameter. This theorem packages them without
adding any successor/age axiom. The restriction m>0 is genuine for
the M2 gap (and avoids converting a parameter of free cut 1 into
an empty parameter by deleting coordinate 0).
-/

namespace SuccessorTree.V10

/-- Delete coordinate m from a raw Kpt parameter precisely when that
coordinate occurs in its complete ordinary socle. For smaller
parameters, retain the entire L+ record unchanged. -/
def rawPartialTypeDeleteIfAbove
    {db du dd : Nat}
    (m : Nat) (P : RawPartialTypeNode db du dd) :
    RawPartialTypeNode db du dd :=
  if h : m < P.1 then rawPartialTypeDeleteAt P m h else P

@[simp] theorem rawPartialTypeDeleteIfAbove_low
    {db du dd : Nat} (m : Nat)
    (P : RawPartialTypeNode db du dd)
    (h : P.1 ≤ m) :
    rawPartialTypeDeleteIfAbove m P = P := by
  simp [rawPartialTypeDeleteIfAbove, Nat.not_lt.mpr h]

theorem rawPartialTypeDeleteIfAbove_high
    {db du dd : Nat} (m : Nat)
    (P : RawPartialTypeNode db du dd)
    (h : m < P.1) :
    rawPartialTypeDeleteIfAbove m P =
      rawPartialTypeDeleteAt P m h := by
  simp [rawPartialTypeDeleteIfAbove, h]

/-- One formula for the complete optional canonical parameter after
deleting an earlier ordinary coordinate. In particular the transport
retains the EMPTY parameter and the positive singleton convention. -/
theorem PartialTypeWithE.canonicalParameterRecord_delete_unified
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 2) db du dd)
    (m f : Nat) (hm : m < ell + 1)
    (hf : f ≤ ell + 1) (hmPos : 0 < m) :
    (Q.deleteOrdinary m (by omega)).canonicalParameterRecord
        (deleteAtCut m f) (by
          unfold deleteAtCut
          split_ifs <;> omega) =
      (Q.canonicalParameterRecord f hf).map
        (rawPartialTypeDeleteIfAbove m) := by
  classical
  by_cases hfLow : f ≤ m
  · have hCut : deleteAtCut m f = f := by
      simp [deleteAtCut, Nat.not_lt.mpr hfLow]
    have hFormula :=
      Q.canonicalParameterRecord_delete_outside m f hm hfLow
    have hMap :
        (Q.canonicalParameterRecord f hf).map
            (rawPartialTypeDeleteIfAbove m) =
          Q.canonicalParameterRecord f hf := by
      by_cases hfZero : f = 0
      · simp [PartialTypeWithE.canonicalParameterRecord, hfZero]
      · simp [PartialTypeWithE.canonicalParameterRecord,
          hfZero, rawPartialTypeDeleteIfAbove, Nat.not_lt.mpr hfLow]
    simpa only [hCut, hMap] using hFormula
  · have hmf : m < f := by omega
    have hCut : deleteAtCut m f = f - 1 := by
      simp [deleteAtCut, hmf]
    have hFormula :=
      Q.canonicalParameterRecord_delete_inside m f hm hf hmPos hmf
    have hfZero : f ≠ 0 := by omega
    have hMap :
        (Q.canonicalParameterRecord f hf).map
            (rawPartialTypeDeleteIfAbove m) =
          some (rawPartialTypeDeleteAt
            (⟨f,Q.lastOrdinaryParameter f hf⟩ :
              RawPartialTypeNode db du dd) m hmf) := by
      simp [PartialTypeWithE.canonicalParameterRecord, hfZero,
        rawPartialTypeDeleteIfAbove, hmf]
    simpa only [hCut, hMap] using hFormula

end SuccessorTree.V10

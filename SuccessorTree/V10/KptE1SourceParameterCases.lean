import SuccessorTree.V10.KptE1CanonicalParameterRecovery
import Mathlib.Tactic

/-!
# Source canonical parameter records in the two actual E1 cases

The genuine Kpt successor parameter record is empty at cut zero,
otherwise a singleton encoding the complete last-ordinary type at
its positive cut. Here the literal source parameter record is
computed in each case, with no representation interface and no
new axiom or assumed E-expansion.
-/

namespace SuccessorTree.V10

/-- An empty source parameter list is the exact canonical source
parameter at cut zero for any retained complete target type. -/
theorem kptE1_reindexed_empty_parameter_record
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n : Nat)
    (Q : PartialTypeWithE
      (kptShapeLevelMap family F n + 1) db du dd) :
    (([] : List (AdmissibleKptNode family)).map
      (fun x => x.1)) =
      ((Q.reindexOrdinary
        (kptShapeLastRetainedIndex family F n)).canonicalParameterRecord 0 (Nat.zero_le n)).toList := by
  simp [PartialTypeWithE.canonicalParameterRecord]

/-- A *real* singleton source parameter is exactly the canonical
source parameter after retaining the target successor's coordinates.
The hypothesis identifies the genuine image node as the target's
canonical parameter at its actual shape-level image cut. -/
theorem kptE1_reindexed_singleton_parameter_record
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n : Nat) (x : AdmissibleKptNode family)
    (hx : x.1.1 ≤ n) (hPos : 0 < x.1.1)
    (Q : PartialTypeWithE
      (kptShapeLevelMap family F n + 1) db du dd)
    (hImageParameter :
      (F x).1 =
        (⟨kptShapeLevelMap family F x.1.1,
          Q.lastOrdinaryParameter
            (kptShapeLevelMap family F x.1.1)
            ((kptShapeLevelMap_strictMono family F).monotone hx)⟩ :
          RawPartialTypeNode db du dd)) :
    ([x] : List (AdmissibleKptNode family)).map
        (fun y => y.1) =
      ((Q.reindexOrdinary
        (kptShapeLastRetainedIndex family F n)).canonicalParameterRecord x.1.1 hx).toList := by
  have hRecovered :=
    kptShapeReindex_parameter_recovers_source
      family F n x hx Q hImageParameter
  have hNonzero : x.1.1 ≠ 0 := Nat.ne_of_gt hPos
  simp [PartialTypeWithE.canonicalParameterRecord, hNonzero,
    hRecovered]

/-- The image of an actual canonical Kpt parameter list contains at
most one element, and therefore so does the source list.
This is a finite-shape consequence of the *actual* canonical target
record and not an additional restriction on arbitrary source lists. -/
theorem kptE1_source_parameter_length_le_one
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    {ell : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (g : Nat) (hg : g ≤ ell)
    (p : List (AdmissibleKptNode family))
    (hTargetParameter :
      ((p.map F).map (fun x => x.1)) =
        (Q.canonicalParameterRecord g hg).toList) :
    p.length ≤ 1 := by
  have hLength : p.length =
      (Q.canonicalParameterRecord g hg).toList.length := by
    simpa only [List.length_map] using
      congrArg List.length hTargetParameter
  by_cases hz : g = 0
  · have hEmpty : p.length = 0 := by
      simpa [PartialTypeWithE.canonicalParameterRecord, hz] using hLength
    omega
  · have hOne : p.length = 1 := by
      simpa [PartialTypeWithE.canonicalParameterRecord, hz] using hLength
    omega

end SuccessorTree.V10

import SuccessorTree.V10.LevelRemovalParameter
import SuccessorTree.V10.LevelRemovalRawPrefix
import SuccessorTree.V10.EmptyParameterS2
import Mathlib.Tactic

/-!
# The actual empty-or-singleton canonical parameter survives deletion

The finite complete parameter identities in LevelRemovalParameter
transport the FULL last-ordinary parameter record. The successor graph
uses an Option of a raw Kpt node: none exactly at free cut zero, and a
singleton at every positive free cut.

For deletion of m from an old successor record at level ell+2:
* if f≤m, the canonical Option parameter is unchanged;
* if 0<m<f, it is precisely the old singleton raw type with m deleted.
The positive m assumption excludes the artificial case where
deleting coordinate zero turns a singleton at cut one into no
parameter. This is satisfied at a genuine M2 target gap.

No global M2 map, weak successor clause or age necessity is assumed.
-/

namespace SuccessorTree.V10

/-- If the new ordinary vertex's free cut lies at or below the deleted
coordinate, its genuine canonical Option parameter is unchanged. -/
theorem PartialTypeWithE.canonicalParameterRecord_delete_outside
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 2) db du dd)
    (m f : Nat) (hm : m < ell + 1) (hf : f ≤ m) :
    (Q.deleteOrdinary m (by omega)).canonicalParameterRecord
        f (by omega) =
      Q.canonicalParameterRecord f (by omega) := by
  by_cases hz : f = 0
  · subst f
    simp [PartialTypeWithE.canonicalParameterRecord]
  · have hParam :
        ((Q.deleteOrdinary m (by omega)).lastOrdinaryParameter
            f (by omega)) =
          Q.lastOrdinaryParameter f (by omega) :=
      Q.deleteOrdinary_lastOrdinary_outside m f hm hf
    simp only [PartialTypeWithE.canonicalParameterRecord, if_neg hz]
    change
      some (⟨f, (Q.deleteOrdinary m (by omega)).lastOrdinaryParameter
        f (by omega)⟩ : RawPartialTypeNode db du dd) =
      some (⟨f, Q.lastOrdinaryParameter f (by omega)⟩ :
        RawPartialTypeNode db du dd)
    exact congrArg
      (fun T : PartialTypeWithE f db du dd =>
        some (⟨f,T⟩ : RawPartialTypeNode db du dd)) hParam

/-- If the deleted coordinate belongs to the free E-socle and
m>0, the genuinely nonempty canonical parameter is exactly the
coordinate-deleted former singleton raw Kpt parameter. -/
theorem PartialTypeWithE.canonicalParameterRecord_delete_inside
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 2) db du dd)
    (m f : Nat) (hm : m < ell + 1)
    (hf : f ≤ ell + 1)
    (hPos : 0 < m) (hmf : m < f) :
    (Q.deleteOrdinary m (by omega)).canonicalParameterRecord
        (f - 1) (by omega) =
      some (rawPartialTypeDeleteAt
        (⟨f,Q.lastOrdinaryParameter f hf⟩ :
          RawPartialTypeNode db du dd) m hmf) := by
  have hNewPos : f - 1 ≠ 0 := by omega
  have hParam :
      ((Q.deleteOrdinary m (by omega)).lastOrdinaryParameter
        (f - 1) (by omega)) =
        (Q.lastOrdinaryParameter f hf).deleteOrdinary m hmf :=
    Q.deleteOrdinary_lastOrdinary_inside m f hm hf hmf
  simp only [PartialTypeWithE.canonicalParameterRecord, if_neg hNewPos]
  change
    some (⟨f - 1,
      (Q.deleteOrdinary m (by omega)).lastOrdinaryParameter
        (f - 1) (by omega)⟩ : RawPartialTypeNode db du dd) =
    some (⟨f - 1,
      (Q.lastOrdinaryParameter f hf).deleteOrdinary m hmf⟩ :
        RawPartialTypeNode db du dd)
  exact congrArg
    (fun T : PartialTypeWithE (f - 1) db du dd =>
      some (⟨f - 1,T⟩ : RawPartialTypeNode db du dd)) hParam

end SuccessorTree.V10

import SuccessorTree.V10.LevelRemovalType
import SuccessorTree.V10.AdmissibleKptPrefix
import Mathlib.Tactic

/-!
# A guarded deleted L+ type is again an admissible Kpt type

LevelRemovalType already checks exact equality of complete L+ records
after deleting an ordinary coordinate m. We now transport the
distinguished vertex itself: a vertex v with m<freeLevel(v) occurs
at v-1 in the shortened enumeration. Its canonical free level
decreases by exactly one, and its entire extracted type is the
coordinate-deleted old type.

Since induced coordinate deletion preserves every forbidden-free
finite L age, this gives a genuine admissible Kpt witness, not only
an equality of unvalidated raw records.

This remains the LOCAL age/membership part of Lemma 6.34. The
uniform global ShapeMap removal, M2 decomposition, and corrected
finite L-only B3 necessity are NOT asserted.
-/

namespace SuccessorTree.V10

/-- Address of an old vertex strictly after the deleted coordinate,
expressed in the new shortened enumeration. -/
theorem deleteAt_pred_of_gt (m v : Nat) (h : m < v) :
    deleteAt m (v - 1) = v := by
  have hm : m ≤ v - 1 := by omega
  rw [deleteAt_above m (v - 1) hm]
  omega

/-- After a guarded deletion, the exact full raw Kpt type
of the retained distinguished vertex is the old one with
ordinary coordinate m removed. No E relation is forgotten. -/
theorem deleteAtPartial_rawTypeAtFree_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (m : Nat)
    (hnext : m + 1 < A.size)
    (hguard : A.freeLevel (m + 1) < m)
    (v : Nat) (hm : m < A.freeLevel v) :
    let B := deleteAtPartial A m hnext hguard
    B.rawTypeAtFree (v - 1) =
      (⟨A.freeLevel v - 1,
        (A.partialTypeAt (A.freeLevel v) v).deleteOrdinary m hm⟩ :
        RawPartialTypeNode db du dd) := by
  let B := deleteAtPartial A m hnext hguard
  have hmv : m < v := lt_of_lt_of_le hm (A.freeLevel_le v)
  have hAddress : deleteAt m (v - 1) = v :=
    deleteAt_pred_of_gt m v hmv
  have hFreeB : B.freeLevel (v - 1) = A.freeLevel v - 1 := by
    have hh := deleteAtPartial_freeLevel_eq A m hnext hguard (v - 1)
    rw [hAddress] at hh
    have hCut : deleteAtCut m (A.freeLevel v) =
        A.freeLevel v - 1 := by
      simp [deleteAtCut, hm]
    exact hh.trans hCut
  have hType :
      B.partialTypeAt (A.freeLevel v - 1) (v - 1) =
        (A.partialTypeAt (A.freeLevel v) v).deleteOrdinary m hm := by
    have hh := deleteAtPartial_partialTypeAt_eq_deleteOrdinary
      A m (A.freeLevel v) (v - 1) hnext hguard hm
    rw [hAddress] at hh
    exact hh
  change (⟨B.freeLevel (v - 1),
    B.partialTypeAt (B.freeLevel (v - 1)) (v - 1)⟩ :
      RawPartialTypeNode db du dd) = _
  rw [hFreeB]
  exact congrArg (Sigma.mk (A.freeLevel v - 1)) hType

/-- The deleted type has an ACTUAL forbidden-free partial-structure
representative with the transported canonical free level. This is the
local Kpt membership clause needed by a future uniform deletion map. -/
theorem admissible_deleted_complete_type
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (m : Nat)
    (hnext : m + 1 < A.size)
    (hguard : A.freeLevel (m + 1) < m)
    (v : Nat) (hv : v < A.size)
    (hm : m < A.freeLevel v)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    IsAdmissibleRawType family
      (⟨A.freeLevel v - 1,
        (A.partialTypeAt (A.freeLevel v) v).deleteOrdinary m hm⟩ :
        RawPartialTypeNode db du dd) := by
  let B := deleteAtPartial A m hnext hguard
  have hmv : m < v := lt_of_lt_of_le hm (A.freeLevel_le v)
  have hvB : v - 1 < B.size := by
    change v - 1 < A.size - 1
    omega
  have hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L :=
    deleteAtPartial_preserves_avoidance family A m hnext hguard hAvoid
  have hRaw : B.rawTypeAtFree (v - 1) =
      (⟨A.freeLevel v - 1,
        (A.partialTypeAt (A.freeLevel v) v).deleteOrdinary m hm⟩ :
        RawPartialTypeNode db du dd) :=
    deleteAtPartial_rawTypeAtFree_eq A m hnext hguard v hm
  exact ⟨B,v - 1,hvB,hAvoidB,hRaw.symm⟩

end SuccessorTree.V10

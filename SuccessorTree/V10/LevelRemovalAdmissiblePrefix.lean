import SuccessorTree.V10.LevelRemovalAdmissibleType
import SuccessorTree.V10.LevelRemovalType
import SuccessorTree.V10.AdmissibleKptPrefix
import Mathlib.Tactic

/-!
# Guarded deletion preserves the admissibility of a shortened Kpt prefix

A genuine finite witness of the image successor has a canonical
free level one higher than the boundary type we want to shorten.
It is therefore incorrect to claim that the distinguished vertex's
new canonical free level is already the shortened boundary cut.

Instead, delete coordinate m in the genuine finite partial structure,
then take the COMPLETE extracted type at the shortened cut.
The previously proved prefix-closure theorem supplies an admissible
representation at that cut (one neutral filler when necessary).

This result uses the original strict deletion guard; its derivation
from a target level gap belongs to the separate M2 gap-column proof.
No global deletion ShapeMap, M2 factorization or B3 age premise is
assumed here.
-/

namespace SuccessorTree.V10

/-- For any initial cut c below the distinguished vertex's
actual free level, deleting ordinary coordinate m<c under the
strict spacing guard produces another ADMISSIBLE Kpt type.
All positive/absent L atoms and E bits are literally transported.

The relevant represented vertex after deletion is v-1, but its
canonical new free level may exceed c-1. The proof explicitly
passes to the admissible prefix at c-1; it does not silently
identify those two cuts. -/
theorem admissible_deleted_type_at_shorter_cut
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (m cut v : Nat)
    (hnext : m + 1 < A.size)
    (hguard : A.freeLevel (m + 1) < m)
    (hv : v < A.size)
    (hCut : cut ≤ A.freeLevel v)
    (hm : m < cut)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    IsAdmissibleRawType family
      (⟨cut - 1,
        (A.partialTypeAt cut v).deleteOrdinary m hm⟩ :
        RawPartialTypeNode db du dd) := by
  let B := deleteAtPartial A m hnext hguard
  have hmv : m < v := by
    have hvFree := A.freeLevel_le v
    omega
  have hAddress : deleteAt m (v - 1) = v :=
    deleteAt_pred_of_gt m v hmv
  have hvB : v - 1 < B.size := by
    change v - 1 < A.size - 1
    omega
  have hFree : B.freeLevel (v - 1) = A.freeLevel v - 1 := by
    calc
      B.freeLevel (v - 1) =
          deleteAtCut m (A.freeLevel (deleteAt m (v - 1))) :=
        deleteAtPartial_freeLevel_eq A m hnext hguard (v - 1)
      _ = deleteAtCut m (A.freeLevel v) := by rw [hAddress]
      _ = A.freeLevel v - 1 := by
        simp [deleteAtCut, lt_of_lt_of_le hm hCut]
  have hNewCut : cut - 1 ≤ B.freeLevel (v - 1) := by
    omega
  have hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L :=
    deleteAtPartial_preserves_avoidance family A m hnext hguard hAvoid
  have hAdFull : IsAdmissibleRawType family (B.rawTypeAtFree (v - 1)) :=
    ⟨B,v - 1,hvB,hAvoidB,rfl⟩
  have hAdPrefix :=
    admissibleRawType_closed_under_prefix family hAdFull
      (cut - 1) hNewCut
  have hRestr :
      (B.partialTypeAt (B.freeLevel (v - 1)) (v - 1)).restrict hNewCut =
        B.partialTypeAt (cut - 1) (v - 1) :=
    B.partialTypeAt_restrict (cut - 1) (B.freeLevel (v - 1))
      (v - 1) hNewCut
  have hDeleted :
      B.partialTypeAt (cut - 1) (v - 1) =
        (A.partialTypeAt cut v).deleteOrdinary m hm := by
    have hh := deleteAtPartial_partialTypeAt_eq_deleteOrdinary
      A m cut (v - 1) hnext hguard hm
    rw [hAddress] at hh
    exact hh
  change IsAdmissibleRawType family
    (⟨cut - 1,
      (B.partialTypeAt (B.freeLevel (v - 1)) (v - 1)).restrict hNewCut⟩ :
      RawPartialTypeNode db du dd) at hAdPrefix
  rw [hRestr,hDeleted] at hAdPrefix
  exact hAdPrefix

end SuccessorTree.V10

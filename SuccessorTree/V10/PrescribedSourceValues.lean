import SuccessorTree.V10.PrescribedKptFullPrefix
import SuccessorTree.V10.PrescribedUpperSelection
import Mathlib.Tactic

/-!
# Prescribed values: the actual finite L-type at a source node

The full prescribed map must agree with f on its level-ell domain.
We first isolate a literal constructor statement for the complete
L-reduct; it is a consequence of B1/B2 and the actual upper
selection, not a restatement of prescribed output equality.

Equality of E atoms is a separate obligation. In particular, this
module must not be cited as proof of agreement in the full L+ tree.
-/

namespace SuccessorTree.V10

/-- At any level-ell source vertex of F, the finite prescribed
insertion realizes *all* atoms of the target's L-reduct at the
shifted vertex. No equality of E records is assumed or concluded. -/
theorem PrescribedBoringData.prescribedInsertPartial_source_L
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (hv : v < A.size)
    (hFree : A.freeLevel v = ell)
    (hSrc : A.partialTypeAt ell v ∈ F.source)
    (k : Nat)
    (hValid : ValidNewOrdinaryColumn
       (F.target (A.partialTypeAt ell v)) k)
    (hell : ell ≤ A.size) (hPos : 0 < ell)
    (hk : k ≤ ell) (hGate : k = 0 ∨ k < ell) :
    ((prescribedInsertPartial A
      (F.target (A.partialTypeAt ell v)) k hValid
      hell hPos hk hGate
      (F.upperIncoming A) (F.upperOutgoing A)).partialTypeAt
        (ell+1) (insertAddress ell v)).lReduct =
      (F.target (A.partialTypeAt ell v)).lReduct := by
  have hV : ell ≤ v := by
    have hh := A.freeLevel_le v
    omega
  have hReach : ell ≤ A.freeLevel v := by omega
  have hSelected :
      F.selectedLowerColumn (A.partialTypeAt ell v) =
        some (lowerInsertedColumn (F.target (A.partialTypeAt ell v))) :=
    F.selectedLowerColumn_eq (A.partialTypeAt ell v)
      (A.partialTypeAt ell v) hSrc
      (sameOrdinaryAtCut_refl (A.partialTypeAt ell v))
  have hL := F.upper_realizes_target_L A v v
    (lowerInsertedColumn (F.target (A.partialTypeAt ell v)))
    hV hReach hSelected hSrc
  exact hL

end SuccessorTree.V10

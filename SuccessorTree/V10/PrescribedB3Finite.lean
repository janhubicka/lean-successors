import SuccessorTree.V10.PrescribedCommonSocle
import SuccessorTree.V10.PrescribedInsertPartial
import Mathlib.Tactic

/-!
# The matching-socle prescribed finite insertion preserves forbidden age

We now assemble the three formerly separate conditions of the finite
B3 no-age-change argument in Lemma 6.51.

Choose one prescribed source S0 compatible with the original ordinary
socle of A, and let Q=f(S0). Insert its entire new ordinary lower column
using the genuine finite L+ constructor. For each old upper vertex u,
the two incident directed L columns are selected from f(type_A^ell(u))
when defined, and zero otherwise, with the original free-level E gate.

The finite structural constructor automatically satisfies all E axioms,
and copies all old L atoms. B1/B2 imply the resulting initial L-socle
equals that of a forbidden-free ambient witness W of Q. Every upper
vertex linked to the inserted coordinate realizes an f[S] complete
L-type (proved from actual atomic columns, not assumed). The existing
finite three-clause B3 no-age-change test then excludes every forbidden
induced configuration in the newly inserted structure.

The theorem below is fully local and keeps W, its Q-identification and
the age-test hypothesis explicit. Next: derive W and the valid cut
directly from admissibility of Q, then prove representation independence
and the global Kpt map. No global M2/M3 is claimed.
-/

namespace SuccessorTree.V10

/-- Under the manuscript's genuine three-clause finite no-age-change
hypothesis, the prescribed insertion with all upper L-columns SELECTED
from the actual partial f is forbidden-free. Neither the common socle
nor the upper-type condition is an independent input: they follow from
B1, B2, source admissibility and literal old-atom transport. -/
theorem PrescribedBoringData.prescribedInsertion_avoids_of_witness
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : PrescribedBoringData ell db du dd)
    (A W : EnumeratedPartialStructure db du dd)
    (base w : Nat)
    (S0 : PartialTypeWithE ell db du dd)
    (hS0 : S0 ∈ F.source)
    (hComp : SameOrdinaryAtCut S0 (A.partialTypeAt ell base))
    (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hAvoidW : ∀ bad, bad ∈ family → bad.Avoids W.L)
    (hWSize : ell < W.size)
    (hWitness : F.target S0 = W.partialTypeAt (ell+1) w)
    (d : Nat)
    (hValid : ValidNewOrdinaryColumn (F.target S0) d)
    (hd : d ≤ ell) (hdGate : d = 0 ∨ d < ell)
    (hAgeTest : CommonSocleAgeTest family W.L ell
      F.PrescribedUpperLType) :
    ∀ bad, bad ∈ family →
      bad.Avoids
        (prescribedInsertPartial A (F.target S0) d hValid
          hell hellPos hd hdGate (F.upperIncoming A)
          (F.upperOutgoing A)).L := by
  have hSelected :
      F.selectedLowerColumn (A.partialTypeAt ell base) =
        some (lowerInsertedColumn (F.target S0)) :=
    F.selectedLowerColumn_eq (A.partialTypeAt ell base)
      S0 hS0 hComp
  have hSocle : SameInitialL
      (prescribedInsertPartial A (F.target S0) d hValid
        hell hellPos hd hdGate (F.upperIncoming A)
        (F.upperOutgoing A)).L W.L ell := by
    change SameInitialL
      (insertL A ell (F.insertedLData A
        (lowerInsertedColumn (F.target S0)))) W.L ell
    exact F.insertedData_common_initial_L A W
      S0 hS0 base w hComp hell hWSize hWitness
  have hUpper : ∀ x,
      x < (prescribedInsertPartial A (F.target S0) d hValid
          hell hellPos hd hdGate (F.upperIncoming A)
          (F.upperOutgoing A)).size →
      ell < x →
      (∃ t : Fin db,
        (prescribedInsertPartial A (F.target S0) d hValid
          hell hellPos hd hdGate (F.upperIncoming A)
          (F.upperOutgoing A)).L.binary ell x t = true ∨
        (prescribedInsertPartial A (F.target S0) d hValid
          hell hellPos hd hdGate (F.upperIncoming A)
          (F.upperOutgoing A)).L.binary x ell t = true) →
      F.PrescribedUpperLType
        (RelationalPrefixType.ofAgeModel
          (prescribedInsertPartial A (F.target S0) d hValid
            hell hellPos hd hdGate (F.upperIncoming A)
            (F.upperOutgoing A)).L (ell+1) x) := by
    intro x hx hxAbove hLink
    change x < A.size + 1 at hx
    change ∃ t : Fin db,
      (insertL A ell (F.insertedLData A
        (lowerInsertedColumn (F.target S0)))).binary ell x t = true ∨
      (insertL A ell (F.insertedLData A
        (lowerInsertedColumn (F.target S0)))).binary x ell t = true
      at hLink
    change F.PrescribedUpperLType
      (RelationalPrefixType.ofAgeModel
        (insertL A ell (F.insertedLData A
          (lowerInsertedColumn (F.target S0)))) (ell+1) x)
    exact F.insertL_linked_upper_is_prescribed A base
      (lowerInsertedColumn (F.target S0)) hSelected
      x hx hxAbove hLink
  exact prescribedInsertPartial_avoids_of_ageTest
    family A (F.target S0) d hValid hell hellPos hd hdGate
    (F.upperIncoming A) (F.upperOutgoing A)
    hAvoidA W.L F.PrescribedUpperLType
    hSocle hAvoidW hUpper hAgeTest

end SuccessorTree.V10

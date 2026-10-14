import SuccessorTree.V10.PrescribedSocleColumn
import SuccessorTree.V10.LocalAgeFreeCut
import Mathlib.Tactic

/-!
# A genuine finite prescribed one-level insertion

Starting from an actual one-level prescribed crossing Q at level ell+1,
its last ordinary vertex provides a lower L-column and a UNIQUE E free
cut d. Arbitrary upper directed tuples are gated by the ORIGINAL free
levels to enforce the E3 linked-pair axiom. The lower E3 obligation follows
from the checked no-new-tuples property of Q, rather than an assumed
inserted partial structure.

This constructs a genuine finite L+ partial structure B, with all old
L atoms preserved and exact E cut transport. If the source and inserted
common socle agree with a forbidden-free age-test datum, and every linked
upper vertex realizes one of the prescribed types, the existing finite
three-clause age-test theorem makes B forbidden-free.

The latter two hypotheses are the remaining uniform-selection/compatibility
obligations of Lemma 6.51 and are deliberately visible. This module does
not claim the prescribed global shape map.
-/

namespace SuccessorTree.V10

/-- The actual finite L+ insertion obtained from a prescribed lower
ordinary column. Both E3 gates are now DERIVED by the previous module. -/
noncomputable def prescribedInsertPartial
    {db du dd ell : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (d : Nat)
    (hValid : ValidNewOrdinaryColumn Q d)
    (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (hd : d ≤ ell) (hdGate : d = 0 ∨ d < ell)
    (upperIncoming upperOutgoing : Nat → Fin db → Bool) :
    EnumeratedPartialStructure db du dd :=
  insertPartial A ell d
    (gatedInsertedLData A (lowerInsertedColumn Q)
      upperIncoming upperOutgoing)
    hell hellPos hd hdGate
    (gatedInsertedLData_below A Q d hValid upperIncoming upperOutgoing)
    (gatedInsertedLData_above A (lowerInsertedColumn Q)
      upperIncoming upperOutgoing)

/-- This prescription copies every old ordered induced L tuple exactly;
neither the choice of lower crossing nor the gated upper data modifies
positive or absent source L facts. -/
theorem prescribedInsertPartial_isLInsertion
    {db du dd ell : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (d : Nat) (hValid : ValidNewOrdinaryColumn Q d)
    (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (hd : d ≤ ell) (hdGate : d = 0 ∨ d < ell)
    (upperIncoming upperOutgoing : Nat → Fin db → Bool) :
    IsLInsertion A
      (prescribedInsertPartial A Q d hValid hell hellPos hd hdGate
        upperIncoming upperOutgoing) ell := by
  exact insertPartial_isLInsertion A ell d
    (gatedInsertedLData A (lowerInsertedColumn Q)
      upperIncoming upperOutgoing)
    hell hellPos hd hdGate
    (gatedInsertedLData_below A Q d hValid upperIncoming upperOutgoing)
    (gatedInsertedLData_above A (lowerInsertedColumn Q)
      upperIncoming upperOutgoing)

/-- The inserted ordinary vertex has exactly the prescribed FIRST MISSING
E coordinate. This is a real canonical free level, not merely a d chosen
as metadata. -/
theorem prescribedInsertPartial_new_freeLevel
    {db du dd ell : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (d : Nat) (hValid : ValidNewOrdinaryColumn Q d)
    (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (hd : d ≤ ell) (hdGate : d = 0 ∨ d < ell)
    (upperIncoming upperOutgoing : Nat → Fin db → Bool) :
    (prescribedInsertPartial A Q d hValid hell hellPos hd hdGate
      upperIncoming upperOutgoing).freeLevel ell = d := by
  exact insertPartial_freeLevel_at_inserted A ell d
    (gatedInsertedLData A (lowerInsertedColumn Q)
      upperIncoming upperOutgoing)
    hell hellPos hd hdGate
    (gatedInsertedLData_below A Q d hValid upperIncoming upperOutgoing)
    (gatedInsertedLData_above A (lowerInsertedColumn Q)
      upperIncoming upperOutgoing)

/-- All old vertices still have their canonical E-cuts shifted at precisely
the gap ell, including those with original free cut zero. -/
theorem prescribedInsertPartial_old_freeLevel
    {db du dd ell : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (d : Nat) (hValid : ValidNewOrdinaryColumn Q d)
    (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (hd : d ≤ ell) (hdGate : d = 0 ∨ d < ell)
    (upperIncoming upperOutgoing : Nat → Fin db → Bool)
    (v : Nat) (hv : v < A.size) :
    (prescribedInsertPartial A Q d hValid hell hellPos hd hdGate
      upperIncoming upperOutgoing).freeLevel (insertAddress ell v) =
      if A.freeLevel v < ell then A.freeLevel v
      else A.freeLevel v + 1 := by
  exact insertPartial_freeLevel_old A ell d
    (gatedInsertedLData A (lowerInsertedColumn Q)
      upperIncoming upperOutgoing)
    hell hellPos hd hdGate
    (gatedInsertedLData_below A Q d hValid upperIncoming upperOutgoing)
    (gatedInsertedLData_above A (lowerInsertedColumn Q)
      upperIncoming upperOutgoing)
    v hv

/-- A real prescribed finite insertion is F-free under EXACTLY the
remaining common-socle/prescribed-upper-type conditions of the finite
B3 age test. There is no additional E assumption on age-test witnesses. -/
theorem prescribedInsertPartial_avoids_of_ageTest
    {db du dd ell : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (d : Nat) (hValid : ValidNewOrdinaryColumn Q d)
    (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (hd : d ≤ ell) (hdGate : d = 0 ∨ d < ell)
    (upperIncoming upperOutgoing : Nat → Fin db → Bool)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (D : AgeTestModel db du dd)
    (Prescribed : RelationalPrefixType (ell + 1) db du dd → Prop)
    (hSocle : SameInitialL
      (prescribedInsertPartial A Q d hValid hell hellPos hd hdGate
        upperIncoming upperOutgoing).L D ell)
    (hAvoidD : ∀ bad, bad ∈ family → bad.Avoids D)
    (hUpper : ∀ x,
      x < (prescribedInsertPartial A Q d hValid hell hellPos hd hdGate
        upperIncoming upperOutgoing).size →
      ell < x →
      (∃ t : Fin db,
        (prescribedInsertPartial A Q d hValid hell hellPos hd hdGate
          upperIncoming upperOutgoing).L.binary ell x t = true ∨
        (prescribedInsertPartial A Q d hValid hell hellPos hd hdGate
          upperIncoming upperOutgoing).L.binary x ell t = true) →
      Prescribed (RelationalPrefixType.ofAgeModel
        (prescribedInsertPartial A Q d hValid hell hellPos hd hdGate
          upperIncoming upperOutgoing).L (ell + 1) x))
    (hAgeTest : CommonSocleAgeTest family D ell Prescribed) :
    ∀ bad, bad ∈ family →
      bad.Avoids (prescribedInsertPartial A Q d hValid hell hellPos hd hdGate
        upperIncoming upperOutgoing).L := by
  exact localAgeTest_preserves_avoidance_of_common_socle
    family D ell Prescribed
    (prescribedInsertPartial_isLInsertion A Q d hValid hell
      hellPos hd hdGate upperIncoming upperOutgoing)
    hAvoid hSocle hAvoidD hUpper hAgeTest

end SuccessorTree.V10

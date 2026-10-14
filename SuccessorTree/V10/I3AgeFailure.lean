import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# The finite L-age witness furnished by a failed I3 local-age test

The manuscript's condition (I3) is triggered when the finite
common-socle age test fails. Unfolding that failure must give a
genuine *finite L-only* witness, an exact initial socle, prescribed
upper types, an admissible deletion and a forbidden configuration.
This interface makes those consequences explicit; it does not
postulate an auxiliary E-expansion or choose an unrelated partial
structure.

The individual forbidden-copy membership in the tested coordinate
then follows simply from avoidance after deleting that coordinate.
The original labels for upper witnesses are established separately
from the actual prescribed crossing.
-/

namespace SuccessorTree.V10

/-- Failure of a corrected finite common-socle age test supplies the
exact finite L-only witness required by the I3 signature argument.
In particular the failure is not an arbitrary infinite age witness. -/
theorem failedCommonSocleAgeTest_has_finite_L_witness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (D : AgeTestModel db du dd)
    (ell : Nat)
    (Prescribed : RelationalPrefixType (ell + 1) db du dd → Prop)
    (hFailure : ¬ CommonSocleAgeTest family D ell Prescribed) :
    ∃ W : AgeTestModel db du dd,
      W.BoundedCarrier ∧
      SameInitialL W D ell ∧
      UpperTypesPrescribed W ell Prescribed ∧
      (∀ bad, bad ∈ family → bad.Avoids (W.withoutVertex ell)) ∧
      ∃ bad, bad ∈ family ∧ ¬ bad.Avoids W := by
  classical
  unfold CommonSocleAgeTest at hFailure
  push_neg at hFailure
  exact hFailure

/-- An induced forbidden copy in a finite tested L-age witness
must contain the coordinate whose deletion is forbidden-free.
The conclusion works equally for singleton and nontrivial patterns;
no positive-only copying assumption is used. -/
theorem forbiddenCopy_meets_tested_coordinate
    {r db du dd : Nat}
    (W : AgeTestModel db du dd) (ell : Nat)
    (P : ForbiddenAtomicPattern r db du dd)
    (e : Fin r → Nat)
    (hCopy : W.Realizes P e)
    (hDeletedAvoid : ¬ ∃ f : Fin r → Nat,
      (W.withoutVertex ell).Realizes P f) :
    ∃ a : Fin r, e a = ell := by
  by_contra hNone
  have hAway : ∀ a : Fin r, e a ≠ ell := by
    intro a ha
    exact hNone ⟨a,ha⟩
  have hRestricted : (W.withoutVertex ell).Realizes P e :=
    AgeTestModel.realizes_restrictCarrier
      W (fun x => x ≠ ell) P e hCopy hAway
  exact hDeletedAvoid ⟨e,hRestricted⟩

end SuccessorTree.V10

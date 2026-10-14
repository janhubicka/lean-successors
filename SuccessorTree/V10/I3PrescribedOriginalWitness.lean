import SuccessorTree.V10.I3AgeFailure
import SuccessorTree.V10.ChosenAgeSignatures
import SuccessorTree.V10.PrescribedCompatibleB3
import Mathlib.Tactic

/-!
# The actual original labels in a failed prescribed finite-age test

The manuscript's I3 construction starts with a partial function f on
genuine Kpt source types obtained from a fixed ambient finite model
C and a finite pool of named original vertices. A failed corrected
B3 test gives a finite L-only witness W. It remains essential to show
that every upper type in that witness is one of the prescribed images
f(T), hence agrees with the L-type of a named original of C.

This module derives that implication directly from the definition of
CompatibleUpperLType and extracts the finite witness from the failure
of CompatibleB3. Its sole representation hypothesis is about the
prescribed SOURCE FUNCTION f itself, before any age-test witness is
chosen. It does not assign E to the arbitrary L-age witness.

The pending manuscript bridge is to identify the actual I3
source/crossing function and original pool with the representation
hypothesis below. No weakening of the original axioms is introduced.
-/

namespace SuccessorTree.V10

/-- If every actual prescribed output comes from an ambient original,
then every upper type allowed by its compatible B3 test also comes
from an ambient original. Both true and false L atoms are retained. -/
theorem PrescribedBoringData.compatibleUpper_has_ambient_original
    {ell db du dd M : Nat}
    (F : PrescribedBoringData ell db du dd)
    (C W : AgeTestModel db du dd)
    (original : Fin M → Nat)
    (S0 : PartialTypeWithE ell db du dd)
    (hRepresented : ∀ T, T ∈ F.source →
      ∃ v : Fin M,
        (F.target T).lReduct =
          RelationalPrefixType.ofAgeModel C (ell + 1) (original v))
    (hUpper : UpperTypesPrescribed W ell
      (F.CompatibleUpperLType S0))
    (x : Nat) (hx : x ∈ W.carrier) (hAbove : ell < x) :
    ∃ v : Fin M,
      RelationalPrefixType.ofAgeModel W (ell + 1) x =
        RelationalPrefixType.ofAgeModel C (ell + 1) (original v) := by
  obtain ⟨T,hT,_hComp,hType⟩ := hUpper x hx hAbove
  obtain ⟨v,hAmbient⟩ := hRepresented T hT
  exact ⟨v,hType.trans hAmbient⟩

/-- Failure of B3 for an actual prescribed source function yields
one FINITE L-only witness with the exact initial socle and complete
ambient-original labels for all upper vertices. The only assumption
not built into f is its explicit source-to-original representation.

The resulting witness contains a forbidden configuration even though
deleting the tested coordinate makes it forbidden-free. -/
theorem PrescribedBoringData.failedCompatibleB3_has_ambient_original_witness
    {ell db du dd M : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (C : AgeTestModel db du dd)
    (original : Fin M → Nat)
    (hRepresented : ∀ T, T ∈ F.source →
      ∃ v : Fin M,
        (F.target T).lReduct =
          RelationalPrefixType.ofAgeModel C (ell + 1) (original v))
    (hFailure : ¬ F.CompatibleB3 family) :
    ∃ S0 : PartialTypeWithE ell db du dd,
      S0 ∈ F.source ∧
      ∃ W : AgeTestModel db du dd,
        W.BoundedCarrier ∧
        SameInitialL W (prescribedOrdinarySocle (F.target S0)) ell ∧
        (∀ bad, bad ∈ family → bad.Avoids (W.withoutVertex ell)) ∧
        (∀ x, x ∈ W.carrier → ell < x →
          ∃ v : Fin M,
            RelationalPrefixType.ofAgeModel W (ell + 1) x =
              RelationalPrefixType.ofAgeModel C (ell + 1) (original v)) ∧
        ∃ bad, bad ∈ family ∧ ¬ bad.Avoids W := by
  classical
  unfold PrescribedBoringData.CompatibleB3 at hFailure
  push_neg at hFailure
  obtain ⟨S0,hS0,hFailedAge⟩ := hFailure
  obtain ⟨W,hFinite,hSame,hUpper,hDelete,bad,hMember,hBad⟩ :=
    failedCommonSocleAgeTest_has_finite_L_witness
      family (prescribedOrdinarySocle (F.target S0))
      ell (F.CompatibleUpperLType S0) hFailedAge
  refine ⟨S0,hS0,W,hFinite,hSame,hDelete,?_,bad,hMember,hBad⟩
  intro x hx hAbove
  exact F.compatibleUpper_has_ambient_original C W original S0
    hRepresented hUpper x hx hAbove

/-- A forbidden configuration violating the finite-age conclusion
actually meets the tested coordinate. This conclusion covers both
allowed non-neutral-singleton obstructions and nontrivial irreducibles. -/
theorem normalizedForbidden_bad_copy_meets_tested_coordinate
    {db du dd : Nat}
    (W : AgeTestModel db du dd) (ell : Nat)
    (bad : NormalizedForbidden db du dd)
    (hDelete : bad.Avoids (W.withoutVertex ell))
    (hViolates : ¬ bad.Avoids W) :
    ∃ (r : Nat) (P : ForbiddenAtomicPattern r db du dd)
      (e : Fin r → Nat),
      W.Realizes P e ∧ ∃ a : Fin r, e a = ell := by
  cases bad with
  | singleton P hNonNeutral =>
      change ¬ ¬ ∃ e : Fin 1 → Nat, W.Realizes P e at hViolates
      push_neg at hViolates
      obtain ⟨e,hCopy⟩ := hViolates
      exact ⟨1,P,e,hCopy,
        forbiddenCopy_meets_tested_coordinate W ell P e hCopy hDelete⟩
  | nontrivial r P hr hIrred =>
      change ¬ ¬ ∃ e : Fin r → Nat, W.Realizes P e at hViolates
      push_neg at hViolates
      obtain ⟨e,hCopy⟩ := hViolates
      exact ⟨r,P,e,hCopy,
        forbiddenCopy_meets_tested_coordinate W ell P e hCopy hDelete⟩


/-- If every prescribed source comes from the same ambient partial
structure at the same cut, all source ordinary L+ socles agree.
The type vertices can still differ; this is exactly the ordinary-
socle compatibility required in the author's boring extension. -/
theorem PrescribedBoringData.source_pairwise_compatible_of_ambient
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (hSource : ∀ T, T ∈ F.source →
      ∃ v : Nat, T = A.partialTypeAt ell v)
    (T U : PartialTypeWithE ell db du dd)
    (hT : T ∈ F.source) (hU : U ∈ F.source) :
    SameOrdinaryAtCut T U := by
  obtain ⟨v,hv⟩ := hSource T hT
  obtain ⟨w,hw⟩ := hSource U hU
  rw [hv,hw]
  exact sameOrdinaryAtCut_sameAmbient A ell v w

/-- On a prescribed source family lying in ONE ordinary L+ ambient
socle, the manuscript's unqualified corrected B3 is equivalent to
the compatible-class B3 used in the implemented finite insertion.

This is the exact bridge needed before using a failed author B3
condition to choose a compatible B3 age witness. No shape-map
axiom or E-extension of an age witness is involved. -/
theorem PrescribedBoringData.correctedB3_iff_compatibleB3_of_one_socle
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hPairwise : ∀ T U, T ∈ F.source → U ∈ F.source →
      SameOrdinaryAtCut T U) :
    F.CorrectedB3 family ↔ F.CompatibleB3 family := by
  constructor
  · exact F.correctedB3_implies_compatibleB3 family
  · intro hB3 S0 hS0 W hFinite hSame hUpper hDelete
    have hUpperCompatible : UpperTypesPrescribed W ell
        (F.CompatibleUpperLType S0) := by
      intro x hx hAbove
      obtain ⟨T,hT,hType⟩ := hUpper x hx hAbove
      exact ⟨T,hT,hPairwise T S0 hT hS0,hType⟩
    exact hB3 S0 hS0 W hFinite hSame hUpperCompatible hDelete

/-- The manuscript's actual failed B3 test, rather than a separately
assumed compatible-class failure, produces a finite original-labelled
L-only witness whenever all source types and target crossing types
come from the same named ambient structure.

The conclusion is a failed age witness with a named ambient original
for EACH upper vertex. It is not a higher-arity generalization. -/
theorem PrescribedBoringData.failedCorrectedB3_has_ambient_original_witness
    {ell db du dd M : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (original : Fin M → Nat)
    (hSource : ∀ T, T ∈ F.source →
      ∃ v : Nat, T = A.partialTypeAt ell v)
    (hRepresented : ∀ T, T ∈ F.source →
      ∃ v : Fin M,
        (F.target T).lReduct =
          RelationalPrefixType.ofAgeModel A.L (ell + 1) (original v))
    (hFailure : ¬ F.CorrectedB3 family) :
    ∃ S0 : PartialTypeWithE ell db du dd,
      S0 ∈ F.source ∧
      ∃ W : AgeTestModel db du dd,
        W.BoundedCarrier ∧
        SameInitialL W (prescribedOrdinarySocle (F.target S0)) ell ∧
        (∀ bad, bad ∈ family → bad.Avoids (W.withoutVertex ell)) ∧
        (∀ x, x ∈ W.carrier → ell < x →
          ∃ v : Fin M,
            RelationalPrefixType.ofAgeModel W (ell + 1) x =
              RelationalPrefixType.ofAgeModel A.L (ell + 1) (original v)) ∧
        ∃ bad, bad ∈ family ∧ ¬ bad.Avoids W := by
  have hPairwise : ∀ T U, T ∈ F.source → U ∈ F.source →
      SameOrdinaryAtCut T U :=
    F.source_pairwise_compatible_of_ambient A hSource
  have hFailureCompatible : ¬ F.CompatibleB3 family := by
    intro hCompatible
    exact hFailure ((F.correctedB3_iff_compatibleB3_of_one_socle
      family hPairwise).2 hCompatible)
  exact F.failedCompatibleB3_has_ambient_original_witness
    family A.L original hRepresented hFailureCompatible


end SuccessorTree.V10

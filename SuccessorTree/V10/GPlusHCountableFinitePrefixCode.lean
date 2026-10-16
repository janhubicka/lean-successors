import SuccessorTree.V10.KptBaseToGOmega
import SuccessorTree.V10.GPlusOrdinaryCode
import Mathlib.Tactic

/-!
# Exact countable-to-finite H+ prefix codes in the universal G-omega

The numerical H+ construction is defined both at every finite
carrier N and on the entire countable carrier Nat. The real
countable finite-prefix operation clips only the E target and
preserves the same induced directed binary/unary/diagonal records.

For each v<N, the G+ vertex of the countable H+ initial segment
through v equals the genuine finite H+ code on its first v+1
vertices. No off-carrier atoms, phantom E expansions, or arbitrary
representation witnesses are introduced.

This is the exact transfer missing between the numerical HTop
seed-pair/palette arguments and the genuine fixed exhaustive
size-nondecreasing enumeration of G-omega.
-/

namespace SuccessorTree.V10

/-- Equality of complete finite on-carrier tables commutes with
dependent prefix restriction. The two bounds can be different
proofs: their proof irrelevance is handled when eliminating the
structure equality, rather than by ill-typed rewriting. -/
theorem FinitePartialCode.restrict_eq_of_eq
    {db du dd : Nat}
    {A B : FinitePartialCode db du dd}
    (h : A = B)
    (n : Nat) (hA : n ≤ A.size) (hB : n ≤ B.size) :
    A.restrict n hA = B.restrict n hB := by
  cases h
  rfl


/-- The finite prefix of the actual countable numerical H+ is
literally the existing finite numerical H+ constructor. All
non-data proof fields are definitionally irrelevant. -/
theorem infiniteNumericHPlus_finitePrefix_eq_finiteNumericH
    {db du dd : Nat}
    (K : AgeTestModel db du dd) (k N : Nat) :
    (infiniteNumericHPlus K k).finitePrefix N =
      finiteNumericH K k N := by
  rfl

/-- A countable numerical H+ G+ vertex has precisely the finite
prefix code from any enclosing finite numerical H+, retaining all
positive and absent directed binary, unary, diagonal and E bits. -/
theorem infiniteNumericHPlusToGPlus_finitePrefix_code
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N v : Nat) (hv : v + 1 ≤ N) :
    (infiniteNumericHPlusToGPlus family K hCarrier hAvoidK k v).val =
      FinitePartialCode.ofEnumerated
        ((finiteNumericH K k N).initialSegment (v + 1) hv) := by
  let C : CountableEnumeratedPartialStructure db du dd :=
    infiniteNumericHPlus K k
  calc
    (infiniteNumericHPlusToGPlus family K hCarrier hAvoidK k v).val =
        C.prefixCode (v + 1) := rfl
    _ = (C.prefixCode N).restrict (v + 1) hv :=
      (C.prefixCode_restrict (v + 1) N hv).symm
    _ = (FinitePartialCode.ofEnumerated (C.finitePrefix N)).restrict
          (v + 1) hv := by
      exact FinitePartialCode.restrict_eq_of_eq
        (C.ofEnumerated_finitePrefix N).symm
        (v + 1) hv hv
    _ = FinitePartialCode.ofEnumerated
          ((C.finitePrefix N).initialSegment (v + 1) hv) :=
      FinitePartialCode.ofEnumerated_initialSegment _ _ _
    _ = FinitePartialCode.ofEnumerated
          ((finiteNumericH K k N).initialSegment (v + 1) hv) := by
      have hSame :
          C.finitePrefix N = finiteNumericH K k N :=
        infiniteNumericHPlus_finitePrefix_eq_finiteNumericH K k N
      have hSegment :
          (C.finitePrefix N).initialSegment (v + 1) hv =
            (finiteNumericH K k N).initialSegment (v + 1) hv := by
        cases hSame
        rfl
      exact congrArg FinitePartialCode.ofEnumerated hSegment

/-- Evaluation in the actual exhaustive size-ordered G-omega
enumeration is the same genuine finite H+ prefix code. -/
theorem infiniteNumericHPlusToGOmega_finitePrefix_code
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N v : Nat) (hv : v + 1 ≤ N) :
    let C := infiniteNumericHPlus K k
    let hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L :=
      infiniteNumericHL_avoids_family family K hCarrier hAvoidK k
    (GPlusEnumeration.enumerate C family hAvoid
      (C.toGOmega family hAvoid v)).val =
      FinitePartialCode.ofEnumerated
        ((finiteNumericH K k N).initialSegment (v + 1) hv) := by
  let C := infiniteNumericHPlus K k
  let hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L :=
    infiniteNumericHL_avoids_family family K hCarrier hAvoidK k
  change (GPlusEnumeration.enumerate C family hAvoid
    (C.toGOmega family hAvoid v)).val =
      FinitePartialCode.ofEnumerated
        ((finiteNumericH K k N).initialSegment (v + 1) hv)
  rw [C.toGOmega_eval family hAvoid v]
  exact infiniteNumericHPlusToGPlus_finitePrefix_code
    family K hCarrier hAvoidK k N v hv

/-- The same finite prefix code is read in a single FIXED
G-omega enumeration chosen independently of the base K.
The only C+ witness used by the enumeration is its proof
of layer nonemptiness; the numerical H+ and all prefix codes
are still the genuine input K constructions. -/
theorem infiniteNumericHPlusToFixedGOmega_finitePrefix_code
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (C : CountableEnumeratedPartialStructure db du dd)
    (hAvoidC : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N v : Nat) (hv : v + 1 ≤ N) :
    let H := infiniteNumericHPlus K k
    let hAvoidH : ∀ bad, bad ∈ family → bad.Avoids H.L :=
      infiniteNumericHL_avoids_family family K hCarrier hAvoidK k
    (GPlusEnumeration.enumerate C family hAvoidC
      (H.toGOmega family hAvoidH v)).val =
      FinitePartialCode.ofEnumerated
        ((finiteNumericH K k N).initialSegment (v + 1) hv) := by
  let H := infiniteNumericHPlus K k
  let hAvoidH : ∀ bad, bad ∈ family → bad.Avoids H.L :=
    infiniteNumericHL_avoids_family family K hCarrier hAvoidK k
  have hEnum : GPlusEnumeration.enumerate C family hAvoidC =
      GPlusEnumeration.enumerate H family hAvoidH :=
    GPlusEnumeration.enumerate_independent_of_witness family C H
      hAvoidC hAvoidH
  change (GPlusEnumeration.enumerate C family hAvoidC
    (H.toGOmega family hAvoidH v)).val =
      FinitePartialCode.ofEnumerated
        ((finiteNumericH K k N).initialSegment (v + 1) hv)
  rw [hEnum]
  exact infiniteNumericHPlusToGOmega_finitePrefix_code
    family K hCarrier hAvoidK k N v hv

end SuccessorTree.V10

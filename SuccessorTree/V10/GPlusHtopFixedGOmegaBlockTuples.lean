import SuccessorTree.V10.GPlusHCountableFinitePrefixCode
import SuccessorTree.V10.GPlusHTopTuplePalette
import SuccessorTree.V10.HTopRootStrictPrefix
import Mathlib.Tactic

/-!
# Tuples of genuine top-generation G-omega vertices are finite HTop prefixes

Every q-tuple of top-generation vertices of the SAME countable numerical
H+ arises from finitely many original indices. Choose a numerical top
root j larger than all of these indices and a finite H+ truncation N
containing them. The full G-omega codes of the vertices are then exactly
the finite numerical H+ initial-prefix codes supplied to the envelope
algorithm. Both binary orientations, absent facts, unary/diagonal
records and all genuine E bits are retained.

The fixed G-omega enumeration is independent of the base K. The
tuple may have repeated indices; nothing about being an induced A-copy
is presupposed. A later theorem will combine this statement with
uniform height bounds and genuine finite approximation lifting to
obtain ONE covering palette for all tuples, not a W chosen separately
for each tuple.
-/

namespace SuccessorTree.V10

/-- In the fixed exhaustive enumeration of all genuine G+ vertices,
every tuple of countable numerical H+ top-generation vertices indexed
by a chosen finite block set is among the exact finite numerical HTop
prefix tuples for an enclosing next top root. -/
theorem numericHTop_fixedGOmega_tuple_mem_prefixTuples
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (C : CountableEnumeratedPartialStructure db du dd)
    (hAvoidC : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k j q : Nat) (blocks : Finset Nat)
    (hEarlier : ∀ i, i ∈ blocks → i < j)
    (indices : Fin q → Nat)
    (hIndices : ∀ i, indices i ∈ blocks) :
    (fun i : Fin q =>
      GPlusEnumeration.enumerate C family hAvoidC
        ((infiniteNumericHPlus K k).toGOmega family
          (infiniteNumericHL_avoids_family
            family K hCarrier hAvoidK k)
          (hPosition k (indices i) k))) ∈
      numericHTopPrefixTuples family K k
        (hPosition k j k + 1) blocks q := by
  intro i
  have hEarlierI : indices i < j := hEarlier (indices i) (hIndices i)
  have hPositionLt :
      hPosition k (indices i) k < hPosition k j k :=
    hPosition_lt_of_block_lt k (indices i) j k k le_rfl hEarlierI
  have hSize : hPosition k (indices i) k + 1 ≤
      (finiteNumericH K k (hPosition k j k + 1)).size := by
    change hPosition k (indices i) k + 1 ≤ hPosition k j k + 1
    omega
  refine ⟨indices i, hIndices i, hSize, ?_⟩
  exact infiniteNumericHPlusToFixedGOmega_finitePrefix_code
    family C hAvoidC K hCarrier hAvoidK k
    (hPosition k j k + 1) (hPosition k (indices i) k) hSize

/-- Choose the same finite block set and a later HTop root for every
coordinate of any finite tuple of original K indices, including the
empty tuple. The finite set has at most q elements. -/
theorem numericHTop_indices_common_later_root
    {q : Nat} (indices : Fin q → Nat) :
    ∃ (blocks : Finset Nat) (j : Nat),
      blocks.card ≤ q ∧
      0 < j ∧
      (∀ i : Fin q, indices i ∈ blocks) ∧
      (∀ i, i ∈ blocks → i < j) := by
  classical
  let blocks : Finset Nat := Finset.univ.image indices
  let j : Nat := (Finset.univ : Finset (Fin q)).sup indices + 1
  refine ⟨blocks, j, ?_, by dsimp [j]; omega, ?_, ?_⟩
  · calc
      blocks.card ≤ (Finset.univ : Finset (Fin q)).card :=
        Finset.card_image_le
      _ = q := by simp
  · intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · intro i hi
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hi
    have hBound : indices a ≤
        (Finset.univ : Finset (Fin q)).sup indices :=
      Finset.le_sup (Finset.mem_univ a)
    dsimp [j]
    omega

end SuccessorTree.V10

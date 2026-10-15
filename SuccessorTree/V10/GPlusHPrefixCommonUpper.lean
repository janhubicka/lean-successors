import SuccessorTree.V10.GPlusCommonUpperRepresentation
import SuccessorTree.V10.CountableGPlusEmbedding
import Mathlib.Tactic

/-!
# V10 Definition 6.43: actual H+ prefix chains share one Kpt upper node

Every countable forbidden-free enumerated partial L+ structure C+ has
the genuine G+ code C_n of its first n+1 numbered vertices.
These codes form one exact finite-table prefix chain. For any N,
ALL codes C_0,...,C_N are prefixes of the actual full code C_N.

The previously checked canonical neutral-cap theorem and common-upper
representation of G+ prefixes therefore give one genuine admissible
Kpt type U_N above this entire finite chain, with literal representing
pairs (S_i,U_N) satisfying v(S_i,U_N)=C_i for every i<=N.

The statement is also specialized to the already verified countable
numerical H+, using its genuine forbidden-age avoidance theorem;
no new age/representation assumption is inserted. This supplies
the exact FINITE source pair family for the next Algorithm 5.4
envelope seed and height calculation. The existence of a sufficiently
short finite approximation and the final Ramsey colouring assembly
are still separate obligations.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

namespace CountableEnumeratedPartialStructure

/-- The canonical finite G+ codes of any actual countable partial
L+ structure form an exact induced finite-table prefix chain. -/
theorem toGPlus_code_prefix_of_le
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L)
    {i j : Nat} (hij : i ≤ j) :
    (C.toGPlus family hAvoid i).val.IsPrefix
      (C.toGPlus family hAvoid j).val := by
  rcases lt_or_eq_of_le hij with hlt | heq
  · exact (C.toGPlus_properPrefix family hAvoid hlt).1
  · subst j
    exact FinitePartialCode.isPrefix_refl _

/-- ALL finite initial vertices C_0,...,C_N admit ACTUAL strict
representing Kpt pairs with ONE shared upper node: the canonical
neutral cap of the full code C_N. The represented G+ vertex is
literally the original finite prefix code, including every absent
L+ atomic relation and auxiliary E bit. -/
theorem toGPlus_prefixes_have_common_upper
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (N : Nat) :
    let U : AdmissibleKptNode family :=
      (C.toGPlus family hAvoid N).canonicalCap
    ∀ i : Nat, i ≤ N →
      ∃ P : GPlusRepresentingPair family,
        P.upper = U ∧ P.vertex = C.toGPlus family hAvoid i := by
  dsimp only
  intro i hi
  let U : AdmissibleKptNode family :=
    (C.toGPlus family hAvoid N).canonicalCap
  have hPrefix :
      (C.toGPlus family hAvoid i).val.IsPrefix
        (RawPartialTypeNode.ordinaryCode U.1) := by
    have h := C.toGPlus_code_prefix_of_le family hAvoid hi
    have hCode := (C.toGPlus family hAvoid N).canonicalCap_ordinaryCode
    rw [hCode]
    exact h
  let P := GPlusRepresentingPair.fromUpper U
    (C.toGPlus family hAvoid i).val.size
    (finiteGPlusVertex_size_pos (C.toGPlus family hAvoid i))
    hPrefix.1
  exact ⟨P, rfl,
    GPlusRepresentingPair.fromUpper_vertex_eq_of_prefix
      U (C.toGPlus family hAvoid i) hPrefix⟩

/-- The same common-upper statement for the FINITE indexed family
of first N+1 vertices, avoiding a standalone infinite surjectivity
or choice assumption. -/
theorem toGPlus_prefixes_range_common_upper
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (N : Nat) :
    let U : AdmissibleKptNode family :=
      (C.toGPlus family hAvoid N).canonicalCap
    ∀ i ∈ Finset.range (N+1),
      ∃ P : GPlusRepresentingPair family,
        P.upper = U ∧ P.vertex = C.toGPlus family hAvoid i := by
  dsimp only
  intro i hi
  have hiN : i ≤ N := by
    have hiLt : i < N+1 := Finset.mem_range.mp hi
    omega
  exact C.toGPlus_prefixes_have_common_upper family hAvoid N i hiN

end CountableEnumeratedPartialStructure

/-- Concrete numerical H+ specialization: every finite set of its
first N+1 G+ prefix vertices is represented by actual Kpt pairs
with one common admissible upper type.
This uses the existing checked H+ forbidden-age theorem directly. -/
theorem infiniteNumericHPlus_GPlus_prefixes_have_common_upper
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat) :
    let C := infiniteNumericHPlus K k
    let hAvoidC :=
      infiniteNumericHL_avoids_family family K hCarrier hAvoidK k
    let U : AdmissibleKptNode family :=
      (C.toGPlus family hAvoidC N).canonicalCap
    ∀ i : Nat, i ≤ N →
      ∃ P : GPlusRepresentingPair family,
        P.upper = U ∧ P.vertex = C.toGPlus family hAvoidC i := by
  exact (infiniteNumericHPlus K k).toGPlus_prefixes_have_common_upper
    family (infiniteNumericHL_avoids_family family K hCarrier hAvoidK k) N

end SuccessorTree.V10

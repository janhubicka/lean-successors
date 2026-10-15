import SuccessorTree.V10.HInfiniteBaseEmbedding
import SuccessorTree.V10.HFinitePartial
import Mathlib.Tactic

/-!
# Countable numerical H+ and its coherent finite partial segments

The original v10 Proposition 6.44 needs a countable enumerated
L+ partial structure H+, not only the forbidden-free L-reduct H.
This file constructs H+ directly from the exact generated E
relation already verified for finite H.

A countable enumerated partial structure has all Nat vertices,
complete directed L records, and an E relation satisfying the
same spacing/downward/linkage axioms as finite partial structures.
Every finite initial segment is then a genuine verified
EnumeratedPartialStructure, with E clipped only at the target.

For the numerical H+ model, every finite initial segment has
EXACTLY the same L and E records as finiteNumericH K k N.
The initial segments form a coherent tower and their canonical
free-cut values agree for vertices already in the smaller segment.
No auxiliary E is manufactured on an arbitrary finite L-age
witness. This is the countable H+ part of the K-to-G+ transfer;
the universal G+ vertex coding is handled separately.
-/

namespace SuccessorTree.V10

/-- The countable counterpart of Definition 6.28. Its carrier
is all Nat. Nullary data remain fixed outside this record;
unary and diagonal records are retained in the L-reduct. -/
structure CountableEnumeratedPartialStructure
    (db du dd : Nat) where
  L : AgeTestModel db du dd
  fullCarrier : ∀ v : Nat, v ∈ L.carrier
  E : Nat → Nat → Bool
  spaced : SpacedE E
  downward : DownwardE E
  linked_E : ∀ u v : Nat, u < v →
    (∃ a : Fin db,
      L.binary u v a = true ∨ L.binary v u a = true) →
    E u v = true

/-- The finite initial segment is an ACTUAL finite enumerated
partial structure. Only the E TARGET is clipped, exactly as
in the verified finite numerical H constructor. -/
noncomputable def CountableEnumeratedPartialStructure.finitePrefix
    {db du dd : Nat}
    (C : CountableEnumeratedPartialStructure db du dd)
    (N : Nat) : EnumeratedPartialStructure db du dd where
  size := N
  L := {
    carrier := {v | v < N}
    binary := C.L.binary
    unary := C.L.unary
    diagonal := C.L.diagonal }
  carrier_iff := by intro v; rfl
  E := fun u v => if v < N then C.E u v else false
  E_inside := by
    intro u v h
    by_cases hv : v < N
    · have hE : C.E u v = true := by simpa [hv] using h
      have hs := C.spaced u v hE
      omega
    · simp [hv] at h
  spaced := by
    intro u v h
    by_cases hv : v < N
    · exact C.spaced u v (by simpa [hv] using h)
    · simp [hv] at h
  downward := by
    intro u v h w hw
    by_cases hv : v < N
    · have hE : C.E u v = true := by simpa [hv] using h
      change (if v < N then C.E w v else false) = true
      simp [hv, C.downward u v hE w hw]
    · simp [hv] at h
  linked_E := by
    intro u v huv _hu hv hLink
    change (if v < N then C.E u v else false) = true
    simp [hv, C.linked_E u v huv hLink]

/-- Full directed L data of finite initial segments are literally
unchanged as the prefix length grows. -/
theorem CountableEnumeratedPartialStructure.finitePrefix_binary_agree
    {db du dd : Nat}
    (C : CountableEnumeratedPartialStructure db du dd)
    (N M x y : Nat) (a : Fin db) :
    (C.finitePrefix N).L.binary x y a =
      (C.finitePrefix M).L.binary x y a := rfl

theorem CountableEnumeratedPartialStructure.finitePrefix_unary_agree
    {db du dd : Nat}
    (C : CountableEnumeratedPartialStructure db du dd)
    (N M x : Nat) (a : Fin du) :
    (C.finitePrefix N).L.unary x a =
      (C.finitePrefix M).L.unary x a := rfl

theorem CountableEnumeratedPartialStructure.finitePrefix_diagonal_agree
    {db du dd : Nat}
    (C : CountableEnumeratedPartialStructure db du dd)
    (N M x : Nat) (a : Fin dd) :
    (C.finitePrefix N).L.diagonal x a =
      (C.finitePrefix M).L.diagonal x a := rfl

/-- The countable E field is coherent: no E atom between
vertices already in the shorter initial segment can change. -/
theorem CountableEnumeratedPartialStructure.finitePrefix_E_agree
    {db du dd : Nat}
    (C : CountableEnumeratedPartialStructure db du dd)
    {N M : Nat} (hNM : N ≤ M)
    (u v : Nat) (hv : v < N) :
    (C.finitePrefix N).E u v =
      (C.finitePrefix M).E u v := by
  change (if v < N then C.E u v else false) =
    (if v < M then C.E u v else false)
  simp [hv, lt_of_lt_of_le hv hNM]

/-- The intrinsic finite free cut is the SAME canonical free
cut of the global E relation. Proof is by uniqueness of the
first missing column position, not by equality of choice proofs. -/
theorem CountableEnumeratedPartialStructure.finitePrefix_freeLevel_eq
    {db du dd : Nat}
    (C : CountableEnumeratedPartialStructure db du dd)
    (N v : Nat) (hv : v < N) :
    (C.finitePrefix N).freeLevel v =
      canonicalFreeLevel C.E C.spaced C.downward v := by
  have hColumn : ∀ u : Nat,
      (C.finitePrefix N).E u v = C.E u v := by
    intro u
    change (if v < N then C.E u v else false) = C.E u v
    simp [hv]
  have hGlobal : IsFreeCut C.E v
      (canonicalFreeLevel C.E C.spaced C.downward v) :=
    canonicalFreeLevel_isFreeCut C.E C.spaced C.downward v
  have hLocal : IsFreeCut (C.finitePrefix N).E v
      (canonicalFreeLevel C.E C.spaced C.downward v) := by
    constructor
    · intro u hu
      rw [hColumn u]
      exact hGlobal.1 u hu
    · rw [hColumn]
      exact hGlobal.2
  have hChosen : IsFreeCut (C.finitePrefix N).E v
      (C.finitePrefix N).freeLevel v :=
    canonicalFreeLevel_isFreeCut
      (C.finitePrefix N).E
      (C.finitePrefix N).spaced
      (C.finitePrefix N).downward v
  exact freeCut_unique (C.finitePrefix N).E v
    (C.finitePrefix N).freeLevel v
    (canonicalFreeLevel C.E C.spaced C.downward v)
    hChosen hLocal

/-- Coherence of the canonical free level of any old original. -/
theorem CountableEnumeratedPartialStructure.finitePrefix_freeLevel_agree
    {db du dd : Nat}
    (C : CountableEnumeratedPartialStructure db du dd)
    {N M : Nat} (hNM : N ≤ M)
    (v : Nat) (hv : v < N) :
    (C.finitePrefix N).freeLevel v =
      (C.finitePrefix M).freeLevel v := by
  exact (C.finitePrefix_freeLevel_eq N v hv).trans
    (C.finitePrefix_freeLevel_eq M v
      (lt_of_lt_of_le hv hNM)).symm

/-- The ACTUAL countable numerical H+ structure. -/
noncomputable def infiniteNumericHPlus
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k : Nat) : CountableEnumeratedPartialStructure db du dd where
  L := infiniteNumericHL K k
  fullCarrier := by intro v; trivial
  E := exactHEBool k
  spaced := exactHEBool_spaced k
  downward := exactHEBool_downward k
  linked_E := by
    intro u v huv hLink
    exact hNumericBinary_linked_E K.binary k u v huv hLink

/-- Full finite L-reduct equality, not just equality of edges. -/
theorem infiniteNumericHPlus_prefix_L
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N : Nat) :
    ((infiniteNumericHPlus K k).finitePrefix N).L =
      finiteNumericHL K k N := rfl

/-- Finite E is exactly the restricted genuine global E column. -/
theorem infiniteNumericHPlus_prefix_E
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N u v : Nat) :
    ((infiniteNumericHPlus K k).finitePrefix N).E u v =
      (finiteNumericH K k N).E u v := rfl

/-- Exact canonical free-cut coherence with the finite H
construction, including all old vertices, not just real ones. -/
theorem infiniteNumericHPlus_prefix_freeLevel
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N v : Nat) (hv : v < N) :
    ((infiniteNumericHPlus K k).finitePrefix N).freeLevel v =
      (finiteNumericH K k N).freeLevel v := by
  have hC :
      ((infiniteNumericHPlus K k).finitePrefix N).freeLevel v =
        canonicalFreeLevel (exactHEBool k)
          (exactHEBool_spaced k) (exactHEBool_downward k) v :=
    (infiniteNumericHPlus K k).finitePrefix_freeLevel_eq N v hv
  have hCutGlobal :
      IsFreeCut (exactHEBool k) v
        (canonicalFreeLevel (exactHEBool k)
          (exactHEBool_spaced k) (exactHEBool_downward k) v) :=
    canonicalFreeLevel_isFreeCut (exactHEBool k)
      (exactHEBool_spaced k) (exactHEBool_downward k) v
  have hColumn : ∀ u : Nat,
      (finiteNumericH K k N).E u v = exactHEBool k u v := by
    intro u
    change finiteNumericHE k N u v = exactHEBool k u v
    simp [finiteNumericHE, hv]
  have hCutFinite : IsFreeCut (finiteNumericH K k N).E v
      (canonicalFreeLevel (exactHEBool k)
        (exactHEBool_spaced k) (exactHEBool_downward k) v) := by
    constructor
    · intro u hu
      rw [hColumn u]
      exact hCutGlobal.1 u hu
    · rw [hColumn]
      exact hCutGlobal.2
  have hSelected : IsFreeCut (finiteNumericH K k N).E v
      (finiteNumericH K k N).freeLevel v :=
    canonicalFreeLevel_isFreeCut
      (finiteNumericH K k N).E
      (finiteNumericH K k N).spaced
      (finiteNumericH K k N).downward v
  exact hC.trans (freeCut_unique (finiteNumericH K k N).E
    v _ _ hSelected hCutFinite).symm

/-- The finite prefixes of the real countable partial H+ have
the exact forbidden-free L-age proved for finite numerical H. -/
theorem infiniteNumericHPlus_prefix_avoids_family
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat) :
    ∀ bad, bad ∈ family →
      bad.Avoids ((infiniteNumericHPlus K k).finitePrefix N).L := by
  intro bad hBad
  change bad.Avoids (finiteNumericHL K k N)
  exact bad.finiteNumericH_preserves_avoidance
    K hCarrier k N (hAvoidK bad hBad)

end SuccessorTree.V10
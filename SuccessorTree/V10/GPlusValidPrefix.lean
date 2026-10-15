import SuccessorTree.V10.GPlusFinitePrefix
import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# Definition 6.40: admissible G+ vertices are closed under nonempty prefixes

The canonical finite table representation makes G+ literally
countable. But it is not enough to define prefixes for arbitrary
tables: the actual G+ vertex type consists of codes of VALID finite
enumerated L+ partial structures with forbidden-free L-age.

The prefix of such a structure is an actual valid partial structure:
its L-carrier is restricted to the smaller initial segment without
changing any induced directed binary, unary or diagonal atoms; E is
clipped at the target exactly as in the verified H+ tower.
Spacing, downward closure and the linked-E axiom follow from the
original predicates. Forbidden avoidance is hereditary under
restriction of the carrier, for BOTH nontrivial and singleton
forbidden patterns. No arbitrary E on L-only witnesses occurs.

Thus every positive-length prefix of a canonical G+ vertex is a
G+ vertex, and its finite code is literally the table restriction.
This is the missing prefix-closure prerequisite for G+ being a
genuine countable rooted forest/tree in the original v10 proof.
-/

namespace SuccessorTree.V10

/-- The genuine finite initial segment of an arbitrary verified
enumerated partial L+ structure, preserving all induced L atoms
and truncating E only in the target coordinate. -/
noncomputable def EnumeratedPartialStructure.initialSegment
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) (hn : n ≤ A.size) :
    EnumeratedPartialStructure db du dd where
  size := n
  L := A.L.restrictCarrier (fun x => x < n)
  carrier_iff := by
    intro v
    change (v ∈ A.L.carrier ∧ v < n) ↔ v < n
    constructor
    · exact And.right
    · intro hv
      exact ⟨(A.carrier_iff v).2 (lt_of_lt_of_le hv hn),hv⟩
  E := fun u v => if v < n then A.E u v else false
  E_inside := by
    intro u v h
    by_cases hv : v < n
    · have hA : A.E u v = true := by
        simpa only [if_pos hv] using h
      have hSpaced := A.spaced u v hA
      exact ⟨by omega,hv⟩
    · simp [hv] at h
  spaced := by
    intro u v h
    by_cases hv : v < n
    · exact A.spaced u v (by simpa only [if_pos hv] using h)
    · simp [hv] at h
  downward := by
    intro u v h w hwu
    by_cases hv : v < n
    · have hA : A.E u v = true := by
        simpa only [if_pos hv] using h
      change (if v < n then A.E w v else false) = true
      simp [hv, A.downward u v hA w hwu]
    · simp [hv] at h
  linked_E := by
    intro u v huv hu hv hLink
    have huA : u < A.size := lt_of_lt_of_le hu hn
    have hvA : v < A.size := lt_of_lt_of_le hv hn
    change (if v < n then A.E u v else false) = true
    simp [hv, A.linked_E u v huv huA hvA hLink]

/-- Avoiding a forbidden induced pattern survives deleting
arbitrary carrier vertices, with all atomic bits unchanged. -/
theorem NormalizedForbidden.avoids_restrictCarrier
    {db du dd : Nat}
    (bad : NormalizedForbidden db du dd)
    (L : AgeTestModel db du dd)
    (P : Nat → Prop)
    (hAvoid : bad.Avoids L) :
    bad.Avoids (L.restrictCarrier P) := by
  cases bad with
  | singleton F hNeutral =>
      rintro ⟨f,hF⟩
      apply hAvoid
      exact ⟨f,L.realizes_of_restrictCarrier P F f hF⟩
  | nontrivial r F hr hIrred =>
      rintro ⟨f,hF⟩
      apply hAvoid
      exact ⟨f,L.realizes_of_restrictCarrier P F f hF⟩

/-- Every finite prefix of a forbidden-free partial structure
is forbidden-free, even when absence of atoms matters. -/
theorem EnumeratedPartialStructure.initialSegment_avoids
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (n : Nat) (hn : n ≤ A.size) :
    ∀ bad, bad ∈ family →
      bad.Avoids (A.initialSegment n hn).L := by
  intro bad hBad
  exact bad.avoids_restrictCarrier A.L (fun x => x < n)
    (hAvoid bad hBad)

/-- The finite table restriction of an actual L+ structure is
exactly the canonical table of its genuine initial-segment
partial structure, not just equivalent up to some renaming. -/
theorem FinitePartialCode.ofEnumerated_initialSegment
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) (hn : n ≤ A.size) :
    (FinitePartialCode.ofEnumerated A).restrict n hn =
      FinitePartialCode.ofEnumerated (A.initialSegment n hn) := by
  cases h : (FinitePartialCode.ofEnumerated A).restrict n hn with
  | mk size binary unary diagonal eRelation =>
      have hSize : size = n := by
        simpa [h] using
          (FinitePartialCode.restrict_size
            (FinitePartialCode.ofEnumerated A) n hn)
      subst size
      have hBinary :
          binary = (FinitePartialCode.ofEnumerated
            (A.initialSegment n hn)).binary := by
        funext i j a
        have hAt := congrArg
          (fun C : FinitePartialCode db du dd => C.binary i j a) h
        simpa [FinitePartialCode.ofEnumerated,
          FinitePartialCode.restrict,
          EnumeratedPartialStructure.initialSegment,
          AgeTestModel.restrictCarrier] using hAt.symm
      have hUnary :
          unary = (FinitePartialCode.ofEnumerated
            (A.initialSegment n hn)).unary := by
        funext i a
        have hAt := congrArg
          (fun C : FinitePartialCode db du dd => C.unary i a) h
        simpa [FinitePartialCode.ofEnumerated,
          FinitePartialCode.restrict,
          EnumeratedPartialStructure.initialSegment,
          AgeTestModel.restrictCarrier] using hAt.symm
      have hDiagonal :
          diagonal = (FinitePartialCode.ofEnumerated
            (A.initialSegment n hn)).diagonal := by
        funext i a
        have hAt := congrArg
          (fun C : FinitePartialCode db du dd => C.diagonal i a) h
        simpa [FinitePartialCode.ofEnumerated,
          FinitePartialCode.restrict,
          EnumeratedPartialStructure.initialSegment,
          AgeTestModel.restrictCarrier] using hAt.symm
      have hE :
          eRelation = (FinitePartialCode.ofEnumerated
            (A.initialSegment n hn)).eRelation := by
        funext i j
        have hAt := congrArg
          (fun C : FinitePartialCode db du dd => C.eRelation i j) h
        simpa [FinitePartialCode.ofEnumerated,
          FinitePartialCode.restrict,
          EnumeratedPartialStructure.initialSegment, j.isLt] using hAt.symm
      simp [FinitePartialCode.ofEnumerated,
        hBinary,hUnary,hDiagonal,hE] at *

/-- Positive-length prefixes remain canonical forbidden-free
G+ vertices, not merely arbitrary finite table records. -/
noncomputable def FiniteGPlusVertex.restrict
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (C : FiniteGPlusVertex family)
    (n : Nat) (hPos : 0 < n) (hn : n ≤ C.val.size) :
    FiniteGPlusVertex family := by
  classical
  obtain ⟨A,hCode,hAPos,hAvoid⟩ := C.property
  have hnA : n ≤ A.size := by
    rw [hCode] at hn
    exact hn
  let B := A.initialSegment n hnA
  have hCodeB :
      C.val.restrict n hn = FinitePartialCode.ofEnumerated B := by
    have hEq := FinitePartialCode.ofEnumerated_initialSegment A n hnA
    cases hCode
    exact hEq
  exact ⟨C.val.restrict n hn,
    B,hCodeB,by simpa only [B] using hPos,
    A.initialSegment_avoids family hAvoid n hnA⟩

/-- The selected prefix is a literal ancestor in the finite-code
prefix relation of Definition 6.40. -/
theorem FiniteGPlusVertex.restrict_isPrefix
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (C : FiniteGPlusVertex family)
    (n : Nat) (hPos : 0 < n) (hn : n ≤ C.val.size) :
    (C.restrict n hPos hn).val.IsPrefix C.val := by
  exact ⟨hn,rfl⟩

end SuccessorTree.V10

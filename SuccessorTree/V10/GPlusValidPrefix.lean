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
  -- Compare the four literal on-carrier tables. Every index of the
  -- smaller code satisfies j.val<n, so clipping the E target does
  -- not alter a single on-carrier E bit.
  change
    (FinitePartialCode.mk n
      (fun i j a => A.L.binary i.val j.val a)
      (fun i a => A.L.unary i.val a)
      (fun i a => A.L.diagonal i.val a)
      (fun i j => A.E i.val j.val)) =
    (FinitePartialCode.mk n
      (fun i j a => A.L.binary i.val j.val a)
      (fun i a => A.L.unary i.val a)
      (fun i a => A.L.diagonal i.val a)
      (fun i j => if j.val < n then A.E i.val j.val else false))
  have hE :
      (fun i j : Fin n => A.E i.val j.val) =
      (fun i j : Fin n =>
        if j.val < n then A.E i.val j.val else false) := by
    funext i j
    simp only [if_pos j.isLt]
  rw [← hE]

/-- Congruence of finite-code restriction even though its length
bound has a proof-dependent source. -/
private theorem finiteCode_restrict_eq_of_eq
    {db du dd : Nat}
    {C D : FinitePartialCode db du dd}
    (h : C = D) (n : Nat)
    (hC : n ≤ C.size) (hD : n ≤ D.size) :
    C.restrict n hC = D.restrict n hD := by
  cases h
  rfl

/-- Positive-length prefixes remain canonical forbidden-free
G+ vertices, not merely arbitrary finite table records. -/
noncomputable def FiniteGPlusVertex.restrict
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (C : FiniteGPlusVertex family)
    (n : Nat) (hPos : 0 < n) (hn : n ≤ C.val.size) :
    FiniteGPlusVertex family := by
  classical
  let A : EnumeratedPartialStructure db du dd :=
    Classical.choose C.property
  obtain ⟨hCode,hAPos,hAvoid⟩ := Classical.choose_spec C.property
  have hnA : n ≤ A.size := by
    exact (congrArg FinitePartialCode.size hCode) ▸ hn
  let B : EnumeratedPartialStructure db du dd :=
    A.initialSegment n hnA
  have hCodeB :
      C.val.restrict n hn = FinitePartialCode.ofEnumerated B := by
    exact (finiteCode_restrict_eq_of_eq hCode n hn hnA).trans
      (FinitePartialCode.ofEnumerated_initialSegment A n hnA)
  exact ⟨C.val.restrict n hn,
    ⟨B,hCodeB,hPos,A.initialSegment_avoids family hAvoid n hnA⟩⟩

/-- The selected prefix is a literal ancestor in the finite-code
prefix relation of Definition 6.40. -/
theorem FiniteGPlusVertex.restrict_isPrefix
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (C : FiniteGPlusVertex family)
    (n : Nat) (hPos : 0 < n) (hn : n ≤ C.val.size) :
    (C.restrict n hPos hn).val.IsPrefix C.val := by
  change ∃ h : n ≤ C.val.size,
    (C.val.restrict n hn) = C.val.restrict n h
  exact ⟨hn,rfl⟩

end SuccessorTree.V10

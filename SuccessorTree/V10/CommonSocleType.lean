import SuccessorTree.V10.PartialTypeRestriction

/-!
# Exact complete-type comparisons over a common ambient L+ socle

This closes an important local-record step in the manuscript's v10
meet calculation. Two type vertices v,w from the SAME enumerated
partial structure A are compared through an initial cut d below BOTH
free levels, and the level-zero (singleton) types agree.

Then their complete induced L+ types through d are equal if and only
if all directed binary relation bits involving the type vertex and a
socle vertex below d agree. The common ambient supplies all relations
IN the socle; equality at level zero supplies unary/diagonal and
type-vertex loop data; the free-level equations supply all E bits
between t and the socle, including reversed pairs.

Unlike a comparison of binary traces in isolation, this actually
checks the complete records, including E, loops, singleton data,
negative relation bits and every ordered direction.

The final theorem converts an earliest binary difference at coordinate
d into equality of the full predecessors of height d and inequality at
height d+1. The remaining Kpt/LevelTree adapter must identify these
induced restrictions with the actual ancestors and their meet.
-/

namespace SuccessorTree.V10

/-- The two complete directed relation patterns from a type vertex
to the same initial segment of the ambient structure. -/
def SameAmbientCrossType
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (v w d : Nat) : Prop :=
  (∀ i : Fin d, ∀ r : Fin db,
    A.L.binary i.val v r = A.L.binary i.val w r) ∧
  (∀ i : Fin d, ∀ r : Fin db,
    A.L.binary v i.val r = A.L.binary w i.val r)

/-- In a common ambient partial structure, shared level-zero types
and equality of all cross L-relations determine the entire L+ types
at a cut below both free levels. In particular the E components are
reconstructed, not silently omitted. -/
theorem sameAmbient_partialType_eq_of_cross
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (v w d : Nat)
    (hv : d ≤ A.freeLevel v) (hw : d ≤ A.freeLevel w)
    (hRoot : A.partialTypeAt 0 v = A.partialTypeAt 0 w)
    (hCross : SameAmbientCrossType A v w d) :
    A.partialTypeAt d v = A.partialTypeAt d w := by
  have hRootB : ∀ r : Fin db,
      A.L.binary v v r = A.L.binary w w r := by
    intro r
    have h := congrArg
      (fun T : PartialTypeWithE 0 db du dd =>
        T.lReduct.binary none none r) hRoot
    exact h
  have hRootU : ∀ r : Fin du,
      A.L.unary v r = A.L.unary w r := by
    intro r
    have h := congrArg
      (fun T : PartialTypeWithE 0 db du dd =>
        T.lReduct.unary none r) hRoot
    exact h
  have hRootD : ∀ r : Fin dd,
      A.L.diagonal v r = A.L.diagonal w r := by
    intro r
    have h := congrArg
      (fun T : PartialTypeWithE 0 db du dd =>
        T.lReduct.diagonal none r) hRoot
    exact h
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      cases a with
      | none =>
        cases b with
        | none => exact hRootB r
        | some j => exact hCross.2 j r
      | some i =>
        cases b with
        | none => exact hCross.1 i r
        | some j => rfl
    · intro a r
      cases a with
      | none => exact hRootU r
      | some i => rfl
    · intro a r
      cases a with
      | none => exact hRootD r
      | some i => rfl
  · intro a b
    cases a with
    | none =>
      cases b with
      | none =>
        exact (A.partialTypeAt_no_typeE_loop d v).trans
          (A.partialTypeAt_no_typeE_loop d w).symm
      | some j =>
        exact (A.partialTypeAt_no_reverseE d v hv j).trans
          (A.partialTypeAt_no_reverseE d w hw j).symm
    | some i =>
      cases b with
      | none =>
        exact (A.partialTypeAt_fullESocle d v hv i).trans
          (A.partialTypeAt_fullESocle d w hw i).symm
      | some j => rfl

/-- The converse is direct, but important: equality of the COMPLETE
records reflects every positive and negative binary bit in both
orientations at all coordinates of their common socle. -/
theorem sameAmbient_cross_of_partialType_eq
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (v w d : Nat)
    (hEq : A.partialTypeAt d v = A.partialTypeAt d w) :
    SameAmbientCrossType A v w d := by
  constructor
  · intro i r
    have h := congrArg
      (fun T : PartialTypeWithE d db du dd =>
        T.lReduct.binary (some i) none r) hEq
    exact h
  · intro i r
    have h := congrArg
      (fun T : PartialTypeWithE d db du dd =>
        T.lReduct.binary none (some i) r) hEq
    exact h

/-- The exact iff used to transport the H binary trace calculation
to equality of genuine full induced types over a shared ambient C+. -/
theorem sameAmbient_partialType_eq_iff_cross
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (v w d : Nat)
    (hv : d ≤ A.freeLevel v) (hw : d ≤ A.freeLevel w)
    (hRoot : A.partialTypeAt 0 v = A.partialTypeAt 0 w) :
    A.partialTypeAt d v = A.partialTypeAt d w ↔
      SameAmbientCrossType A v w d := by
  constructor
  · exact sameAmbient_cross_of_partialType_eq A v w d
  · exact sameAmbient_partialType_eq_of_cross A v w d hv hw hRoot

/-- The first different complete binary pair at coordinate d is also
the FIRST difference of the full L+ partial types: predecessors
through d coincide, and the predecessors through d+1 differ.

The positive free-level bounds are essential. Without them the two
E-socles could differ before the first binary disagreement. -/
theorem sameAmbient_first_fullType_difference
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (v w d : Nat)
    (hv : d + 1 ≤ A.freeLevel v)
    (hw : d + 1 ≤ A.freeLevel w)
    (hRoot : A.partialTypeAt 0 v = A.partialTypeAt 0 w)
    (hBefore : SameAmbientCrossType A v w d)
    (hDiff :
      (∃ r : Fin db, A.L.binary d v r ≠ A.L.binary d w r) ∨
      (∃ r : Fin db, A.L.binary v d r ≠ A.L.binary w d r)) :
    A.partialTypeAt d v = A.partialTypeAt d w ∧
      A.partialTypeAt (d + 1) v ≠ A.partialTypeAt (d + 1) w := by
  have hprev : A.partialTypeAt d v = A.partialTypeAt d w :=
    (sameAmbient_partialType_eq_iff_cross A v w d
      (by omega) (by omega) hRoot).2 hBefore
  refine ⟨hprev, ?_⟩
  intro heq
  have hCross :=
    (sameAmbient_partialType_eq_iff_cross A v w (d + 1)
      hv hw hRoot).1 heq
  let newVertex : Fin (d + 1) := ⟨d, by omega⟩
  rcases hDiff with ⟨r, hne⟩ | ⟨r, hne⟩
  · exact hne (hCross.1 newVertex r)
  · exact hne (hCross.2 newVertex r)

end SuccessorTree.V10

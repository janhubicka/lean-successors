import SuccessorTree.V10.ParameterLetterUniqueness
import SuccessorTree.V10.CanonicalCrossing
import Mathlib.Tactic

/-!
# S2 uniqueness for successor records extracted from genuine partial structures

The conditional uniqueness theorem in ParameterLetterUniqueness uses
the E-cut and no-new-tuples hypotheses explicitly. In this module
we DISCHARGE those hypotheses for an arbitrary actual L+ partial type
extracted from an enumerated partial structure A.

Given two level-(ell+1) types extracted from possibly different
partial structures, equality of their old predecessor records,
their new vertex free levels, the actual new ordinary vertex
parameter types and their terminal Sigma letters forces the
entire successor types to be equal.

This is a substantive S2 uniqueness result for actual
witness-generated covers. The still-unverified interface is to
show that every output of the manuscript's *forward* S is
represented by this canonical decomposition and conversely that
every admissible cover is that S output (S3).
-/

namespace SuccessorTree.V10

/-- Every actual one-level partial-type extension satisfies the
free E-cut and complete no-new-tuples conditions at its last
ordinary vertex. No additional crossing axiom is assumed. -/
theorem validNewColumn_of_extracted_partialType
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v ell : Nat) (hv : v < A.size)
    (hCut : ell + 1 ≤ A.freeLevel v) :
    ValidNewOrdinaryColumn
      (A.partialTypeAt (ell + 1) v)
      (A.freeLevel ell) := by
  have hEllSize : ell < A.size := by
    have hvfl := A.freeLevel_le v
    omega
  refine
    { oldToNewE := ?_
      newToOldE := ?_
      noNewBinaryBeyondCut := ?_ }
  · intro i
    change A.E i.val ell = decide (i.val < A.freeLevel ell)
    exact E_eq_decide_freeLevel A i.val ell
  · intro i
    change A.E ell i.val = false
    cases he : A.E ell i.val with
    | false => rfl
    | true =>
        have hSpacing := A.spaced ell i.val he
        omega
  · intro i hi r
    change A.L.binary i.val ell r = false ∧
      A.L.binary ell i.val r = false
    exact binary_false_at_or_above_freeLevel A
      i.val ell i.isLt
      (lt_trans i.isLt hEllSize) hEllSize hi r

/-- The actual S2 uniqueness statement for two represented covers:
all complete L+ atoms are fixed by the old predecessor, the
unique free E cut of the freshly inserted vertex, its genuine
shortened parameter and the two-vertex terminal Sigma letter. -/
theorem extracted_successor_unique_of_canonical_decomposition
    {db du dd : Nat}
    (A B : EnumeratedPartialStructure db du dd)
    (v w ell : Nat)
    (hv : v < A.size) (hw : w < B.size)
    (hCutA : ell + 1 ≤ A.freeLevel v)
    (hCutB : ell + 1 ≤ B.freeLevel w)
    (hFree : A.freeLevel ell = B.freeLevel ell)
    (hOld :
      (A.partialTypeAt (ell + 1) v).restrict
          (Nat.le_succ ell) =
        (B.partialTypeAt (ell + 1) w).restrict
          (Nat.le_succ ell))
    (hParameter :
      A.partialTypeAt (A.freeLevel ell) ell =
        B.partialTypeAt (A.freeLevel ell) ell)
    (hLetter :
      (A.partialTypeAt (ell + 1) v).terminalLetter =
        (B.partialTypeAt (ell + 1) w).terminalLetter) :
    A.partialTypeAt (ell + 1) v =
      B.partialTypeAt (ell + 1) w := by
  let f := A.freeLevel ell
  have hf : f ≤ ell := A.freeLevel_le ell
  have hVA : ValidNewOrdinaryColumn
      (A.partialTypeAt (ell + 1) v) f := by
    exact validNewColumn_of_extracted_partialType A v ell hv hCutA
  have hVB : ValidNewOrdinaryColumn
      (B.partialTypeAt (ell + 1) w) f := by
    change ValidNewOrdinaryColumn
      (B.partialTypeAt (ell + 1) w) (A.freeLevel ell)
    rw [hFree]
    exact validNewColumn_of_extracted_partialType B w ell hw hCutB
  have hParam :
      (A.partialTypeAt (ell + 1) v).lastOrdinaryParameter f hf =
        (B.partialTypeAt (ell + 1) w).lastOrdinaryParameter f hf := by
    calc
      (A.partialTypeAt (ell + 1) v).lastOrdinaryParameter f hf =
        A.partialTypeAt f ell :=
          partialTypeAt_lastOrdinaryParameter A v ell f hf
      _ = B.partialTypeAt f ell := hParameter
      _ = (B.partialTypeAt (ell + 1) w).lastOrdinaryParameter f hf :=
        (partialTypeAt_lastOrdinaryParameter B w ell f hf).symm
  exact complete_successor_unique_of_canonical_inputs
    (A.partialTypeAt (ell + 1) v)
    (B.partialTypeAt (ell + 1) w)
    f hf hOld hVA hVB hParam hLetter

end SuccessorTree.V10

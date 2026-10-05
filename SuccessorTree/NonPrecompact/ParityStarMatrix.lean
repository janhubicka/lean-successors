import Mathlib
import SuccessorTree.NonPrecompact.AffineParity

/-!
# A binary matrix with prescribed row and column parities

Given finite nonempty row and column index types, and prescribed F₂ row
and column sums with equal total sum, we construct an explicit matrix with
those marginals.  The construction is a star through distinguished row and
column indices.

This is the finite parity gadget used by the atom-coordinate pre-BANANA
amalgam.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators Matrix

/-- Explicit star matrix with prescribed marginals, before imposing the
compatibility of the two total sums. -/
def parityStarMatrix
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    [Fintype I] [Fintype J]
    (row : I → F2) (col : J → F2)
    (i0 : I) (j0 : J) :
    Matrix I J F2 :=
  fun i j =>
    if hi : i = i0 then
      if hj : j = j0 then
        row i0 + ∑ j' ∈ (Finset.univ : Finset J).erase j0, col j'
      else
        col j
    else
      if hj : j = j0 then row i else 0

/-- Every row of the star matrix has the prescribed row sum. -/
theorem sum_row_parityStarMatrix
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    [Fintype I] [Fintype J]
    (row : I → F2) (col : J → F2)
    (i0 : I) (j0 : J) (i : I) :
    (∑ j, parityStarMatrix row col i0 j0 i j) = row i := by
  by_cases hi : i = i0
  · subst i
    let C : F2 := ∑ j ∈ (Finset.univ : Finset J).erase j0, col j
    rw [← Finset.sum_erase_add
      (Finset.univ : Finset J)
      (fun j => parityStarMatrix row col i0 j0 i0 j)
      (by simp)]
    have hsum :
        (∑ j ∈ (Finset.univ : Finset J).erase j0,
            parityStarMatrix row col i0 j0 i0 j) = C := by
      dsimp [C]
      apply Finset.sum_congr rfl
      intro j hj
      have hj0 : j ≠ j0 := (Finset.mem_erase.mp hj).1
      simp [parityStarMatrix, hj0]
    have hcenter :
        parityStarMatrix row col i0 j0 i0 j0 = row i0 + C := by
      simp [parityStarMatrix, C]
    rw [hsum, hcenter]
    calc
      C + (row i0 + C) = row i0 + (C + C) := by abel
      _ = row i0 := by
        rw [CharTwo.add_self_eq_zero, add_zero]
  · rw [← Finset.sum_erase_add
      (Finset.univ : Finset J)
      (fun j => parityStarMatrix row col i0 j0 i j)
      (by simp)]
    have hzero :
        (∑ j ∈ (Finset.univ : Finset J).erase j0,
            parityStarMatrix row col i0 j0 i j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj0 : j ≠ j0 := (Finset.mem_erase.mp hj).1
      simp [parityStarMatrix, hi, hj0]
    rw [hzero]
    simp [parityStarMatrix, hi]

/-- If the prescribed row and column totals agree, every column of the star
matrix has the prescribed column sum. -/
theorem sum_col_parityStarMatrix
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    [Fintype I] [Fintype J]
    (row : I → F2) (col : J → F2)
    (i0 : I) (j0 : J)
    (htotal : (∑ i, row i) = ∑ j, col j)
    (j : J) :
    (∑ i, parityStarMatrix row col i0 j0 i j) = col j := by
  by_cases hj : j = j0
  · subst j
    let R : F2 := ∑ i ∈ (Finset.univ : Finset I).erase i0, row i
    let C : F2 := ∑ j ∈ (Finset.univ : Finset J).erase j0, col j
    have htot' : R + row i0 = C + col j0 := by
      dsimp [R, C]
      calc
        (∑ i ∈ (Finset.univ : Finset I).erase i0, row i) + row i0 =
            ∑ i, row i := Finset.sum_erase_add _ _ (by simp)
        _ = ∑ j, col j := htotal
        _ = (∑ j ∈ (Finset.univ : Finset J).erase j0, col j) + col j0 :=
          (Finset.sum_erase_add _ _ (by simp)).symm
    rw [← Finset.sum_erase_add
      (Finset.univ : Finset I)
      (fun i => parityStarMatrix row col i0 j0 i j0)
      (by simp)]
    have hrest :
        (∑ i ∈ (Finset.univ : Finset I).erase i0,
            parityStarMatrix row col i0 j0 i j0) = R := by
      dsimp [R]
      apply Finset.sum_congr rfl
      intro i hi
      have hi0 : i ≠ i0 := (Finset.mem_erase.mp hi).1
      simp [parityStarMatrix, hi0]
    rw [hrest]
    have hcenter :
        parityStarMatrix row col i0 j0 i0 j0 = row i0 + C := by
      simp [parityStarMatrix, C]
    rw [hcenter]
    calc
      R + (row i0 + C) = (R + row i0) + C := by abel
      _ = (C + col j0) + C := by rw [htot']
      _ = col j0 := by
        rw [show (C + col j0) + C = col j0 + (C + C) by abel]
        rw [CharTwo.add_self_eq_zero, add_zero]
  · rw [← Finset.sum_erase_add
      (Finset.univ : Finset I)
      (fun i => parityStarMatrix row col i0 j0 i j)
      (by simp)]
    have hzero :
        (∑ i ∈ (Finset.univ : Finset I).erase i0,
            parityStarMatrix row col i0 j0 i j) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi0 : i ≠ i0 := (Finset.mem_erase.mp hi).1
      simp [parityStarMatrix, hi0, hj]
    rw [hzero]
    simp [parityStarMatrix, hj]

end SuccessorTree.NonPrecompact

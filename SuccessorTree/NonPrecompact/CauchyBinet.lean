import SuccessorTree.NonPrecompact.AffineParity

/-!
# The Cauchy--Binet aggregate needed by BANANA

Mathlib does not currently expose the rectangular Cauchy--Binet formula
under that name.  For the BANANA residue argument we only need its
full-size aggregate over `F₂`.  We derive exactly that statement from
Sylvester's determinant identity together with the formula for the
coefficients of `det (1 + X M)` as sums of principal minors.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators Matrix
open Polynomial

/-- Reindexing a principal minor by the canonical increasing
enumeration of its finite index set preserves its determinant. -/
theorem det_principal_submatrix_eq_orderEmb
    {n d : ℕ} (M : Matrix (Fin n) (Fin n) F2)
    (s : Finset (Fin n)) (hs : s.card = d) :
    (M.submatrix
        (Subtype.val : s → Fin n)
        (Subtype.val : s → Fin n)).det =
      (M.submatrix
        (s.orderEmbOfFin hs)
        (s.orderEmbOfFin hs)).det := by
  let e := (s.orderIsoOfFin hs).toEquiv
  have h :=
    Matrix.det_submatrix_equiv_self e
      (M.submatrix
        (Subtype.val : s → Fin n)
        (Subtype.val : s → Fin n))
  have hmat :
      (M.submatrix
          (Subtype.val : s → Fin n)
          (Subtype.val : s → Fin n)).submatrix e e =
        M.submatrix (s.orderEmbOfFin hs) (s.orderEmbOfFin hs) := by
    ext i j
    rfl
  calc
    (M.submatrix
        (Subtype.val : s → Fin n)
        (Subtype.val : s → Fin n)).det =
        ((M.submatrix
          (Subtype.val : s → Fin n)
          (Subtype.val : s → Fin n)).submatrix e e).det := h.symm
    _ = (M.submatrix
        (s.orderEmbOfFin hs)
        (s.orderEmbOfFin hs)).det := by rw [hmat]

/-- Characteristic-two Cauchy--Binet aggregate.

If `A Bᵀ = I_d`, then the sum of the `d × d` principal minors of
`Bᵀ A` is one.  This is the form of Cauchy--Binet used in the
bilinear residue count. -/
theorem sum_principal_minors_transpose_mul_eq_one
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (hAB : A * Bᵀ = 1) :
    (∑ s ∈ Finset.univ.powersetCard d,
      ((Bᵀ * A).submatrix
        (Subtype.val : s → Fin n)
        (Subtype.val : s → Fin n)).det) = 1 := by
  let C : F2 →+* F2[X] := Polynomial.C
  have hABp :
      A.map C * (Bᵀ).map C =
        (1 : Matrix (Fin d) (Fin d) F2[X]) := by
    have h :=
      congrArg (fun M : Matrix (Fin d) (Fin d) F2 => M.map C) hAB
    simpa [Matrix.map_mul, C] using h
  have hsyl :=
    Matrix.det_one_add_mul_comm
      ((X : F2[X]) • A.map C) ((Bᵀ).map C)
  rw [Matrix.smul_mul, hABp, Matrix.mul_smul, ← Matrix.map_mul] at hsyl
  have hdiag :
      Matrix.det
        (1 + (X : F2[X]) • (1 : Matrix (Fin d) (Fin d) F2[X])) =
        (1 + X) ^ d := by
    have hm :
        (1 + (X : F2[X]) • (1 : Matrix (Fin d) (Fin d) F2[X])) =
          Matrix.diagonal (fun _ : Fin d => 1 + X) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    rw [hm, Matrix.det_diagonal]
    simp
  have hpoly :
      Matrix.det
          (1 + (X : F2[X]) • (Bᵀ * A).map C) =
        (1 + X) ^ d := by
    calc
      Matrix.det
          (1 + (X : F2[X]) • (Bᵀ * A).map C) =
          Matrix.det
            (1 + (X : F2[X]) •
              (1 : Matrix (Fin d) (Fin d) F2[X])) := hsyl.symm
      _ = (1 + X) ^ d := hdiag
  rw [← Matrix.coeff_det_one_add_X_smul_eq_sum_minors (Bᵀ * A) d]
  rw [hpoly, Polynomial.coeff_one_add_X_pow]
  simp

end SuccessorTree.NonPrecompact

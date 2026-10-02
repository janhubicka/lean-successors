import SuccessorTree.NonPrecompact.BilinearResidue

/-!
# Affine slices of perfect BANANA pairs

The BANANA persistence argument restricts a perfect pair of dimension
`d+1` to vectors whose last coordinate is one.  On the remaining
`d` coordinates the ambient coordinate functions become affine.
This file packages the corresponding matrix reduction.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- The first `d` rows of a `(d+1) × n` matrix. -/
abbrev frontRows {d n : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin n) F2) :
    Matrix (Fin d) (Fin n) F2 :=
  A.submatrix Fin.castSucc id

/-- The last row, viewed as the affine offset after fixing the last
coordinate to one. -/
def lastOffset {d n : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin n) F2) :
    Fin n → F2 :=
  fun j => A (Fin.last d) j

/-- A left-inverse identity for a perfect pair survives after deleting
the last row from both matrices. -/
theorem frontRows_mul_transpose_eq_one
    {d n : ℕ}
    (A B : Matrix (Fin (d + 1)) (Fin n) F2)
    (hAB : A * Bᵀ = 1) :
    frontRows A * (frontRows B)ᵀ = 1 := by
  calc
    frontRows A * (frontRows B)ᵀ =
        (A * Bᵀ).submatrix Fin.castSucc Fin.castSucc := by
      simpa [frontRows, Matrix.transpose_submatrix] using
        (Matrix.submatrix_mul A Bᵀ
          (Fin.castSucc : Fin d → Fin (d + 1))
          (id : Fin n → Fin n)
          (Fin.castSucc : Fin d → Fin (d + 1))
          Function.bijective_id).symm
    _ = 1 := by
      rw [hAB]
      exact Matrix.submatrix_one _ (Fin.castSucc_injective d)

/-- The affine-slice form used for the even and odd one-atom BANANA
sources.  Every residue is realised on the slice where the deleted last
coordinate is fixed to one. -/
theorem exists_affineSlice_bilinearWeight_eq_residue
    (k : ℕ) {d n : ℕ}
    (hd : d = 2 ^ (k + 1) - 1)
    (A B : Matrix (Fin (d + 1)) (Fin n) F2)
    (hAB : A * Bᵀ = 1)
    (r : ZMod (2 ^ (k + 1))) :
    ∃ u v : Fin d → F2,
      (bilinearWeight
          (frontRows A) (frontRows B)
          (lastOffset A) (lastOffset B) u v :
        ZMod (2 ^ (k + 1))) = r := by
  subst d
  exact exists_bilinearWeight_eq_residue
    k (frontRows A) (frontRows B)
      (lastOffset A) (lastOffset B)
      (frontRows_mul_transpose_eq_one A B hAB) r


/-- Append a final coordinate equal to one. -/
def snocOne {d : ℕ} (u : Fin d → F2) : Fin (d + 1) → F2 :=
  Fin.snoc u 1

@[simp] theorem snocOne_castSucc
    {d : ℕ} (u : Fin d → F2) (i : Fin d) :
    snocOne u i.castSucc = u i := by
  simp [snocOne]

@[simp] theorem snocOne_last
    {d : ℕ} (u : Fin d → F2) :
    snocOne u (Fin.last d) = 1 := by
  simp [snocOne]

theorem snocOne_ne_zero
    {d : ℕ} (u : Fin d → F2) :
    snocOne u ≠ 0 := by
  intro h
  have hlast := congrFun h (Fin.last d)
  simpa using hlast

/-- Restricting a full linear coordinate function to the last-coordinate-one
slice gives the corresponding affine coordinate function. -/
theorem affineBit_frontRows_lastOffset
    {d n : ℕ}
    (A : Matrix (Fin (d + 1)) (Fin n) F2)
    (i : Fin n) (u : Fin d → F2) :
    affineBit (frontRows A) (lastOffset A) i u =
      affineBit A (0 : Fin n → F2) i (snocOne u) := by
  classical
  simp [affineBit, frontRows, lastOffset, snocOne, dotProduct,
    Fin.sum_univ_castSucc]

/-- The ordinary support-intersection weight is unchanged when the
last-coordinate-one slice is rewritten using affine coordinate functions. -/
theorem bilinearWeight_frontRows_lastOffset
    {d n : ℕ}
    (A B : Matrix (Fin (d + 1)) (Fin n) F2)
    (u v : Fin d → F2) :
    bilinearWeight
        (frontRows A) (frontRows B)
        (lastOffset A) (lastOffset B) u v =
      bilinearWeight A B
        (0 : Fin n → F2) (0 : Fin n → F2)
        (snocOne u) (snocOne v) := by
  classical
  unfold bilinearWeight
  apply Finset.sum_congr rfl
  intro i hi
  simp only [pairBit, affineBit_frontRows_lastOffset]


/-- Modulo two, the ordinary support-intersection weight of a perfect pair
is exactly the preserved bilinear pairing. -/
theorem natCast_bilinearWeight_eq_dotProduct
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (hAB : A * Bᵀ = 1)
    (x y : Fin d → F2) :
    (bilinearWeight A B
        (0 : Fin n → F2) (0 : Fin n → F2) x y : F2) =
      x ⬝ᵥ y := by
  classical
  unfold bilinearWeight pairBit affineBit
  rw [Nat.cast_sum]
  simp_rw [ZMod.natCast_zmod_val]
  simp only [Pi.zero_apply, add_zero]
  change (Aᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ y) = x ⬝ᵥ y
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, hAB, Matrix.vecMul_one]

/-- Matrix-level form of the second half of the BANANA persistent-colouring
argument: in a perfect pair of dimension `q`, every residue modulo
`q = 2^(k+1)` is realised by two nonzero vectors. -/
theorem exists_nonzero_full_bilinearWeight_eq_residue
    (k : ℕ) {d n : ℕ}
    (hd : d = 2 ^ (k + 1) - 1)
    (A B : Matrix (Fin (d + 1)) (Fin n) F2)
    (hAB : A * Bᵀ = 1)
    (r : ZMod (2 ^ (k + 1))) :
    ∃ x y : Fin (d + 1) → F2,
      x ≠ 0 ∧ y ≠ 0 ∧
        (bilinearWeight A B
            (0 : Fin n → F2) (0 : Fin n → F2) x y :
          ZMod (2 ^ (k + 1))) = r := by
  obtain ⟨u, v, huv⟩ :=
    exists_affineSlice_bilinearWeight_eq_residue k hd A B hAB r
  refine ⟨snocOne u, snocOne v,
    snocOne_ne_zero u, snocOne_ne_zero v, ?_⟩
  rw [← bilinearWeight_frontRows_lastOffset]
  exact huv

/-- Every dyadic residue is realised on the last-coordinate-one slice by
nonzero vectors, and the pairing of those vectors is exactly the reduction
of that residue modulo two. -/
theorem exists_nonzero_full_bilinearWeight_eq_residue_with_pairing
    (k : ℕ) {d n : ℕ}
    (hd : d = 2 ^ (k + 1) - 1)
    (A B : Matrix (Fin (d + 1)) (Fin n) F2)
    (hAB : A * Bᵀ = 1)
    (r : ZMod (2 ^ (k + 1))) :
    ∃ x y : Fin (d + 1) → F2,
      x ≠ 0 ∧ y ≠ 0 ∧
        (bilinearWeight A B
            (0 : Fin n → F2) (0 : Fin n → F2) x y :
          ZMod (2 ^ (k + 1))) = r ∧
        x ⬝ᵥ y = (ZMod.cast r : F2) := by
  obtain ⟨x, y, hx, hy, hres⟩ :=
    exists_nonzero_full_bilinearWeight_eq_residue k hd A B hAB r
  refine ⟨x, y, hx, hy, hres, ?_⟩
  have htwo : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (by omega)
  have hcast :=
    congrArg (fun z : ZMod (2 ^ (k + 1)) => (ZMod.cast z : F2)) hres
  rw [ZMod.cast_natCast htwo] at hcast
  calc
    x ⬝ᵥ y =
        (bilinearWeight A B
            (0 : Fin n → F2) (0 : Fin n → F2) x y : F2) :=
      (natCast_bilinearWeight_eq_dotProduct A B hAB x y).symm
    _ = (ZMod.cast r : F2) := hcast


end SuccessorTree.NonPrecompact

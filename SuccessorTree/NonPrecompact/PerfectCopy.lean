import SuccessorTree.NonPrecompact.ColouringWrappers

/-!
# Coordinate interfaces for perfect BANANA target copies

A coordinate embedding of the perfect pairing B_d into B_n is represented
by two d x n matrices P,Q with P Qᵀ = I_d. This file packages that
representation as an actual pair of injective linear maps and proves the
pairing-preservation statement used by the manuscript.

The persistent-colouring wrappers can then be stated directly as assertions
about such coordinate target copies.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators Matrix

/-- Matrix data for a coordinate copy of the perfect pairing B_d
inside B_n. -/
structure PerfectCopyMatrices (d n : ℕ) where
  left : Matrix (Fin d) (Fin n) F2
  right : Matrix (Fin d) (Fin n) F2
  pairing : left * rightᵀ = 1

namespace PerfectCopyMatrices

variable {d n : ℕ} (E : PerfectCopyMatrices d n)

/-- The induced map on the left sort. -/
def leftMap : (Fin d → F2) →ₗ[F2] (Fin n → F2) :=
  E.leftᵀ.mulVecLin

/-- The induced map on the right sort. -/
def rightMap : (Fin d → F2) →ₗ[F2] (Fin n → F2) :=
  E.rightᵀ.mulVecLin

@[simp] theorem leftMap_apply (x : Fin d → F2) :
    E.leftMap x = E.leftᵀ *ᵥ x := by
  rfl

@[simp] theorem rightMap_apply (y : Fin d → F2) :
    E.rightMap y = E.rightᵀ *ᵥ y := by
  rfl

/-- Transposing P Qᵀ = I gives the left inverse needed for the
left-sort coordinate map. -/
theorem right_mul_left_transpose :
    E.right * E.leftᵀ = 1 := by
  have h := congrArg Matrix.transpose E.pairing
  simpa using h

theorem leftMap_injective : Function.Injective E.leftMap := by
  intro x y hxy
  change E.leftᵀ *ᵥ x = E.leftᵀ *ᵥ y at hxy
  have h :=
    congrArg (fun z : Fin n → F2 => E.right *ᵥ z) hxy
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    E.right_mul_left_transpose, Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

theorem rightMap_injective : Function.Injective E.rightMap := by
  intro x y hxy
  change E.rightᵀ *ᵥ x = E.rightᵀ *ᵥ y at hxy
  have h :=
    congrArg (fun z : Fin n → F2 => E.left *ᵥ z) hxy
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    E.pairing, Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

/-- The coordinate maps preserve the perfect pairing. -/
theorem pairing_apply (x y : Fin d → F2) :
    E.leftMap x ⬝ᵥ E.rightMap y = x ⬝ᵥ y := by
  change (E.leftᵀ *ᵥ x) ⬝ᵥ (E.rightᵀ *ᵥ y) = x ⬝ᵥ y
  calc
    (E.leftᵀ *ᵥ x) ⬝ᵥ (E.rightᵀ *ᵥ y) =
        (E.rightᵀ *ᵥ y) ⬝ᵥ (E.leftᵀ *ᵥ x) := dotProduct_comm _ _
    _ = x ⬝ᵥ E.left *ᵥ (E.rightᵀ *ᵥ y) :=
      Matrix.dotProduct_transpose_mulVec E.left (E.rightᵀ *ᵥ y) x
    _ = x ⬝ᵥ (E.left * E.rightᵀ) *ᵥ y := by
      rw [Matrix.mulVec_mulVec]
    _ = x ⬝ᵥ y := by
      rw [E.pairing, Matrix.one_mulVec]

/-- The ordinary coordinate intersection count of the two images.

For vectors regarded as subsets of the ambient coordinate set, this is
exactly the cardinality of their intersection. -/
noncomputable def intersectionCount (x y : Fin d → F2) : ℕ :=
  bilinearWeight E.left E.right
    (0 : Fin n → F2) (0 : Fin n → F2) x y

/-- Ordinary coordinate-support intersection count in the ambient perfect pair. -/
noncomputable def ambientIntersectionCount
    {n : ℕ} (X Y : Fin n → F2) : ℕ :=
  ∑ i : Fin n, (X i * Y i).val

/-- The matrix weight is literally the support-intersection count of the
two image vectors in the ambient coordinate perfect pair. -/
theorem intersectionCount_eq_ambientIntersectionCount
    (x y : Fin d → F2) :
    E.intersectionCount x y =
      ambientIntersectionCount (E.leftMap x) (E.rightMap y) := by
  classical
  unfold intersectionCount ambientIntersectionCount bilinearWeight pairBit affineBit
  simp only [Pi.zero_apply, add_zero, leftMap_apply, rightMap_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change
    (E.leftᵀ i ⬝ᵥ x * E.rightᵀ i ⬝ᵥ y).val =
      ((E.leftᵀ *ᵥ x) i * (E.rightᵀ *ᵥ y) i).val
  rfl

theorem leftMap_ne_zero {x : Fin d → F2} (hx : x ≠ 0) :
    E.leftMap x ≠ 0 := by
  intro h
  apply hx
  apply E.leftMap_injective
  simpa using h

theorem rightMap_ne_zero {y : Fin d → F2} (hy : y ≠ 0) :
    E.rightMap y ≠ 0 := by
  intro h
  apply hy
  apply E.rightMap_injective
  simpa using h

/-- The colour has the parity required by the source pairing. -/
theorem intersectionCount_parity (x y : Fin d → F2) :
    (E.intersectionCount x y : F2) = x ⬝ᵥ y :=
  bilinearWeight_natCast_f2_eq_dotProduct
    E.left E.right E.pairing x y

/-- A source pair represents a copy of the four-element line-pair
structure A_b. -/
def IsLinePair (b : F2) (x y : Fin d → F2) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ x ⬝ᵥ y = b

/-- Pairing-one source: a B_(q-1) target copy sees every odd
intersection colour. -/
theorem exists_pairingOne_intersectionColour
    (k : ℕ)
    (E : PerfectCopyMatrices (2 ^ (k + 1) - 1) n)
    (r : ℕ) (hr : Odd r) :
    ∃ x y : Fin (2 ^ (k + 1) - 1) → F2,
      IsLinePair 1 x y ∧
      (E.intersectionCount x y : ZMod (2 ^ (k + 1))) =
        (r : ZMod (2 ^ (k + 1))) := by
  obtain ⟨x, y, hx, hy, hpair, hcolour⟩ :=
    exists_pairing_one_bilinearWeight_eq_odd_residue
      k E.left E.right E.pairing r hr
  exact ⟨x, y, ⟨hx, hy, hpair⟩, hcolour⟩

/-- Full affine-slice target: every residue is realised by a line pair whose
pairing is exactly the residue parity. -/
theorem exists_intersectionColour
    (k : ℕ)
    (E :
      PerfectCopyMatrices ((2 ^ (k + 1) - 1) + 1) n)
    (r : ZMod (2 ^ (k + 1))) :
    ∃ x y : Fin ((2 ^ (k + 1) - 1) + 1) → F2,
      IsLinePair (residueParityHom k r) x y ∧
      (E.intersectionCount x y : ZMod (2 ^ (k + 1))) = r := by
  obtain ⟨x, y, hx, hy, hpair, hcolour⟩ :=
    exists_nonzero_pair_of_residue
      k E.left E.right E.pairing r
  exact ⟨x, y, ⟨hx, hy, hpair⟩, hcolour⟩

/-- Ambient-vector form of the full BANANA target-copy wrapper.

Every residue is realised by two nonzero vectors in the ambient coordinate
perfect pair; their ambient pairing is the parity of the residue, and their
ordinary support-intersection count has the prescribed residue. -/
theorem exists_ambient_intersectionColour
    (k : ℕ)
    (E : PerfectCopyMatrices ((2 ^ (k + 1) - 1) + 1) n)
    (r : ZMod (2 ^ (k + 1))) :
    ∃ X Y : Fin n → F2,
      X ≠ 0 ∧ Y ≠ 0 ∧
      X ⬝ᵥ Y = residueParityHom k r ∧
      (ambientIntersectionCount X Y : ZMod (2 ^ (k + 1))) = r := by
  obtain ⟨x, y, hline, hcolour⟩ :=
    E.exists_intersectionColour k r
  refine ⟨E.leftMap x, E.rightMap y,
    E.leftMap_ne_zero hline.1,
    E.rightMap_ne_zero hline.2.1, ?_, ?_⟩
  · exact (E.pairing_apply x y).trans hline.2.2
  · rw [← E.intersectionCount_eq_ambientIntersectionCount x y]
    exact hcolour

end PerfectCopyMatrices

end SuccessorTree.NonPrecompact

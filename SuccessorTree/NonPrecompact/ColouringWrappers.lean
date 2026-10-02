import SuccessorTree.NonPrecompact.BilinearResidue

/-!
# Wrappers matching the persistent-colouring arguments

The lower-bound files formalise the arithmetic and linear-algebraic cores of
the three non-precompact colourings.  This file packages those cores in the
forms used directly in the manuscript proofs.

For pre-BANANA, we record that the selected side and its complement are both
legitimate odd blocks.  For Folkman--BANANA, we record that the selected
ordinary count itself is odd.  For BANANA, we prove the parity identity for
the ordinary intersection count and the affine-slice argument used for the
pairing-zero source.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators Matrix

/-! ## Pre-BANANA and Folkman--BANANA wrappers -/

/-- Pre-BANANA target-copy form.

Besides realising the prescribed odd residue, the chosen subset uses an even
number of the `q - 1` remaining target blocks.  Consequently the block
containing the distinguished atom and its complementary block both contain
an odd number of target blocks; in particular, the complement is nonempty.
The corresponding ordinary marked-atom sums are odd as well. -/
theorem prebanana_odd_residue_copy_witness
    {k : ℕ} (hk : 0 < k) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℕ)
    (hcard : s.card + 1 = 2 ^ k)
    (ha : ∀ i ∈ s, Odd (a i))
    (c r : ℕ) (hc : Odd c) (hr : Odd r) :
    ∃ t : Finset ι,
      t ⊆ s ∧
      Even t.card ∧
      Odd (t.card + 1) ∧
      Odd (s \ t).card ∧
      (s \ t).Nonempty ∧
      Odd (c + ∑ i ∈ t, a i) ∧
      Odd (∑ i ∈ s \ t, a i) ∧
      (c : ZMod (2 ^ k)) + ∑ i ∈ t, (a i : ZMod (2 ^ k)) =
        (r : ZMod (2 ^ k)) := by
  classical
  obtain ⟨t, ht, hteven, hsum⟩ :=
    prebanana_odd_residue_even_subset
      hk s a hcard ha c r hc hr
  have hqeven : Even (2 ^ k) :=
    even_two.pow_of_ne_zero (Nat.ne_of_gt hk)
  have hsplus : Even (s.card + 1) := by
    rw [hcard]
    exact hqeven
  have hsodd : Odd s.card := by
    rw [Nat.even_add_one, Nat.not_even_iff_odd] at hsplus
    exact hsplus
  have hchosenCard : Odd (t.card + 1) := hteven.add_one
  have hdiffCard : Odd (s \ t).card := by
    rw [Finset.card_sdiff_of_subset ht]
    exact Nat.Odd.sub_even (Finset.card_le_card ht) hsodd hteven
  have hdiffNonempty : (s \ t).Nonempty :=
    Finset.card_pos.mp hdiffCard.pos
  have htSumEven : Even (∑ i ∈ t, a i) := by
    rw [Finset.even_sum_iff_even_card_odd]
    have hfilter :
        t.filter (fun i => Odd (a i)) = t := by
      apply Finset.filter_eq_self.2
      intro i hi
      exact ha i (ht hi)
    rw [hfilter]
    exact hteven
  have hchosenSum : Odd (c + ∑ i ∈ t, a i) :=
    hc.add_even htSumEven
  have hdiffSum : Odd (∑ i ∈ s \ t, a i) := by
    rw [Finset.odd_sum_iff_odd_card_odd]
    have hfilter :
        (s \ t).filter (fun i => Odd (a i)) = s \ t := by
      apply Finset.filter_eq_self.2
      intro i hi
      exact ha i ((Finset.mem_sdiff.mp hi).1)
    rw [hfilter]
    exact hdiffCard
  exact ⟨t, ht, hteven, hchosenCard, hdiffCard, hdiffNonempty,
    hchosenSum, hdiffSum, hsum⟩

/-- Folkman--BANANA target-copy form.

The subset supplied by the subset-sum argument is nonempty, and its ordinary
integer count is itself odd.  These are precisely the two conditions needed
for the resulting left vector to be nonzero and to pair to one with the
chosen right vector. -/
theorem folkman_odd_residue_copy_witness
    {k : ℕ} (hk : 0 < k) {ι : Type*}
    (s : Finset ι) (a : ι → ℕ)
    (hcard : s.card + 1 = 2 ^ k)
    (ha : ∀ i ∈ s, Odd (a i))
    (r : ℕ) (hr : Odd r) :
    ∃ t : Finset ι,
      t ⊆ s ∧
      t.Nonempty ∧
      Odd (∑ i ∈ t, a i) ∧
      (∑ i ∈ t, (a i : ZMod (2 ^ k))) = (r : ZMod (2 ^ k)) := by
  obtain ⟨t, ht, htne, hsum⟩ :=
    folkman_odd_residue hk s a hcard ha r hr
  have htwo : 2 ∣ 2 ^ k :=
    dvd_pow_self 2 (Nat.ne_of_gt hk)
  let red : ZMod (2 ^ k) →+* ZMod 2 :=
    ZMod.castHom htwo (ZMod 2)
  have hpar0 := congrArg red hsum
  have hpar :
      (∑ i ∈ t, (a i : ZMod 2)) = (r : ZMod 2) := by
    simpa [red] using hpar0
  have hr2 : (r : ZMod 2) = 1 := hr.natCast_zmod_two
  have hsum2 :
      ((∑ i ∈ t, a i : ℕ) : ZMod 2) = 1 := by
    rw [Nat.cast_sum]
    simpa [hr2] using hpar
  have hodd : Odd (∑ i ∈ t, a i) :=
    ZMod.natCast_eq_one_iff_odd.mp hsum2
  exact ⟨t, ht, htne, hodd, hsum⟩

/-! ## BANANA wrappers -/

/-- The ordinary bilinear weight has parity equal to the preserved pairing.

This is the matrix form of the manuscript sentence
`F(x,y) ≡ x · y (mod 2)`. -/
theorem bilinearWeight_natCast_f2_eq_dotProduct
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (hAB : A * Bᵀ = 1)
    (x y : Fin d → F2) :
    (bilinearWeight A B (0 : Fin n → F2) (0 : Fin n → F2) x y : F2) =
      x ⬝ᵥ y := by
  rw [bilinearWeight, Nat.cast_sum]
  simp_rw [ZMod.natCast_zmod_val]
  simp only [pairBit, affineBit, Pi.zero_apply, add_zero]
  change (Aᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ y) = x ⬝ᵥ y
  calc
    (Aᵀ *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ y) =
        (Bᵀ *ᵥ y) ⬝ᵥ (Aᵀ *ᵥ x) := dotProduct_comm _ _
    _ = x ⬝ᵥ A *ᵥ (Bᵀ *ᵥ y) :=
      Matrix.dotProduct_transpose_mulVec A (Bᵀ *ᵥ y) x
    _ = x ⬝ᵥ (A * Bᵀ) *ᵥ y := by
      rw [Matrix.mulVec_mulVec]
    _ = x ⬝ᵥ y := by
      rw [hAB, Matrix.one_mulVec]

/-- The first `d` rows of a `(d+1) × n` matrix. -/
def initialRows
    {d n : ℕ} (P : Matrix (Fin (d + 1)) (Fin n) F2) :
    Matrix (Fin d) (Fin n) F2 :=
  P.submatrix Fin.castSucc id

/-- The last row of a `(d+1) × n` matrix, used as the affine offset
after fixing the final source coordinate to one. -/
def finalRow
    {d n : ℕ} (P : Matrix (Fin (d + 1)) (Fin n) F2) :
    Fin n → F2 :=
  P (Fin.last d)

/-- Passing to the first `d` rows preserves the perfect-pairing identity. -/
theorem initialRows_mul_transpose_eq_one
    {d n : ℕ}
    (P Q : Matrix (Fin (d + 1)) (Fin n) F2)
    (hPQ : P * Qᵀ = 1) :
    initialRows P * (initialRows Q)ᵀ = 1 := by
  ext i j
  have hij :=
    congrArg
      (fun M : Matrix (Fin (d + 1)) (Fin (d + 1)) F2 =>
        M i.castSucc j.castSucc) hPQ
  simpa [initialRows, Matrix.mul_apply, Matrix.one_apply] using hij

/-- Fixing the last source coordinate to one converts the corresponding
linear coordinate functional into the affine coordinate functional formed
from the initial rows and the last-row offset. -/
theorem affineBit_initialRows_finalRow
    {d n : ℕ}
    (P : Matrix (Fin (d + 1)) (Fin n) F2)
    (i : Fin n) (u : Fin d → F2) :
    affineBit (initialRows P) (finalRow P) i u =
      affineBit P (0 : Fin n → F2) i (Fin.snoc u (1 : F2) : Fin (d + 1) → F2) := by
  change
    (∑ j : Fin d, P j.castSucc i * u j) + P (Fin.last d) i =
      (∑ j : Fin (d + 1), P j i *
        (Fin.snoc u (1 : F2) : Fin (d + 1) → F2) j) + 0
  rw [Fin.sum_univ_castSucc]
  simp

/-- The affine weight on the initial `d` coordinates is exactly the original
linear weight evaluated at vectors whose final coordinate is one. -/
theorem bilinearWeight_initialRows_eq_snoc
    {d n : ℕ}
    (P Q : Matrix (Fin (d + 1)) (Fin n) F2)
    (u v : Fin d → F2) :
    bilinearWeight (initialRows P) (initialRows Q)
        (finalRow P) (finalRow Q) u v =
      bilinearWeight P Q
        (0 : Fin n → F2) (0 : Fin n → F2)
        (Fin.snoc u (1 : F2) : Fin (d + 1) → F2)
        (Fin.snoc v (1 : F2) : Fin (d + 1) → F2) := by
  rw [bilinearWeight, bilinearWeight]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [pairBit]
  rw [affineBit_initialRows_finalRow, affineBit_initialRows_finalRow]

/-- Affine-slice form of the bilinear residue count.

Starting from a perfect `(D+1)`-dimensional target copy, where
`D = q - 1`, every residue is realised by vectors whose last coordinate
is one.  Hence both vectors are automatically nonzero. -/
theorem exists_snoc_bilinearWeight_eq_residue
    (k : ℕ) {n : ℕ}
    (P Q :
      Matrix (Fin ((2 ^ (k + 1) - 1) + 1)) (Fin n) F2)
    (hPQ : P * Qᵀ = 1)
    (r : ZMod (2 ^ (k + 1))) :
    ∃ x y : Fin ((2 ^ (k + 1) - 1) + 1) → F2,
      x (Fin.last (2 ^ (k + 1) - 1)) = 1 ∧
      y (Fin.last (2 ^ (k + 1) - 1)) = 1 ∧
      x ≠ 0 ∧ y ≠ 0 ∧
      (bilinearWeight P Q
          (0 : Fin n → F2) (0 : Fin n → F2) x y :
        ZMod (2 ^ (k + 1))) = r := by
  let d := 2 ^ (k + 1) - 1
  have hhead :
      initialRows P * (initialRows Q)ᵀ = 1 :=
    initialRows_mul_transpose_eq_one P Q hPQ
  obtain ⟨u, v, huv⟩ :=
    exists_bilinearWeight_eq_residue
      k (initialRows P) (initialRows Q)
        (finalRow P) (finalRow Q) hhead r
  let x : Fin (d + 1) → F2 := Fin.snoc u (1 : F2)
  let y : Fin (d + 1) → F2 := Fin.snoc v (1 : F2)
  have hxlast : x (Fin.last d) = 1 := by
    simp [x]
  have hylast : y (Fin.last d) = 1 := by
    simp [y]
  have hx : x ≠ 0 := by
    intro hx0
    have hz := congrFun hx0 (Fin.last d)
    have : (1 : F2) = 0 := by
      simpa [hxlast] using hz
    exact one_ne_zero this
  have hy : y ≠ 0 := by
    intro hy0
    have hz := congrFun hy0 (Fin.last d)
    have : (1 : F2) = 0 := by
      simpa [hylast] using hz
    exact one_ne_zero this
  have hweight :
      bilinearWeight (initialRows P) (initialRows Q)
          (finalRow P) (finalRow Q) u v =
        bilinearWeight P Q
          (0 : Fin n → F2) (0 : Fin n → F2) x y := by
    simpa [d, x, y] using
      bilinearWeight_initialRows_eq_snoc P Q u v
  refine ⟨x, y, ?_, ?_, hx, hy, ?_⟩
  · simpa [d] using hxlast
  · simpa [d] using hylast
  · rw [← hweight]
    exact huv

/-- Reduction modulo two from a power-of-two residue ring. -/
def residueParityHom (k : ℕ) :
    ZMod (2 ^ (k + 1)) →+* F2 :=
  ZMod.castHom
    (dvd_pow_self 2 (Nat.succ_ne_zero k))
    (ZMod 2)

/-- Full BANANA target-copy wrapper.

Every residue in a `B_q`-copy is realised by two nonzero vectors, and the
pairing of those vectors is exactly the parity of the residue.  This is the
affine-slice step used for both `A_0` and `A_1`. -/
theorem exists_nonzero_pair_of_residue
    (k : ℕ) {n : ℕ}
    (P Q :
      Matrix (Fin ((2 ^ (k + 1) - 1) + 1)) (Fin n) F2)
    (hPQ : P * Qᵀ = 1)
    (r : ZMod (2 ^ (k + 1))) :
    ∃ x y : Fin ((2 ^ (k + 1) - 1) + 1) → F2,
      x ≠ 0 ∧ y ≠ 0 ∧
      x ⬝ᵥ y = residueParityHom k r ∧
      (bilinearWeight P Q
          (0 : Fin n → F2) (0 : Fin n → F2) x y :
        ZMod (2 ^ (k + 1))) = r := by
  obtain ⟨x, y, hxlast, hylast, hx, hy, hres⟩ :=
    exists_snoc_bilinearWeight_eq_residue k P Q hPQ r
  have hred := congrArg (residueParityHom k) hres
  have hpar :
      (bilinearWeight P Q
          (0 : Fin n → F2) (0 : Fin n → F2) x y : F2) =
        residueParityHom k r := by
    simpa [residueParityHom] using hred
  have hdot :=
    bilinearWeight_natCast_f2_eq_dotProduct P Q hPQ x y
  refine ⟨x, y, hx, hy, ?_, hres⟩
  exact hdot.symm.trans hpar

/-- The smaller `B_{q-1}` target already works for the pairing-one source:
every odd residue is realised by nonzero vectors whose pairing is one. -/
theorem exists_pairing_one_bilinearWeight_eq_odd_residue
    (k : ℕ) {n : ℕ}
    (A B : Matrix (Fin (2 ^ (k + 1) - 1)) (Fin n) F2)
    (hAB : A * Bᵀ = 1)
    (r : ℕ) (hr : Odd r) :
    ∃ x y : Fin (2 ^ (k + 1) - 1) → F2,
      x ≠ 0 ∧ y ≠ 0 ∧
      x ⬝ᵥ y = 1 ∧
      (bilinearWeight A B
          (0 : Fin n → F2) (0 : Fin n → F2) x y :
        ZMod (2 ^ (k + 1))) =
          (r : ZMod (2 ^ (k + 1))) := by
  obtain ⟨x, y, hx, hy, hres⟩ :=
    exists_nonzero_bilinearWeight_eq_odd_residue
      k A B hAB r hr
  have htwo : 2 ∣ 2 ^ (k + 1) :=
    dvd_pow_self 2 (Nat.succ_ne_zero k)
  let red : ZMod (2 ^ (k + 1)) →+* F2 :=
    ZMod.castHom htwo (ZMod 2)
  have hred := congrArg red hres
  have hpar :
      (bilinearWeight A B
          (0 : Fin n → F2) (0 : Fin n → F2) x y : F2) = 1 := by
    have hr2 : (r : F2) = 1 := hr.natCast_zmod_two
    simpa [red, hr2] using hred
  have hdot :=
    bilinearWeight_natCast_f2_eq_dotProduct A B hAB x y
  exact ⟨x, y, hx, hy, hdot.symm.trans hpar, hres⟩

end SuccessorTree.NonPrecompact

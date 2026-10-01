import SuccessorTree.NonPrecompact.PersistentColourings
import SuccessorTree.NonPrecompact.ResidueAlgebra
import SuccessorTree.NonPrecompact.CauchyBinet

/-!
# The bilinear residue count

This file packages the selected-column affine systems used in the
BANANA persistent-colouring argument.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators Matrix

/-- Restrict the rows of `Aᵀ` to a finite set of column indices of `A`,
using the canonical increasing enumeration of that set. -/
noncomputable def selectedRows
    {d n : ℕ} (A : Matrix (Fin d) (Fin n) F2)
    (s : Finset (Fin n)) :
    Matrix (Fin s.card) (Fin d) F2 :=
  Aᵀ.submatrix (s.orderEmbOfFin rfl) id

/-- Restrict an affine offset to the same canonical enumeration. -/
noncomputable def selectedRhs
    {n : ℕ} (c : Fin n → F2) (s : Finset (Fin n)) :
    Fin s.card → F2 :=
  fun i => c (s.orderEmbOfFin rfl i)

/-- The solution set of the affine system selected by `s`. -/
abbrev selectedFiber
    {d n : ℕ} (A : Matrix (Fin d) (Fin n) F2)
    (c : Fin n → F2) (s : Finset (Fin n)) :=
  affineFiber (selectedRows A s).mulVecLin (selectedRhs c s)

/-- The parity of the number of solutions of a selected affine system. -/
noncomputable def selectedParity
    {d n : ℕ} (A : Matrix (Fin d) (Fin n) F2)
    (c : Fin n → F2) (s : Finset (Fin n)) : F2 :=
  (Nat.card (selectedFiber A c s) : F2)

/-- If fewer than `d` equations are selected, the solution count is even. -/
theorem selectedParity_eq_zero_of_card_lt
    {d n : ℕ} (A : Matrix (Fin d) (Fin n) F2)
    (c : Fin n → F2) (s : Finset (Fin n))
    (hs : s.card < d) :
    selectedParity A c s = 0 := by
  rw [selectedParity, ZMod.natCast_eq_zero_iff_even]
  exact even_card_matrixAffineFiber_of_lt
    (selectedRows A s) (selectedRhs c s) hs

/-- When exactly `d` equations are selected, their solution-count parity
is the determinant of the corresponding square selected matrix. -/
theorem selectedParity_eq_det_of_card_eq
    {d n : ℕ} (A : Matrix (Fin d) (Fin n) F2)
    (c : Fin n → F2) (s : Finset (Fin n))
    (hs : s.card = d) :
    selectedParity A c s =
      (Aᵀ.submatrix (s.orderEmbOfFin hs) id).det := by
  subst d
  change
    (Nat.card
      (affineFiber (selectedRows A s).mulVecLin (selectedRhs c s)) : F2) =
      (Aᵀ.submatrix (s.orderEmbOfFin rfl) id).det
  simpa [selectedRows] using
    natCast_card_affineFiber_eq_det
      (M := selectedRows A s) (b := selectedRhs c s)

/-- The affine coordinate bit attached to column `i`. -/
noncomputable def affineBit
    {d n : ℕ} (A : Matrix (Fin d) (Fin n) F2)
    (c : Fin n → F2) (i : Fin n) (x : Fin d → F2) : F2 :=
  Aᵀ i ⬝ᵥ x + c i

/-- Every element of `F₂` is either zero or one. -/
theorem f2_eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  by_cases h : a = 0
  · exact Or.inl h
  · right
    apply ZMod.val_injective
    have hpos : 0 < a.val := (ZMod.val_pos).2 h
    have hlt : a.val < 2 := ZMod.val_lt a
    simp only [ZMod.val_one]
    omega

/-- The selected matrix equation is equivalent to saying that every
selected affine bit is one. -/
theorem selectedRows_mulVec_eq_iff_affineBit_one
    {d n : ℕ} (A : Matrix (Fin d) (Fin n) F2)
    (c : Fin n → F2) (s : Finset (Fin n)) (x : Fin d → F2) :
    selectedRows A s *ᵥ x =
        selectedRhs (fun i => 1 + c i) s ↔
      ∀ i ∈ s, affineBit A c i x = 1 := by
  constructor
  · intro h i hi
    have hi' : i ∈ Set.range (s.orderEmbOfFin rfl) := by
      simpa using hi
    obtain ⟨j, rfl⟩ := hi'
    have hj := congrFun h j
    change
      Aᵀ (s.orderEmbOfFin rfl j) ⬝ᵥ x =
        1 + c (s.orderEmbOfFin rfl j) at hj
    change
      Aᵀ (s.orderEmbOfFin rfl j) ⬝ᵥ x +
        c (s.orderEmbOfFin rfl j) = 1
    exact CharTwo.add_eq_iff_eq_add.mpr hj
  · intro h
    funext j
    have hj := h (s.orderEmbOfFin rfl j)
      (Finset.orderEmbOfFin_mem s rfl j)
    change
      Aᵀ (s.orderEmbOfFin rfl j) ⬝ᵥ x =
        1 + c (s.orderEmbOfFin rfl j)
    change
      Aᵀ (s.orderEmbOfFin rfl j) ⬝ᵥ x +
        c (s.orderEmbOfFin rfl j) = 1 at hj
    exact CharTwo.add_eq_iff_eq_add.mp hj

/-- A product of affine `F₂`-bits is the indicator that all selected
bits are one. -/
theorem prod_affineBit_eq_indicator
    {d n : ℕ} (A : Matrix (Fin d) (Fin n) F2)
    (c : Fin n → F2) (s : Finset (Fin n)) (x : Fin d → F2) :
    (∏ i ∈ s, affineBit A c i x) =
      if (∀ i ∈ s, affineBit A c i x = 1) then 1 else 0 := by
  classical
  by_cases h : ∀ i ∈ s, affineBit A c i x = 1
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    exact h i hi
  · simp only [h, ite_false]
    push Not at h
    obtain ⟨i, hi, hne⟩ := h
    apply Finset.prod_eq_zero_iff.mpr
    refine ⟨i, hi, ?_⟩
    exact (f2_eq_zero_or_one (affineBit A c i x)).resolve_right hne

/-- Summing a selected affine-bit product over all vectors gives the
parity of the corresponding affine fibre. -/
theorem sum_prod_affineBit_eq_selectedParity
    {d n : ℕ} (A : Matrix (Fin d) (Fin n) F2)
    (c : Fin n → F2) (s : Finset (Fin n)) :
    (∑ x : Fin d → F2, ∏ i ∈ s, affineBit A c i x) =
      selectedParity A (fun i => 1 + c i) s := by
  classical
  let p : (Fin d → F2) → Prop := fun x =>
    selectedRows A s *ᵥ x =
      selectedRhs (fun i => 1 + c i) s
  have hp (x : Fin d → F2) :
      (∀ i ∈ s, affineBit A c i x = 1) ↔ p x :=
    (selectedRows_mulVec_eq_iff_affineBit_one A c s x).symm
  calc
    (∑ x : Fin d → F2, ∏ i ∈ s, affineBit A c i x) =
        ∑ x : Fin d → F2, if p x then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [prod_affineBit_eq_indicator]
      exact if_congr (hp x) rfl rfl
    _ = (Nat.card {x : Fin d → F2 // p x} : F2) := by
      rw [Nat.card_eq_fintype_card, Finset.sum_boole,
        ← Fintype.card_subtype]
    _ = selectedParity A (fun i => 1 + c i) s := by
      rfl

/-- The Boolean product contributing at coordinate `i`. -/
noncomputable def pairBit
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2) (i : Fin n)
    (x y : Fin d → F2) : F2 :=
  affineBit A c i x * affineBit B e i y

/-- The ordinary integer weight from the manuscript. -/
noncomputable def bilinearWeight
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2)
    (x y : Fin d → F2) : ℕ :=
  ∑ i : Fin n, (pairBit A B c e i x y).val

/-- The residue generating function `∑_{x,y} z^{F(x,y)}`. -/
noncomputable def bilinearGenerating
    (q : ℕ) {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2) : ResidueAlgebra q :=
  ∑ x : Fin d → F2, ∑ y : Fin d → F2,
    residueZ q ^ bilinearWeight A B c e x y

/-- A single pair contributes the product of its Boolean residue factors. -/
theorem residueZ_pow_bilinearWeight_eq_prod_residueFactor
    (q : ℕ) {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2)
    (x y : Fin d → F2) :
    residueZ q ^ bilinearWeight A B c e x y =
      ∏ i : Fin n, residueFactor q (pairBit A B c e i x y) := by
  rw [bilinearWeight]
  exact (prod_residueFactor_eq_residueZ_pow_sum
    (q := q) Finset.univ
    (fun i => pairBit A B c e i x y)).symm

/-- Product parity for the two affine systems occurring in the bilinear
residue expansion. -/
noncomputable def selectedPairParity
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2) (s : Finset (Fin n)) : F2 :=
  selectedParity A c s * selectedParity B e s

/-- The double sum of a selected product of left and right affine
bits is exactly the selected pair parity. -/
theorem sum_prod_affineBit_pair_eq_selectedPairParity
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2) (s : Finset (Fin n)) :
    (∑ x : Fin d → F2, ∑ y : Fin d → F2,
      ∏ i ∈ s, affineBit A c i x * affineBit B e i y) =
      selectedPairParity A B
        (fun i => 1 + c i) (fun i => 1 + e i) s := by
  rw [selectedPairParity]
  simp_rw [Finset.prod_mul_distrib]
  calc
    (∑ x : Fin d → F2, ∑ y : Fin d → F2,
        (∏ i ∈ s, affineBit A c i x) *
          ∏ i ∈ s, affineBit B e i y) =
        (∑ x : Fin d → F2, ∏ i ∈ s, affineBit A c i x) *
          ∑ y : Fin d → F2, ∏ i ∈ s, affineBit B e i y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ = selectedParity A (fun i => 1 + c i) s *
        selectedParity B (fun i => 1 + e i) s := by
      rw [sum_prod_affineBit_eq_selectedParity,
        sum_prod_affineBit_eq_selectedParity]

/-- Expanding the residue generating function over subsets gives
selected affine-fibre parities as coefficients. -/
theorem bilinearGenerating_eq_powerset
    (q : ℕ) {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2) :
    bilinearGenerating q A B c e =
      ∑ u ∈ (Finset.univ : Finset (Fin n)).powerset,
        residueCoeff q
            (selectedPairParity A B
              (fun i => 1 + c i) (fun i => 1 + e i) u) *
          residueT q ^ u.card := by
  let P := (Finset.univ : Finset (Fin n)).powerset
  calc
    bilinearGenerating q A B c e =
        ∑ x : Fin d → F2, ∑ y : Fin d → F2,
          ∑ u ∈ P,
            residueCoeff q
                (∏ i ∈ u, pairBit A B c e i x y) *
              residueT q ^ u.card := by
      rw [bilinearGenerating]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [residueZ_pow_bilinearWeight_eq_prod_residueFactor]
      simpa [P] using
        prod_residueFactor_eq_sum_powerset
          (q := q) (Finset.univ : Finset (Fin n))
          (fun i => pairBit A B c e i x y)
    _ = ∑ x : Fin d → F2, ∑ u ∈ P, ∑ y : Fin d → F2,
          residueCoeff q
              (∏ i ∈ u, pairBit A B c e i x y) *
            residueT q ^ u.card := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ u ∈ P, ∑ x : Fin d → F2, ∑ y : Fin d → F2,
          residueCoeff q
              (∏ i ∈ u, pairBit A B c e i x y) *
            residueT q ^ u.card := by
      rw [Finset.sum_comm]
    _ = ∑ u ∈ P,
          residueCoeff q
              (selectedPairParity A B
                (fun i => 1 + c i) (fun i => 1 + e i) u) *
            residueT q ^ u.card := by
      apply Finset.sum_congr rfl
      intro u hu
      calc
        (∑ x : Fin d → F2, ∑ y : Fin d → F2,
            residueCoeff q
                (∏ i ∈ u, pairBit A B c e i x y) *
              residueT q ^ u.card) =
            (∑ x : Fin d → F2, ∑ y : Fin d → F2,
              residueCoeff q
                (∏ i ∈ u, pairBit A B c e i x y)) *
              residueT q ^ u.card := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro x hx
                rw [Finset.sum_mul]
        _ = residueCoeff q
              (∑ x : Fin d → F2, ∑ y : Fin d → F2,
                ∏ i ∈ u, pairBit A B c e i x y) *
              residueT q ^ u.card := by
                congr 1
                simp_rw [← residueCoeff_fintype_sum]
        _ = residueCoeff q
              (selectedPairParity A B
                (fun i => 1 + c i) (fun i => 1 + e i) u) *
              residueT q ^ u.card := by
                rw [show
                  (∑ x : Fin d → F2, ∑ y : Fin d → F2,
                    ∏ i ∈ u, pairBit A B c e i x y) =
                    selectedPairParity A B
                      (fun i => 1 + c i)
                      (fun i => 1 + e i) u by
                  simpa [pairBit] using
                    sum_prod_affineBit_pair_eq_selectedPairParity
                      A B c e u]
    _ = ∑ u ∈ (Finset.univ : Finset (Fin n)).powerset,
          residueCoeff q
              (selectedPairParity A B
                (fun i => 1 + c i) (fun i => 1 + e i) u) *
            residueT q ^ u.card := by rfl

/-- At full size, the product of the two affine-fibre parities is
the corresponding principal minor of `Bᵀ * A`. -/
theorem selectedPairParity_eq_principalMinor_of_card_eq
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2) (s : Finset (Fin n))
    (hs : s.card = d) :
    selectedPairParity A B c e s =
      ((Bᵀ * A).submatrix
        (s.orderEmbOfFin hs) (s.orderEmbOfFin hs)).det := by
  rw [selectedPairParity,
    selectedParity_eq_det_of_card_eq A c s hs,
    selectedParity_eq_det_of_card_eq B e s hs]
  let emb := s.orderEmbOfFin hs
  have hA :
      (Aᵀ.submatrix emb id).det =
        (A.submatrix id emb).det := by
    calc
      (Aᵀ.submatrix emb id).det =
          ((Aᵀ.submatrix emb id)ᵀ).det :=
        (Matrix.det_transpose _).symm
      _ = (A.submatrix id emb).det := by simp
  have hmul :
      Bᵀ.submatrix emb id * A.submatrix id emb =
        (Bᵀ * A).submatrix emb emb := by
    simpa using
      (Matrix.submatrix_mul_equiv
        Bᵀ A emb (Equiv.refl (Fin d)) emb)
  calc
    (Aᵀ.submatrix emb id).det * (Bᵀ.submatrix emb id).det =
        (Bᵀ.submatrix emb id).det * (Aᵀ.submatrix emb id).det := by
          rw [mul_comm]
    _ = (Bᵀ.submatrix emb id).det * (A.submatrix id emb).det := by
          rw [hA]
    _ = (Bᵀ.submatrix emb id * A.submatrix id emb).det :=
      (Matrix.det_mul _ _).symm
    _ = ((Bᵀ * A).submatrix emb emb).det := by rw [hmul]

/-- Summing the full-size selected-pair parities gives one.  This is
the Cauchy--Binet step in the BANANA residue count. -/
theorem sum_selectedPairParity_powersetCard_eq_one
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2)
    (hAB : A * Bᵀ = 1) :
    (∑ ss ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
      selectedPairParity A B c e ss) = 1 := by
  let S := (Finset.univ : Finset (Fin n)).powersetCard d
  calc
    (∑ ss ∈ S, selectedPairParity A B c e ss) =
        ∑ ss ∈ S,
          ((Bᵀ * A).submatrix
            (Subtype.val : ss → Fin n)
            (Subtype.val : ss → Fin n)).det := by
      apply Finset.sum_congr rfl
      intro ss hss
      have hcard : ss.card = d :=
        (Finset.mem_powersetCard.1 hss).2
      rw [selectedPairParity_eq_principalMinor_of_card_eq
        A B c e ss hcard]
      rw [← det_principal_submatrix_eq_orderEmb
        (Bᵀ * A) ss hcard]
    _ = 1 := by
      simpa [S] using
        sum_principal_minors_transpose_mul_eq_one A B hAB

theorem selectedPairParity_eq_zero_of_card_lt
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2) (s : Finset (Fin n))
    (hs : s.card < d) :
    selectedPairParity A B c e s = 0 := by
  simp [selectedPairParity, selectedParity_eq_zero_of_card_lt A c s hs]

/-- Pairs realising a fixed residue of the ordinary integer
bilinear weight. -/
def bilinearResidueFiber
    (q : ℕ) {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2) (r : ZMod q) :=
  {p : (Fin d → F2) × (Fin d → F2) //
    (bilinearWeight A B c e p.1 p.2 : ZMod q) = r}

/-- The coefficient of `z^r` in the generating function is the parity
of the number of pairs whose ordinary integer weight has residue `r`. -/
theorem coeff_bilinearGenerating_eq_card_residueFiber
    (q : ℕ) [NeZero q] {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2) (r : ZMod q) :
    (bilinearGenerating q A B c e).coeff r =
      (Nat.card (bilinearResidueFiber q A B c e r) : F2) := by
  classical
  rw [bilinearGenerating]
  simp only [AddMonoidAlgebra.coeff_sum, Finset.sum_apply',
    residueZ_pow, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, nsmul_one]
  rw [← Fintype.sum_prod_type']
  change
    (∑ p : (Fin d → F2) × (Fin d → F2),
      if (bilinearWeight A B c e p.1 p.2 : ZMod q) = r then 1 else 0) =
      (Nat.card (bilinearResidueFiber q A B c e r) : F2)
  letI : Fintype
      {p : (Fin d → F2) × (Fin d → F2) //
        (bilinearWeight A B c e p.1 p.2 : ZMod q) = r} :=
    Fintype.ofInjective Subtype.val Subtype.coe_injective
  calc
    (∑ p : (Fin d → F2) × (Fin d → F2),
      if (bilinearWeight A B c e p.1 p.2 : ZMod q) = r then 1 else 0) =
        (Nat.card
          {p : (Fin d → F2) × (Fin d → F2) //
            (bilinearWeight A B c e p.1 p.2 : ZMod q) = r} : F2) := by
      rw [Nat.card_eq_fintype_card, Finset.sum_boole,
        ← Fintype.card_subtype]
    _ = (Nat.card (bilinearResidueFiber q A B c e r) : F2) := by
      rfl

/-- In the power-of-two case, all subset sizes except
`D = q - 1` vanish in the residue expansion. -/
theorem powerset_selectedPair_sum_eq_residueT_pow
    (k : ℕ) {n : ℕ}
    (A B : Matrix (Fin (2 ^ (k + 1) - 1)) (Fin n) F2)
    (c e : Fin n → F2)
    (hAB : A * Bᵀ = 1) :
    (∑ u ∈ (Finset.univ : Finset (Fin n)).powerset,
      residueCoeff (2 ^ (k + 1))
          (selectedPairParity A B
            (fun i => 1 + c i) (fun i => 1 + e i) u) *
        residueT (2 ^ (k + 1)) ^ u.card) =
      residueT (2 ^ (k + 1)) ^ (2 ^ (k + 1) - 1) := by
  classical
  let P := (Finset.univ : Finset (Fin n)).powerset
  let d := 2 ^ (k + 1) - 1
  let term : Finset (Fin n) → ResidueAlgebra (2 ^ (k + 1)) :=
    fun u =>
      residueCoeff (2 ^ (k + 1))
          (selectedPairParity A B
            (fun i => 1 + c i) (fun i => 1 + e i) u) *
        residueT (2 ^ (k + 1)) ^ u.card
  have hzero (u : Finset (Fin n)) (hu : u ∈ P)
      (hne : u.card ≠ d) : term u = 0 := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hp :
          selectedPairParity A B
            (fun i => 1 + c i) (fun i => 1 + e i) u = 0 :=
        selectedPairParity_eq_zero_of_card_lt
          A B (fun i => 1 + c i) (fun i => 1 + e i) u
          (by simpa [d] using hlt)
      simp [term, hp, residueCoeff]
    · have hqle : 2 ^ (k + 1) ≤ u.card := by
        have hqpos : 0 < 2 ^ (k + 1) := pow_pos (by decide) _
        dsimp [d] at hgt
        omega
      have ht : residueT (2 ^ (k + 1)) ^ u.card = 0 :=
        pow_eq_zero_of_le hqle
          (residueT_pow_two_pow_eq_zero (k + 1))
      simp [term, ht]
  calc
    (∑ u ∈ (Finset.univ : Finset (Fin n)).powerset,
        residueCoeff (2 ^ (k + 1))
            (selectedPairParity A B
              (fun i => 1 + c i) (fun i => 1 + e i) u) *
          residueT (2 ^ (k + 1)) ^ u.card) =
        ∑ u ∈ P, term u := by rfl
    _ = ∑ u ∈ P.filter (fun u => u.card = d), term u := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro u hu huf
      apply hzero u hu
      intro hcard
      apply huf
      simp [hu, hcard]
    _ = ∑ u ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
          term u := by
      rw [Finset.powersetCard_eq_filter]
    _ = ∑ u ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
          residueCoeff (2 ^ (k + 1))
              (selectedPairParity A B
                (fun i => 1 + c i) (fun i => 1 + e i) u) *
            residueT (2 ^ (k + 1)) ^ d := by
      apply Finset.sum_congr rfl
      intro u hu
      have hcard : u.card = d :=
        (Finset.mem_powersetCard.1 hu).2
      simp [term, hcard]
    _ = residueCoeff (2 ^ (k + 1))
          (∑ u ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
            selectedPairParity A B
              (fun i => 1 + c i) (fun i => 1 + e i) u) *
          residueT (2 ^ (k + 1)) ^ d := by
      rw [residueCoeff_sum, Finset.sum_mul]
    _ = residueT (2 ^ (k + 1)) ^ d := by
      have hsum :
          (∑ u ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
            selectedPairParity A B
              (fun i => 1 + c i) (fun i => 1 + e i) u) = 1 := by
        simpa [d] using
          sum_selectedPairParity_powersetCard_eq_one
            A B (fun i => 1 + c i) (fun i => 1 + e i) hAB
      rw [hsum]
      change (1 : ResidueAlgebra (2 ^ (k + 1))) *
          residueT (2 ^ (k + 1)) ^ d =
        residueT (2 ^ (k + 1)) ^ d
      rw [one_mul]
    _ = residueT (2 ^ (k + 1)) ^ (2 ^ (k + 1) - 1) := by
      rfl

/-- Bilinear residue count: for `q = 2^(k+1)`, every residue is
attained an odd number of times by the ordinary integer weight. -/
theorem bilinearResidueFiber_card_odd
    (k : ℕ) {n : ℕ}
    (A B : Matrix (Fin (2 ^ (k + 1) - 1)) (Fin n) F2)
    (c e : Fin n → F2)
    (hAB : A * Bᵀ = 1)
    (r : ZMod (2 ^ (k + 1))) :
    Odd (Nat.card
      (bilinearResidueFiber (2 ^ (k + 1)) A B c e r)) := by
  have hgen :
      bilinearGenerating (2 ^ (k + 1)) A B c e =
        residueT (2 ^ (k + 1)) ^ (2 ^ (k + 1) - 1) := by
    calc
      bilinearGenerating (2 ^ (k + 1)) A B c e =
          ∑ u ∈ (Finset.univ : Finset (Fin n)).powerset,
            residueCoeff (2 ^ (k + 1))
                (selectedPairParity A B
                  (fun i => 1 + c i) (fun i => 1 + e i) u) *
              residueT (2 ^ (k + 1)) ^ u.card :=
        bilinearGenerating_eq_powerset
          (2 ^ (k + 1)) A B c e
      _ = residueT (2 ^ (k + 1)) ^ (2 ^ (k + 1) - 1) :=
        powerset_selectedPair_sum_eq_residueT_pow
          k A B c e hAB
  have hcoeff :
      (Nat.card
        (bilinearResidueFiber (2 ^ (k + 1)) A B c e r) : F2) = 1 := by
    calc
      (Nat.card
          (bilinearResidueFiber (2 ^ (k + 1)) A B c e r) : F2) =
          (bilinearGenerating (2 ^ (k + 1)) A B c e).coeff r :=
        (coeff_bilinearGenerating_eq_card_residueFiber
          (2 ^ (k + 1)) A B c e r).symm
      _ = (residueT (2 ^ (k + 1)) ^
            (2 ^ (k + 1) - 1)).coeff r := by
          rw [hgen]
      _ = 1 :=
        coeff_residueT_pow_pred_two_pow_eq_one (k + 1) r
  exact ZMod.natCast_eq_one_iff_odd.mp hcoeff

/-- Surjectivity form of the bilinear residue count. -/
theorem exists_bilinearWeight_eq_residue
    (k : ℕ) {n : ℕ}
    (A B : Matrix (Fin (2 ^ (k + 1) - 1)) (Fin n) F2)
    (c e : Fin n → F2)
    (hAB : A * Bᵀ = 1)
    (r : ZMod (2 ^ (k + 1))) :
    ∃ x y : Fin (2 ^ (k + 1) - 1) → F2,
      (bilinearWeight A B c e x y : ZMod (2 ^ (k + 1))) = r := by
  have hodd := bilinearResidueFiber_card_odd k A B c e hAB r
  have hpos :
      0 < Nat.card
        (bilinearResidueFiber (2 ^ (k + 1)) A B c e r) :=
    hodd.pos
  have hne :
      Nonempty (bilinearResidueFiber (2 ^ (k + 1)) A B c e r) :=
    (Nat.card_pos_iff.mp hpos).1
  let p := Classical.choice hne
  exact ⟨p.1.1, p.1.2, p.2⟩

/-- Zero-offset form used for the one-atom BANANA source:
an odd residue is realised by nonzero vectors on both sides. -/
theorem exists_nonzero_bilinearWeight_eq_odd_residue
    (k : ℕ) {n : ℕ}
    (A B : Matrix (Fin (2 ^ (k + 1) - 1)) (Fin n) F2)
    (hAB : A * Bᵀ = 1)
    (r : ℕ) (hr : Odd r) :
    ∃ x y : Fin (2 ^ (k + 1) - 1) → F2,
      x ≠ 0 ∧ y ≠ 0 ∧
        (bilinearWeight A B (0 : Fin n → F2) (0 : Fin n → F2) x y :
          ZMod (2 ^ (k + 1))) =
          (r : ZMod (2 ^ (k + 1))) := by
  obtain ⟨x, y, hxy⟩ :=
    exists_bilinearWeight_eq_residue
      k A B (0 : Fin n → F2) (0 : Fin n → F2) hAB
        (r : ZMod (2 ^ (k + 1)))
  have hrne : (r : ZMod (2 ^ (k + 1))) ≠ 0 :=
    odd_natCast_two_pow_ne_zero (k := k + 1) (Nat.succ_pos k) hr
  have hx : x ≠ 0 := by
    intro hx0
    subst x
    apply hrne
    symm
    simpa [bilinearWeight, pairBit, affineBit] using hxy
  have hy : y ≠ 0 := by
    intro hy0
    subst y
    apply hrne
    symm
    simpa [bilinearWeight, pairBit, affineBit] using hxy
  exact ⟨x, y, hx, hy, hxy⟩

end SuccessorTree.NonPrecompact

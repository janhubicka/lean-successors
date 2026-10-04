import SuccessorTree.NonPrecompact.BilinearResidue

/-!
# Subset moments for the quadratic residue argument

For a finite family of pairs of affine F₂-bits on one variable space, a
selected set S of k coordinates imposes the 2k equations saying that both
bits are one at every coordinate in S.  We package these two systems as one
affine fibre with product codomain.

The general affine-fibre dimension theorem then gives divisibility by
2^(n-2k), and summing over all k-subsets preserves that divisibility.  This
is the linear-algebra counting core of the manuscript's quadratic moments.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators Matrix

/-- Simultaneous selected affine equations for the two affine-bit families. -/
abbrev selectedPairFiber
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2)
    (s : Finset (Fin n)) :=
  affineFiber
    (LinearMap.prod
      (selectedRows A s).mulVecLin
      (selectedRows B s).mulVecLin)
    (selectedRhs (fun i => 1 + c i) s,
      selectedRhs (fun i => 1 + e i) s)

/-- The simultaneous selected system has solution count divisible by
2^(d-2|S|). -/
theorem pow_two_sub_two_card_dvd_selectedPairFiber
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2)
    (s : Finset (Fin n)) :
    2 ^ (d - 2 * s.card) ∣
      Nat.card (selectedPairFiber A B c e s) := by
  have h :=
    pow_two_finrank_sub_dvd_card_affineFiber
      (L :=
        LinearMap.prod
          (selectedRows A s).mulVecLin
          (selectedRows B s).mulVecLin)
      (b :=
        (selectedRhs (fun i => 1 + c i) s,
          selectedRhs (fun i => 1 + e i) s))
  simpa [selectedPairFiber, Module.finrank_pi, Nat.two_mul] using h

/-- The k-th subset moment: sum, over all k-subsets S of the coordinate
family, of the number of vectors on which both selected affine bits are one. -/
noncomputable def quadraticSubsetMoment
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2)
    (k : ℕ) : ℕ :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
    Nat.card (selectedPairFiber A B c e s)

/-- Every k-th subset moment is divisible by 2^(d-2k). -/
theorem pow_two_sub_two_mul_dvd_quadraticSubsetMoment
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2)
    (k : ℕ) :
    2 ^ (d - 2 * k) ∣ quadraticSubsetMoment A B c e k := by
  unfold quadraticSubsetMoment
  apply Finset.dvd_sum
  intro s hs
  have hcard : s.card = k :=
    (Finset.mem_powersetCard.mp hs).2
  simpa [hcard] using
    pow_two_sub_two_card_dvd_selectedPairFiber A B c e s


/-- A Boolean product is one exactly when both factors are one. -/
theorem pairBit_self_eq_one_iff
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2)
    (i : Fin n) (x : Fin d → F2) :
    pairBit A B c e i x x = 1 ↔
      affineBit A c i x = 1 ∧ affineBit B e i x = 1 := by
  rcases f2_eq_zero_or_one (affineBit A c i x) with hA | hA <;>
    rcases f2_eq_zero_or_one (affineBit B e i x) with hB | hB <;>
      simp [pairBit, hA, hB]

/-- The selected pair affine fibre is exactly the set of vectors on which
every selected Boolean product is one. -/
theorem selectedPairFiber_pred_iff
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2)
    (s : Finset (Fin n))
    (x : Fin d → F2) :
    (LinearMap.prod
        (selectedRows A s).mulVecLin
        (selectedRows B s).mulVecLin) x =
      (selectedRhs (fun i => 1 + c i) s,
        selectedRhs (fun i => 1 + e i) s) ↔
      ∀ i ∈ s, pairBit A B c e i x x = 1 := by
  change
    ((selectedRows A s) *ᵥ x =
        selectedRhs (fun i => 1 + c i) s ∧
      (selectedRows B s) *ᵥ x =
        selectedRhs (fun i => 1 + e i) s) ↔ _
  rw [
    selectedRows_mulVec_eq_iff_affineBit_one A c s x,
    selectedRows_mulVec_eq_iff_affineBit_one B e s x]
  constructor
  · rintro ⟨hA, hB⟩ i hi
    exact (pairBit_self_eq_one_iff A B c e i x).2
      ⟨hA i hi, hB i hi⟩
  · intro h
    constructor
    · intro i hi
      exact ((pairBit_self_eq_one_iff A B c e i x).1 (h i hi)).1
    · intro i hi
      exact ((pairBit_self_eq_one_iff A B c e i x).1 (h i hi)).2

/-- Coordinates at which the quadratic Boolean product is one. -/
noncomputable def quadraticPairOnes
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2)
    (x : Fin d → F2) : Finset (Fin n) :=
  Finset.univ.filter fun i => pairBit A B c e i x x = 1

/-- The ordinary integer quadratic weight is the number of coordinates
where the corresponding Boolean product equals one. -/
theorem bilinearWeight_self_eq_quadraticPairOnes_card
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2)
    (x : Fin d → F2) :
    bilinearWeight A B c e x x =
      (quadraticPairOnes A B c e x).card := by
  unfold bilinearWeight quadraticPairOnes
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  rcases f2_eq_zero_or_one (pairBit A B c e i x x) with h | h
  · simp [h]
  · simp [h]

/-- The selected pair fibre cardinality is a Boolean indicator sum over the
ambient vector space. -/
theorem card_selectedPairFiber_eq_sum_indicator
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2)
    (s : Finset (Fin n)) :
    Nat.card (selectedPairFiber A B c e s) =
      ∑ x : Fin d → F2,
        if (∀ i ∈ s, pairBit A B c e i x x = 1) then 1 else 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply Finset.sum_congr rfl
  intro x hx
  rw [if_congr (selectedPairFiber_pred_iff A B c e s x) rfl rfl]

/-- For a fixed vector, the number of selected k-subsets on which every
Boolean product is one is the corresponding binomial coefficient. -/
theorem sum_powersetCard_indicator_eq_choose_weight
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2)
    (x : Fin d → F2)
    (k : ℕ) :
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      if (∀ i ∈ s, pairBit A B c e i x x = 1) then 1 else 0) =
      Nat.choose (bilinearWeight A B c e x x) k := by
  let ones := quadraticPairOnes A B c e x
  have hfilter :
      ((Finset.univ : Finset (Fin n)).powersetCard k).filter
          (fun s => ∀ i ∈ s, pairBit A B c e i x x = 1) =
        ones.powersetCard k := by
    ext s
    simp [ones, quadraticPairOnes, Finset.mem_powersetCard]
  calc
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        if (∀ i ∈ s, pairBit A B c e i x x = 1) then 1 else 0) =
        (((Finset.univ : Finset (Fin n)).powersetCard k).filter
          (fun s => ∀ i ∈ s, pairBit A B c e i x x = 1)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = (ones.powersetCard k).card := by rw [hfilter]
    _ = Nat.choose ones.card k := by rw [Finset.card_powersetCard]
    _ = Nat.choose (bilinearWeight A B c e x x) k := by
      rw [bilinearWeight_self_eq_quadraticPairOnes_card A B c e x]

/-- The selected-subset moment is exactly the manuscript's binomial moment
sum_z binom(Q(z), k), with Q represented by the diagonal bilinear weight. -/
theorem quadraticSubsetMoment_eq_sum_choose_bilinearWeight_self
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2)
    (k : ℕ) :
    quadraticSubsetMoment A B c e k =
      ∑ x : Fin d → F2, Nat.choose (bilinearWeight A B c e x x) k := by
  unfold quadraticSubsetMoment
  calc
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        Nat.card (selectedPairFiber A B c e s)) =
        ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          ∑ x : Fin d → F2,
            if (∀ i ∈ s, pairBit A B c e i x x = 1) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [card_selectedPairFiber_eq_sum_indicator]
    _ = ∑ x : Fin d → F2,
          ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
            if (∀ i ∈ s, pairBit A B c e i x x = 1) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : Fin d → F2,
          Nat.choose (bilinearWeight A B c e x x) k := by
      apply Finset.sum_congr rfl
      intro x hx
      exact sum_powersetCard_indicator_eq_choose_weight A B c e x k

end SuccessorTree.NonPrecompact

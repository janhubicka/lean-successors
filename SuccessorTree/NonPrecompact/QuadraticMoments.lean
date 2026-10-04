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

end SuccessorTree.NonPrecompact

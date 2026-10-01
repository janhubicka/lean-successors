import SuccessorTree.NonPrecompact.SubsetSums

/-!
# Persistent-colouring consequences of the subset-sum lemma

This file packages the arithmetic statements used verbatim in the
pre-BANANA and Folkman--BANANA lower bounds.

For pre-BANANA one first fixes the block containing the distinguished
ambient atom.  Its odd weight is a fixed additive shift, while arbitrary
unions of the remaining target blocks realise every residue.

For Folkman--BANANA there is no fixed block.  Every nonzero residue is
realised by a nonempty union of target blocks.  In the manuscript the
colours are odd residues, so this applies in particular to every colour.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- Adding a fixed shift to the subset sums does not destroy
surjectivity.  This is the arithmetic step in the pre-BANANA colouring. -/
theorem shifted_odd_indexedSubsetSums_two_pow
    {k : ℕ} {ι : Type*}
    (s : Finset ι) (a : ι → ℕ)
    (hcard : s.card + 1 = 2 ^ k)
    (ha : ∀ i ∈ s, Odd (a i))
    (c : ℕ) (r : ZMod (2 ^ k)) :
    ∃ t : Finset ι, t ⊆ s ∧
      (c : ZMod (2 ^ k)) + ∑ i ∈ t, (a i : ZMod (2 ^ k)) = r := by
  have hfull :=
    odd_indexedSubsetSums_two_pow_eq_univ s a hcard ha
  have hx :
      r - (c : ZMod (2 ^ k)) ∈
        indexedSubsetSums s (fun i => (a i : ZMod (2 ^ k))) := by
    rw [hfull]
    simp
  rw [mem_indexedSubsetSums_iff] at hx
  obtain ⟨t, ht, hsum⟩ := hx
  refine ⟨t, ht, ?_⟩
  rw [hsum]
  abel

/-- Pre-BANANA form: when the fixed block and target colour both
have odd marked-atom counts, the realising subset uses an even number of
the remaining odd target blocks.  Thus the chosen block and its complement
both contain an odd number of target blocks. -/
theorem prebanana_odd_residue_even_subset
    {k : ℕ} (hk : 0 < k) {ι : Type*}
    (s : Finset ι) (a : ι → ℕ)
    (hcard : s.card + 1 = 2 ^ k)
    (ha : ∀ i ∈ s, Odd (a i))
    (c r : ℕ) (hc : Odd c) (hr : Odd r) :
    ∃ t : Finset ι, t ⊆ s ∧ Even t.card ∧
      (c : ZMod (2 ^ k)) + ∑ i ∈ t, (a i : ZMod (2 ^ k)) =
        (r : ZMod (2 ^ k)) := by
  obtain ⟨t, ht, hsum⟩ :=
    shifted_odd_indexedSubsetSums_two_pow
      s a hcard ha c (r : ZMod (2 ^ k))
  have htwo : 2 ∣ 2 ^ k :=
    dvd_pow_self 2 (Nat.ne_of_gt hk)
  let red : ZMod (2 ^ k) →+* ZMod 2 :=
    ZMod.castHom htwo (ZMod 2)
  have hpar0 := congrArg red hsum
  change
    red ((c : ZMod (2 ^ k)) +
      ∑ i ∈ t, (a i : ZMod (2 ^ k))) =
      red (r : ZMod (2 ^ k)) at hpar0
  rw [map_add, map_sum] at hpar0
  have hpar :
      (c : ZMod 2) + ∑ i ∈ t, (a i : ZMod 2) = (r : ZMod 2) := by
    simpa [red] using hpar0
  have hsum2 :
      (∑ i ∈ t, (a i : ZMod 2)) = (t.card : ZMod 2) := by
    calc
      (∑ i ∈ t, (a i : ZMod 2)) =
          ∑ i ∈ t, (1 : ZMod 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (ha i (ht hi)).natCast_zmod_two
      _ = (t.card : ZMod 2) := by simp
  have hc2 : (c : ZMod 2) = 1 := hc.natCast_zmod_two
  have hr2 : (r : ZMod 2) = 1 := hr.natCast_zmod_two
  rw [hc2, hr2, hsum2] at hpar
  have hzero : (t.card : ZMod 2) = 0 := by
    calc
      (t.card : ZMod 2) = (1 + 1) + (t.card : ZMod 2) := by
        rw [CharTwo.add_self_eq_zero, zero_add]
      _ = 1 + (1 + (t.card : ZMod 2)) := by ac_rfl
      _ = 1 + 1 := by rw [hpar]
      _ = 0 := CharTwo.add_self_eq_zero 1
  have heven : Even t.card :=
    ZMod.natCast_eq_zero_iff_even.mp hzero
  exact ⟨t, ht, heven, hsum⟩

/-- A nonzero residue is represented by a nonempty subset.

This is the exact extra point needed in Folkman--BANANA: the selected
left union must contain at least one target atom. -/
theorem nonempty_odd_indexedSubsetSum_two_pow
    {k : ℕ} {ι : Type*}
    (s : Finset ι) (a : ι → ℕ)
    (hcard : s.card + 1 = 2 ^ k)
    (ha : ∀ i ∈ s, Odd (a i))
    (r : ZMod (2 ^ k)) (hr : r ≠ 0) :
    ∃ t : Finset ι, t ⊆ s ∧ t.Nonempty ∧
      (∑ i ∈ t, (a i : ZMod (2 ^ k))) = r := by
  have hfull :=
    odd_indexedSubsetSums_two_pow_eq_univ s a hcard ha
  have hx :
      r ∈ indexedSubsetSums s (fun i => (a i : ZMod (2 ^ k))) := by
    rw [hfull]
    simp
  rw [mem_indexedSubsetSums_iff] at hx
  obtain ⟨t, ht, hsum⟩ := hx
  have hne : t.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    subst t
    simp only [Finset.sum_empty] at hsum
    exact hr hsum.symm
  exact ⟨t, ht, hne, hsum⟩

/-- An odd natural residue below a nontrivial power of two is nonzero
modulo that power of two. -/
theorem odd_natCast_two_pow_ne_zero
    {k r : ℕ} (hk : 0 < k) (hr : Odd r) :
    (r : ZMod (2 ^ k)) ≠ 0 := by
  intro hzero
  have hdvd : 2 ^ k ∣ r :=
    (ZMod.natCast_eq_zero_iff r (2 ^ k)).mp hzero
  have htwo : 2 ∣ 2 ^ k := dvd_pow_self 2 (Nat.ne_of_gt hk)
  apply (Nat.not_even_iff_odd.mpr hr)
  rw [even_iff_two_dvd]
  exact dvd_trans htwo hdvd

/-- Folkman--BANANA form: every odd residue is realised by a nonempty
indexed subset of the first `q-1` odd weights. -/
theorem folkman_odd_residue
    {k : ℕ} (hk : 0 < k) {ι : Type*}
    (s : Finset ι) (a : ι → ℕ)
    (hcard : s.card + 1 = 2 ^ k)
    (ha : ∀ i ∈ s, Odd (a i))
    (r : ℕ) (hr : Odd r) :
    ∃ t : Finset ι, t ⊆ s ∧ t.Nonempty ∧
      (∑ i ∈ t, (a i : ZMod (2 ^ k))) = (r : ZMod (2 ^ k)) := by
  exact nonempty_odd_indexedSubsetSum_two_pow
    s a hcard ha (r : ZMod (2 ^ k)) (odd_natCast_two_pow_ne_zero hk hr)

end SuccessorTree.NonPrecompact

import Mathlib

/-!
# Subset-sum lower bounds for the non-precompact colourings

This file formalises the common combinatorial core of the pre-BANANA and
Folkman--BANANA persistent colourings.

The paper uses the following elementary fact. If `q` is a power of two,
then the subset sums of any `q - 1` odd integers cover every residue modulo
`q`. We prove a slightly more general statement: over `ZMod q`, `q - 1`
weights that are units have all residues as indexed subset sums.

The proof follows the manuscript. Starting from `{0}`, adjoining a unit
strictly enlarges the set of attainable sums unless it is already all of
`ZMod q`. Translation by a unit generates the additive cyclic group.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- Indexed subset sums. Keeping the index set is important: the same weight
may occur several times in the colouring arguments. -/
noncomputable def indexedSubsetSums
    {ι M : Type*} [AddCommMonoid M] (s : Finset ι) (a : ι → M) : Finset M := by
  classical
  exact s.powerset.image (fun t => ∑ i ∈ t, a i)

theorem mem_indexedSubsetSums_iff
    {ι M : Type*} [AddCommMonoid M]
    {s : Finset ι} {a : ι → M} {x : M} :
    x ∈ indexedSubsetSums s a ↔
      ∃ t : Finset ι, t ⊆ s ∧ (∑ i ∈ t, a i) = x := by
  classical
  simp [indexedSubsetSums]

@[simp] theorem zero_mem_indexedSubsetSums
    {ι M : Type*} [AddCommMonoid M]
    (s : Finset ι) (a : ι → M) :
    0 ∈ indexedSubsetSums s a := by
  rw [mem_indexedSubsetSums_iff]
  exact ⟨∅, by simp, by simp⟩

theorem indexedSubsetSums_mono
    {ι M : Type*} [AddCommMonoid M]
    {s t : Finset ι} {a : ι → M} (hst : s ⊆ t) :
    indexedSubsetSums s a ⊆ indexedSubsetSums t a := by
  intro x hx
  rw [mem_indexedSubsetSums_iff] at hx ⊢
  obtain ⟨u, hu, hsum⟩ := hx
  exact ⟨u, hu.trans hst, hsum⟩

theorem add_mem_indexedSubsetSums_insert
    {ι M : Type*} [DecidableEq ι] [AddCommMonoid M]
    {s : Finset ι} {a : ι → M} {i : ι} {x : M}
    (hi : i ∉ s) (hx : x ∈ indexedSubsetSums s a) :
    a i + x ∈ indexedSubsetSums (insert i s) a := by
  classical
  rw [mem_indexedSubsetSums_iff] at hx ⊢
  obtain ⟨u, hu, hsum⟩ := hx
  have hiu : i ∉ u := fun hiu => hi (hu hiu)
  refine ⟨insert i u, ?_, ?_⟩
  · rw [Finset.insert_subset_iff]
    exact ⟨Finset.mem_insert_self i s, hu.trans (Finset.subset_insert i s)⟩
  · rw [Finset.sum_insert hiu, hsum]

/-- A unit of `ZMod q` additively generates all of `ZMod q`. -/
theorem exists_nsmul_eq_of_isUnit
    {q : ℕ} [NeZero q] {a y : ZMod q} (ha : IsUnit a) :
    ∃ n : ℕ, n • a = y := by
  let u := ha.unit
  let z : ZMod q := y * (↑(u⁻¹) : ZMod q)
  refine ⟨z.val, ?_⟩
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  change z * a = y
  rw [show a = (u : ZMod q) by exact ha.unit_spec.symm]
  simp [z, mul_assoc]

/-- If a finite set contains zero and is closed under translation by a unit,
then it is the whole cyclic group. -/
theorem eq_univ_of_zero_mem_add_closed_isUnit
    {q : ℕ} [NeZero q]
    (S : Finset (ZMod q)) {a : ZMod q}
    (hzero : 0 ∈ S)
    (hshift : ∀ x ∈ S, x + a ∈ S)
    (ha : IsUnit a) :
    S = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro y
  obtain ⟨n, rfl⟩ := exists_nsmul_eq_of_isUnit (a := a) (y := y) ha
  induction n with
  | zero =>
      simpa using hzero
  | succ n ih =>
      rw [succ_nsmul]
      exact hshift (n • a) ih

/-- Unless `S` is already all of `ZMod q`, translating some member by a
unit leaves `S`. -/
theorem exists_mem_add_not_mem_of_isUnit
    {q : ℕ} [NeZero q]
    (S : Finset (ZMod q)) {a : ZMod q}
    (hzero : 0 ∈ S) (hS : S ≠ Finset.univ) (ha : IsUnit a) :
    ∃ x ∈ S, x + a ∉ S := by
  by_contra h
  push Not at h
  exact hS (eq_univ_of_zero_mem_add_closed_isUnit S hzero h ha)

/-- Adjoining one indexed unit strictly increases the set of subset sums,
unless all residues were already present. -/
theorem card_indexedSubsetSums_lt_insert_of_isUnit
    {q : ℕ} [NeZero q]
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {a : ι → ZMod q} {i : ι}
    (hi : i ∉ s)
    (hfull : indexedSubsetSums s a ≠ Finset.univ)
    (hai : IsUnit (a i)) :
    (indexedSubsetSums s a).card <
      (indexedSubsetSums (insert i s) a).card := by
  classical
  let S := indexedSubsetSums s a
  have hzero : 0 ∈ S := by
    dsimp [S]
    exact zero_mem_indexedSubsetSums s a
  obtain ⟨x, hxS, hxout⟩ :=
    exists_mem_add_not_mem_of_isUnit S hzero hfull hai
  have hsub :
      indexedSubsetSums s a ⊆ indexedSubsetSums (insert i s) a :=
    indexedSubsetSums_mono (Finset.subset_insert i s)
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset hsub]
  refine ⟨x + a i, ?_, hxout⟩
  simpa [add_comm] using
    add_mem_indexedSubsetSums_insert (s := s) (a := a) hi hxS

/-- With fewer than `q` indexed unit weights, the number of attainable
subset sums is at least one more than the number of weights. -/
theorem card_add_one_le_indexedSubsetSums
    {q : ℕ} [NeZero q]
    {ι : Type*} (s : Finset ι) (a : ι → ZMod q)
    (hcard : s.card < q)
    (ha : ∀ i ∈ s, IsUnit (a i)) :
    s.card + 1 ≤ (indexedSubsetSums s a).card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : 0 ∈ indexedSubsetSums (∅ : Finset ι) a :=
        zero_mem_indexedSubsetSums ∅ a
      simpa using (Finset.card_pos.mpr ⟨0, hz⟩)
  | @insert i s hi ih =>
      have hsmall : s.card < q := by
        rw [Finset.card_insert_of_notMem hi] at hcard
        omega
      have hih : s.card + 1 ≤ (indexedSubsetSums s a).card :=
        ih hsmall (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      by_cases hfull : indexedSubsetSums s a = Finset.univ
      · have hmono :
            indexedSubsetSums s a ⊆
              indexedSubsetSums (insert i s) a :=
          indexedSubsetSums_mono (Finset.subset_insert i s)
        have hnew :
            indexedSubsetSums (insert i s) a = Finset.univ := by
          apply Finset.eq_univ_iff_forall.mpr
          intro x
          apply hmono
          simpa [hfull]
        have htarget :
            (indexedSubsetSums (insert i s) a).card = q := by
          rw [hnew]
          simpa only [Finset.card_univ] using (ZMod.card q)
        calc
          (insert i s).card + 1 ≤ q := Nat.succ_le_of_lt hcard
          _ = (indexedSubsetSums (insert i s) a).card := htarget.symm
      · have hgrow :
            (indexedSubsetSums s a).card <
              (indexedSubsetSums (insert i s) a).card :=
          card_indexedSubsetSums_lt_insert_of_isUnit
            hi hfull (ha i (Finset.mem_insert_self i s))
        calc
          (insert i s).card + 1 = (s.card + 1) + 1 := by
            rw [Finset.card_insert_of_notMem hi]
          _ ≤ (indexedSubsetSums s a).card + 1 :=
            Nat.add_le_add_right hih 1
          _ ≤ (indexedSubsetSums (insert i s) a).card :=
            Nat.succ_le_of_lt hgrow

/-- Exactly `q - 1` indexed unit weights in `ZMod q` have every residue as
a subset sum. -/
theorem indexedSubsetSums_eq_univ_of_card_add_one
    {q : ℕ} [NeZero q]
    {ι : Type*} (s : Finset ι) (a : ι → ZMod q)
    (hcard : s.card + 1 = q)
    (ha : ∀ i ∈ s, IsUnit (a i)) :
    indexedSubsetSums s a = Finset.univ := by
  have hlt : s.card < q := by omega
  have hlower :=
    card_add_one_le_indexedSubsetSums s a hlt ha
  have hupper0 :
      (indexedSubsetSums s a).card ≤ Fintype.card (ZMod q) :=
    Finset.card_le_univ _
  have hupper :
      (indexedSubsetSums s a).card ≤ q := by
    simpa only [ZMod.card] using hupper0
  have heq : (indexedSubsetSums s a).card = q := by
    omega
  apply Finset.eq_univ_of_card
  simpa only [ZMod.card] using heq

/-- An odd natural number is a unit modulo a power of two. -/
theorem isUnit_zmod_two_pow_of_odd
    {k n : ℕ} (hn : Odd n) :
    IsUnit (n : ZMod (2 ^ k)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact hn.coprime_two_right.pow_right k

/-- Manuscript Lemma `pre-banana-subset-sums`, in indexed form.

If `q = 2^k` and there are `q-1` odd weights, their subset sums cover
`Z/qZ`. -/
theorem odd_indexedSubsetSums_two_pow_eq_univ
    {k : ℕ} {ι : Type*}
    (s : Finset ι) (a : ι → ℕ)
    (hcard : s.card + 1 = 2 ^ k)
    (ha : ∀ i ∈ s, Odd (a i)) :
    indexedSubsetSums s (fun i => (a i : ZMod (2 ^ k))) = Finset.univ := by
  have hpos : 0 < (2 : ℕ) ^ k := pow_pos (by decide) _
  letI : NeZero (2 ^ k) := ⟨Nat.ne_of_gt hpos⟩
  apply indexedSubsetSums_eq_univ_of_card_add_one s
    (fun i => (a i : ZMod (2 ^ k))) hcard
  intro i hi
  exact isUnit_zmod_two_pow_of_odd (ha i hi)

end SuccessorTree.NonPrecompact

import SuccessorTree.NonPrecompact.SubsetSums
import SuccessorTree.NonPrecompact.ColouringWrappers

/-!
# Nonempty odd subset sums for pre-BANANA residue realisation

The circulation proof of the pre-BANANA finite-residue realisation lemma
needs a strengthening of the basic subset-sum theorem.  With exactly
`q = 2^k` odd weights, every residue modulo `q` is represented by a
nonempty subset.

For a nonzero target residue, apply the existing `q-1` theorem after
reserving one weight; the empty subset cannot realise a nonzero residue.
For the zero residue, use the reserved weight and choose a subset of the
remaining weights which cancels it.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators


/-- The mod-two reduction of a sum of odd integer weights is the parity of
the number of selected weights.  This is the finite parity bridge used when
pre-BANANA residue blocks are turned into marked blocks. -/
theorem residueParityHom_sum_eq_card_of_odd
    {k : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℕ)
    (ha : ∀ i ∈ s, Odd (a i)) :
    residueParityHom k
        (∑ i ∈ s, (a i : ZMod (2 ^ (k + 1)))) =
      (s.card : F2) := by
  calc
    residueParityHom k
        (∑ i ∈ s, (a i : ZMod (2 ^ (k + 1)))) =
        ∑ i ∈ s, residueParityHom k
          (a i : ZMod (2 ^ (k + 1))) := by
      exact map_sum (residueParityHom k)
        (fun i => (a i : ZMod (2 ^ (k + 1)))) s
    _ = ∑ i ∈ s, (1 : F2) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa [residueParityHom] using
        (ha i hi).natCast_zmod_two
    _ = (s.card : F2) := by
      simp

/-- If a block of odd weights has prescribed residue, the parity of the
block cardinality is the parity of that residue. -/
theorem card_parity_eq_residueParityHom_of_odd_sum
    {k : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℕ)
    (ha : ∀ i ∈ s, Odd (a i))
    (r : ZMod (2 ^ (k + 1)))
    (hsum :
      (∑ i ∈ s, (a i : ZMod (2 ^ (k + 1)))) = r) :
    (s.card : F2) = residueParityHom k r := by
  rw [← hsum]
  exact (residueParityHom_sum_eq_card_of_odd s a ha).symm

/-- Exactly `2^k` odd weights have a nonempty subset with any prescribed
sum modulo `2^k`. -/
theorem exists_nonempty_odd_subset_sum_two_pow
    {k : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℕ)
    (hcard : s.card = 2 ^ k)
    (ha : ∀ i ∈ s, Odd (a i))
    (r : ZMod (2 ^ k)) :
    ∃ t : Finset ι,
      t.Nonempty ∧ t ⊆ s ∧
        (∑ i ∈ t, (a i : ZMod (2 ^ k))) = r := by
  have hqpos : 0 < 2 ^ k := pow_pos (by decide) _
  have hspos : 0 < s.card := by
    rw [hcard]
    exact hqpos
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hspos

  let u : Finset ι := s.erase j

  have hucard : u.card + 1 = 2 ^ k := by
    dsimp [u]
    rw [Finset.card_erase_add_one hj]
    exact hcard

  have hua : ∀ i ∈ u, Odd (a i) := by
    intro i hi
    exact ha i (Finset.mem_of_mem_erase hi)

  have hfull :=
    odd_indexedSubsetSums_two_pow_eq_univ
      (s := u) (a := a) hucard hua

  have chooseSubset
      (z : ZMod (2 ^ k)) :
      ∃ t : Finset ι,
        t ⊆ u ∧
          (∑ i ∈ t, (a i : ZMod (2 ^ k))) = z := by
    have hz :
        z ∈ indexedSubsetSums u
          (fun i => (a i : ZMod (2 ^ k))) := by
      rw [hfull]
      simp
    exact
      (mem_indexedSubsetSums_iff.mp hz)

  by_cases hr : r = 0
  · obtain ⟨t, htu, hsum⟩ :=
      chooseSubset (-(a j : ZMod (2 ^ k)))
    have hjnot : j ∉ t := by
      intro hjt
      exact (Finset.mem_erase.mp (htu hjt)).1 rfl
    refine ⟨insert j t, ?_, ?_, ?_⟩
    · exact ⟨j, Finset.mem_insert_self j t⟩
    · rw [Finset.insert_subset_iff]
      exact ⟨hj, htu.trans (Finset.erase_subset _ _)⟩
    · rw [hr, Finset.sum_insert hjnot, hsum]
      simp
  · obtain ⟨t, htu, hsum⟩ := chooseSubset r
    have htne : t ≠ ∅ := by
      intro ht
      subst t
      simp at hsum
      exact hr hsum.symm
    refine ⟨t, Finset.nonempty_iff_ne_empty.mpr htne,
      htu.trans (Finset.erase_subset _ _), hsum⟩


/-- Simultaneously choose a nonempty residue-correct subset from each
power-of-two batch of odd weights. -/
theorem exists_nonempty_odd_subset_sum_family
    {k m : ℕ} {ι : Type*} [DecidableEq ι]
    (batch : Fin m → Finset ι) (a : ι → ℕ)
    (hcard : ∀ i, (batch i).card = 2 ^ k)
    (ha : ∀ i x, x ∈ batch i → Odd (a x))
    (r : Fin m → ZMod (2 ^ k)) :
    ∃ chosen : Fin m → Finset ι,
      ∀ i,
        (chosen i).Nonempty ∧
        chosen i ⊆ batch i ∧
        (∑ x ∈ chosen i, (a x : ZMod (2 ^ k))) = r i := by
  have hchoice :
      ∀ i : Fin m,
        ∃ t : Finset ι,
          t.Nonempty ∧
          t ⊆ batch i ∧
          (∑ x ∈ t, (a x : ZMod (2 ^ k))) = r i := by
    intro i
    exact exists_nonempty_odd_subset_sum_two_pow
      (batch i) a (hcard i) (fun x hx => ha i x hx) (r i)
  choose chosen hchosen using hchoice
  exact ⟨chosen, hchosen⟩


/-- If selected atoms have the complementary residue to the target, then the
unselected atoms have the target residue.  A nonempty reserved set disjoint
from the selected atoms guarantees that the leftover block is nonempty. -/
theorem leftover_nonempty_and_sum_eq
    {q : ℕ} {ι : Type*} [DecidableEq ι]
    (atoms selected reserved : Finset ι)
    (weight : ι → ZMod q)
    (target : ZMod q)
    (hselected : selected ⊆ atoms)
    (hreserved : reserved.Nonempty)
    (hreservedAtoms : reserved ⊆ atoms)
    (hdisj : Disjoint reserved selected)
    (htotal : (∑ x ∈ atoms, weight x) = 0)
    (htarget : (∑ x ∈ selected, weight x) + target = 0) :
    (atoms \ selected).Nonempty ∧
      (∑ x ∈ atoms \ selected, weight x) = target := by
  constructor
  · obtain ⟨x, hx⟩ := hreserved
    refine ⟨x, Finset.mem_sdiff.mpr ⟨hreservedAtoms hx, ?_⟩⟩
    intro hxs
    exact (Finset.disjoint_left.mp hdisj) hx hxs
  · have hsplit :
        (∑ x ∈ atoms \ selected, weight x) +
            (∑ x ∈ selected, weight x) = 0 := by
      rw [Finset.sum_sdiff hselected]
      exact htotal
    have hsplit' :
        (∑ x ∈ selected, weight x) +
            (∑ x ∈ atoms \ selected, weight x) = 0 := by
      simpa [add_comm] using hsplit
    apply add_left_cancel
    exact hsplit'.trans htarget.symm


/-- Assemble the residue-correct batch choices into disjoint blocks, with all
remaining atoms forming one final nonempty block of the prescribed residue.

This is the finite bookkeeping step in the manuscript's pre-BANANA residue
realisation lemma.  The batches are the disjoint q-atom batches, while
the reserved set consists of atoms intentionally left for the final block. -/
theorem exists_prebanana_residue_block_assembly
    {k m : ℕ} {ι : Type*} [DecidableEq ι]
    (atoms reserved : Finset ι)
    (batch : Fin m → Finset ι)
    (a : ι → ℕ)
    (r : Fin m → ZMod (2 ^ k))
    (last : ZMod (2 ^ k))
    (hcard : ∀ i, (batch i).card = 2 ^ k)
    (ha : ∀ i x, x ∈ batch i → Odd (a x))
    (hbatchAtoms : ∀ i, batch i ⊆ atoms)
    (hbatchDisjoint :
      (Set.univ : Set (Fin m)).PairwiseDisjoint batch)
    (hreserved : reserved.Nonempty)
    (hreservedAtoms : reserved ⊆ atoms)
    (hreservedDisjoint : ∀ i, Disjoint reserved (batch i))
    (htotal :
      (∑ x ∈ atoms, (a x : ZMod (2 ^ k))) = 0)
    (hrsum : (∑ i, r i) + last = 0) :
    ∃ chosen : Fin m → Finset ι,
      let selected :=
        (Finset.univ : Finset (Fin m)).biUnion chosen
      (∀ i,
          (chosen i).Nonempty ∧
          chosen i ⊆ batch i ∧
          (∑ x ∈ chosen i, (a x : ZMod (2 ^ k))) = r i) ∧
      (Set.univ : Set (Fin m)).PairwiseDisjoint chosen ∧
      selected ⊆ atoms ∧
      Disjoint reserved selected ∧
      (atoms \ selected).Nonempty ∧
      (∑ x ∈ atoms \ selected, (a x : ZMod (2 ^ k))) = last := by
  obtain ⟨chosen, hchosen⟩ :=
    exists_nonempty_odd_subset_sum_family
      batch a hcard ha r

  let selected : Finset ι :=
    (Finset.univ : Finset (Fin m)).biUnion chosen

  have hchosenDisjoint :
      (Set.univ : Set (Fin m)).PairwiseDisjoint chosen := by
    intro i hi j hj hij
    exact
      (hbatchDisjoint hi hj hij).mono
        (hchosen i).2.1 (hchosen j).2.1

  have hselectedAtoms : selected ⊆ atoms := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
    exact hbatchAtoms i ((hchosen i).2.1 hxi)

  have hreservedSelected : Disjoint reserved selected := by
    rw [Finset.disjoint_left]
    intro x hxr hxs
    rcases Finset.mem_biUnion.mp hxs with ⟨i, hi, hxi⟩
    exact
      (Finset.disjoint_left.mp (hreservedDisjoint i))
        hxr ((hchosen i).2.1 hxi)

  have hchosenDisjointFinset :
      ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
        chosen := by
    simpa using hchosenDisjoint

  have hsumSelected :
      (∑ x ∈ selected, (a x : ZMod (2 ^ k))) =
        ∑ i, r i := by
    dsimp [selected]
    rw [Finset.sum_biUnion hchosenDisjointFinset]
    apply Finset.sum_congr rfl
    intro i hi
    exact (hchosen i).2.2

  have htarget :
      (∑ x ∈ selected, (a x : ZMod (2 ^ k))) + last = 0 := by
    rw [hsumSelected]
    exact hrsum

  obtain ⟨hleftNonempty, hleftSum⟩ :=
    leftover_nonempty_and_sum_eq
      atoms selected reserved
      (fun x => (a x : ZMod (2 ^ k))) last
      hselectedAtoms hreserved hreservedAtoms
      hreservedSelected htotal htarget

  refine ⟨chosen, ?_⟩
  dsimp
  refine ⟨hchosen, hchosenDisjoint, ?_, ?_, hleftNonempty, hleftSum⟩
  · exact hselectedAtoms
  · exact hreservedSelected

end SuccessorTree.NonPrecompact

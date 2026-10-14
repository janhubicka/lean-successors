import SuccessorTree.V10.BlockOrder
import SuccessorTree.V10.MeetBundle

/-!
# Classifying a first positive disagreement of the complete binary trace

Unlike the earlier one-block lemmas, the main theorem below does not assume
which original has the smaller generation, that the disagreement occurs at
that generation, or that its block precedes both originals. It derives these
facts from agreement at every earlier real coordinate and the exact H trace
formula. The language may have no binary symbols (`d = 0`).

This is still a trace theorem, not the manuscript's partial-type meet lemma:
the adapter must identify a nontrivial meet with a first trace disagreement,
using the common root and socle, the E convention and empty fake coordinates.
-/

namespace SuccessorTree.V10

/-- The empty tuple of directed binary relations. -/
def emptyBinaryPattern (d : Nat) : Fin d → Bool := fun _ => false

private theorem bundledTrace_copied
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i n u q : Nat) (hui : u < i)
    (hgate : q < n ∨ (q = n ∧ n = k)) :
    bundledTrace B k i n u q = B u i := by
  funext a
  simp [bundledTrace, traceBit, hui, hgate]

private theorem bundledTrace_empty
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i n u q : Nat)
    (hgate : ¬ (u < i ∧ (q < n ∨ (q = n ∧ n = k)))) :
    bundledTrace B k i n u q = emptyBinaryPattern d := by
  funext a
  simp [bundledTrace, traceBit, hgate, emptyBinaryPattern]

private theorem bundledTrace_empty_of_pair
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i n u q : Nat) (hpair : B u i = emptyBinaryPattern d) :
    bundledTrace B k i n u q = emptyBinaryPattern d := by
  funext a
  have ha : B u i a = false := congrFun hpair a
  simp [bundledTrace, traceBit, ha, emptyBinaryPattern]

/-- A positive-generation original whose trace is empty at the start of a
block has empty trace throughout that block. -/
theorem bundledTrace_empty_of_zero
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i n u q : Nat) (hn : 0 < n)
    (hzero : bundledTrace B k i n u 0 = emptyBinaryPattern d) :
    bundledTrace B k i n u q = emptyBinaryPattern d := by
  by_cases hui : u < i
  · have hcopy := bundledTrace_copied B k i n u 0 hui (Or.inl hn)
    exact bundledTrace_empty_of_pair B k i n u q (hcopy.symm.trans hzero)
  · exact bundledTrace_empty B k i n u q (by simp [hui])

/-- The first block with any nonempty directed binary relation to an original. -/
def FirstBinaryNeighbour {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (i p : Nat) : Prop :=
  p < i ∧ (∃ a : Fin d, B p i a = true) ∧
    ∀ u < p, ∀ a : Fin d, B u i a = false

/-- Agreement at coordinate zero and a later disagreement already force the
block to precede both originals and carry the same nonempty base pattern. -/
theorem positiveDisagreement_commonPair
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j m n p r : Nat) (hm : 0 < m) (hn : 0 < n)
    (hzero : bundledTrace B k i n p 0 = bundledTrace B k j m p 0)
    (hdiff : bundledTrace B k i n p r ≠ bundledTrace B k j m p r) :
    p < i ∧ p < j ∧ B p i = B p j ∧ B p i ≠ emptyBinaryPattern d := by
  have hnonempty : bundledTrace B k i n p 0 ≠ emptyBinaryPattern d := by
    intro hi
    have hj := hzero.symm.trans hi
    exact hdiff ((bundledTrace_empty_of_zero B k i n p r hn hi).trans
      (bundledTrace_empty_of_zero B k j m p r hm hj).symm)
  have hpi : p < i := by
    by_contra hpi
    exact hnonempty (bundledTrace_empty B k i n p 0 (by simp [hpi]))
  have hpj : p < j := by
    by_contra hpj
    exact hnonempty (hzero.trans
      (bundledTrace_empty B k j m p 0 (by simp [hpj])))
  have hi := bundledTrace_copied B k i n p 0 hpi (Or.inl hn)
  have hj := bundledTrace_copied B k j m p 0 hpj (Or.inl hm)
  refine ⟨hpi, hpj, hi.symm.trans (hzero.trans hj), ?_⟩
  intro h
  exact hnonempty (hi.trans h)

private theorem firstPositiveDisagreement_mixed
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j m n p r : Nat)
    (hpi : p < i) (hpj : p < j) (hmn : m < n) (hnk : n ≤ k)
    (hpair : B p i = B p j) (hne : B p i ≠ emptyBinaryPattern d)
    (hbefore : ∀ u q : Nat, q ≤ k →
      hPosition k u q < hPosition k p r →
      bundledTrace B k i n u q = bundledTrace B k j m u q)
    (hdiff : bundledTrace B k i n p r ≠ bundledTrace B k j m p r) :
    r = m ∧ FirstBinaryNeighbour B i p := by
  have hmk : m < k := lt_of_lt_of_le hmn hnk
  have hmle : m ≤ k := Nat.le_of_lt hmk
  have hrge : m ≤ r := by
    by_contra h
    have hrm : r < m := by omega
    have hi := bundledTrace_copied B k i n p r hpi (Or.inl (lt_trans hrm hmn))
    have hj := bundledTrace_copied B k j m p r hpj (Or.inl hrm)
    exact hdiff (hi.trans (hpair.trans hj.symm))
  have hdiffm : bundledTrace B k i n p m ≠ bundledTrace B k j m p m := by
    have hi := bundledTrace_copied B k i n p m hpi (Or.inl hmn)
    have hj := bundledTrace_empty B k j m p m (by omega)
    intro h
    exact hne (hi.symm.trans (h.trans hj))
  have hrle : r ≤ m := by
    by_contra h
    have hmr : m < r := by omega
    exact hdiffm (hbefore p m hmle (hPosition_lt_of_gen_lt k p m r hmr))
  have hrm : r = m := by omega
  have hearlier : ∀ u < p,
      bundledTrace B k i n u m = bundledTrace B k j m u m := by
    intro u hu
    exact hbefore u m hmle (hPosition_lt_of_block_lt k u p m r hmle hu)
  obtain ⟨hex, hfirst⟩ :=
    bundledPositiveMismatch_firstNeighbour B k i j m n p
      hmn hmk hearlier hdiffm
  refine ⟨hrm, hpi, hex, ?_⟩
  intro u hu a
  exact hfirst u hu (lt_trans hu hpi) a

/-- A first positive disagreement determines its generation and its charge.
No common-neighbour, source-block, or unequal-generation premise is assumed.
The special top-generation gate is included by `traceBit` itself. -/
theorem firstPositiveDisagreement_classifies
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j m n p r : Nat)
    (hm : 0 < m) (hn : 0 < n) (hmk : m ≤ k) (hnk : n ≤ k)
    (hr : 0 < r)
    (hbefore : ∀ u q : Nat, q ≤ k →
      hPosition k u q < hPosition k p r →
      bundledTrace B k i n u q = bundledTrace B k j m u q)
    (hdiff : bundledTrace B k i n p r ≠ bundledTrace B k j m p r) :
    p < i ∧ p < j ∧
      ((r = m ∧ m < n ∧ FirstBinaryNeighbour B i p) ∨
       (r = n ∧ n < m ∧ FirstBinaryNeighbour B j p)) := by
  have hzero := hbefore p 0 (Nat.zero_le k)
    (hPosition_lt_of_gen_lt k p 0 r hr)
  obtain ⟨hpi, hpj, hpair, hne⟩ :=
    positiveDisagreement_commonPair B k i j m n p r hm hn hzero hdiff
  refine ⟨hpi, hpj, ?_⟩
  rcases lt_trichotomy m n with hmn | heq | hnm
  · obtain ⟨hrm, hfirst⟩ := firstPositiveDisagreement_mixed
      B k i j m n p r hpi hpj hmn hnk hpair hne hbefore hdiff
    exact Or.inl ⟨hrm, hmn, hfirst⟩
  · subst n
    apply False.elim
    apply hdiff
    funext a
    have heq := congrFun hpair a
    simp [bundledTrace, traceBit, hpi, hpj, heq]
  · have hne' : B p j ≠ emptyBinaryPattern d := by
      intro h
      exact hne (hpair.trans h)
    obtain ⟨hrn, hfirst⟩ := firstPositiveDisagreement_mixed
      B k j i n m p r hpj hpi hnm hmk hpair.symm hne'
      (by intro u q hq hpos; exact (hbefore u q hq hpos).symm)
      (Ne.symm hdiff)
    exact Or.inr ⟨hrn, hnm, hfirst⟩

end SuccessorTree.V10

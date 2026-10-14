import SuccessorTree.V10.HDirectedTraces

/-!
# First incident neighbour from the complete numerical H binary type

Keep both ordered directions of every binary symbol in one finite tuple.
The first-disagreement classifier can then detect an incident pair even
when only the reverse relation is present. The main numerical theorem
uses actual H atoms at every earlier coordinate, and requires the proposed
coordinate to belong to BOTH exact generated E-socles. It derives the
strict lower-block guard, rather than weakening it to p < j.

This is a theorem about the exact numerical H model. It does not assert
that the original manuscript's one-way substructure clause already defines
that model, or identify a numerical disagreement with a Kpt meet.
-/

namespace SuccessorTree.V10

/-- Concatenate both ordered binary tuples, without a symmetry assumption. -/
def bidirectionalBits {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (u v : Nat) (s : Fin (d + d)) : Bool :=
  if h : s.val < d then B u v ⟨s.val, h⟩
  else B v u ⟨s.val - d, by have := s.isLt; omega⟩

@[simp] theorem bidirectionalBits_left
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (u v : Nat) (a : Fin d) :
    bidirectionalBits B u v ⟨a.val, by have := a.isLt; omega⟩ =
      B u v a := by
  simp [bidirectionalBits, a.isLt]

@[simp] theorem bidirectionalBits_right
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (u v : Nat) (a : Fin d) :
    bidirectionalBits B u v ⟨d + a.val, by have := a.isLt; omega⟩ =
      B v u a := by
  have h : ¬ d + a.val < d := by omega
  simp [bidirectionalBits, h]

/-- Nonemptiness means that some binary relation holds in either direction. -/
theorem bidirectionalBits_nonempty_iff
    {d : Nat} (B : Nat → Nat → Fin d → Bool) (u v : Nat) :
    (∃ s, bidirectionalBits B u v s = true) ↔
      ∃ a, B u v a = true ∨ B v u a = true := by
  constructor
  · rintro ⟨s, hs⟩
    by_cases h : s.val < d
    · exact ⟨⟨s.val, h⟩, Or.inl (by
        simpa [bidirectionalBits, h] using hs)⟩
    · exact ⟨⟨s.val - d, by have := s.isLt; omega⟩, Or.inr (by
        simpa [bidirectionalBits, h] using hs)⟩
  · rintro ⟨a, ha | ha⟩
    · refine ⟨⟨a.val, by have := a.isLt; omega⟩, ?_⟩
      simpa using ha
    · refine ⟨⟨d + a.val, by have := a.isLt; omega⟩, ?_⟩
      simpa using ha

/-- The empty tuple excludes every directed relation, not just forward ones. -/
theorem bidirectionalBits_all_false_iff
    {d : Nat} (B : Nat → Nat → Fin d → Bool) (u v : Nat) :
    (∀ s, bidirectionalBits B u v s = false) ↔
      ∀ a, B u v a = false ∧ B v u a = false := by
  constructor
  · intro h a
    constructor
    · simpa using h ⟨a.val, by have := a.isLt; omega⟩
    · simpa using h ⟨d + a.val, by have := a.isLt; omega⟩
  · intro h s
    by_cases hs : s.val < d
    · simpa [bidirectionalBits, hs] using (h ⟨s.val, hs⟩).1
    · simpa [bidirectionalBits, hs] using
        (h ⟨s.val - d, by have := s.isLt; omega⟩).2

/-- This is precisely the least incident base neighbour used for p(i). -/
theorem firstBidirectionalNeighbour_iff
    {d : Nat} (B : Nat → Nat → Fin d → Bool) (i p : Nat) :
    FirstBinaryNeighbour (bidirectionalBits B) i p ↔
      p < i ∧ (∃ a, B p i a = true ∨ B i p a = true) ∧
        ∀ u < p, ∀ a, B u i a = false ∧ B i u a = false := by
  simp only [FirstBinaryNeighbour, bidirectionalBits_nonempty_iff,
    bidirectionalBits_all_false_iff]

/-- The actual numerical H atoms, in both orientations, are one bundled
trace of the corresponding complete base tuple. Absent atoms are retained. -/
theorem hNumericBinary_bidirectional_matches_trace
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k u i q n : Nat) (hui : u < i) (hq : q ≤ k) (hn : n ≤ k) :
    bidirectionalBits (hNumericBinary B k)
        (hPosition k u q) (hPosition k i n) =
      bundledTrace (bidirectionalBits B) k i n u q := by
  funext s
  by_cases hs : s.val < d
  · have h := congrFun
      (hNumericBinary_forward_matches_bundledTrace B k u i q n hui hq hn)
      ⟨s.val, hs⟩
    simpa [bidirectionalBits, bundledTrace, traceBit, hs] using h
  · have h := congrFun
      (hNumericBinary_reverse_matches_bundledTrace B k u i q n hui hq hn)
      ⟨s.val - d, by have := s.isLt; omega⟩
    simpa [bidirectionalBits, bundledTrace, traceBit, hs] using h

/-- Odd fake coordinates cannot be the first binary disagreement. -/
theorem hNumericBinary_odd_bidirectional_empty
    {d : Nat} (B : Nat → Nat → Fin d → Bool) (k a y : Nat) :
    bidirectionalBits (hNumericBinary B k) (2 * a + 1) y =
      emptyBinaryPattern (d + d) := by
  funext s
  by_cases hs : s.val < d
  · simp [bidirectionalBits, hs, emptyBinaryPattern,
      hNumericBinary_odd_left_false]
  · simp [bidirectionalBits, hs, emptyBinaryPattern,
      hNumericBinary_odd_right_false]

/-- A real coordinate in an exact E-socle lies in an earlier base block.
This is derived from the generators, not postulated as a trace premise. -/
theorem generatedE_real_before_source
    (k i n p r : Nat)
    (h : generatedE k i n (hPosition k p r)) : p < i := by
  obtain ⟨u, q, hui, hq, _, hpos⟩ := h
  by_contra hpi
  have hup : u < p := by omega
  have hlt := hPosition_lt_of_block_lt k u p q r hq hup
  omega

/-- Classify a first positive-generation disagreement of the actual
numerical H binary tuples, including BOTH directions. The coordinate is
required to lie in both exact E-socles; consequently the smaller-generation
source has the sharp p+1 < j guard. Equal generations, including two top
generations, cannot give such a disagreement. -/
theorem hNumericBinary_first_positive_disagreement
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j m n p r : Nat)
    (hm : 0 < m) (hn : 0 < n) (hmk : m ≤ k) (hnk : n ≤ k)
    (hr : 0 < r) (hrk : r ≤ k)
    (hinI : generatedE k i n (hPosition k p r))
    (hinJ : generatedE k j m (hPosition k p r))
    (hbefore : ∀ x < hPosition k p r,
      bidirectionalBits (hNumericBinary B k) x (hPosition k i n) =
        bidirectionalBits (hNumericBinary B k) x (hPosition k j m))
    (hdiff : bidirectionalBits (hNumericBinary B k)
        (hPosition k p r) (hPosition k i n) ≠
      bidirectionalBits (hNumericBinary B k)
        (hPosition k p r) (hPosition k j m)) :
    p < i ∧ p < j ∧
      ((r = m ∧ m < n ∧ p + 1 < j ∧
          FirstBinaryNeighbour (bidirectionalBits B) i p) ∨
       (r = n ∧ n < m ∧ p + 1 < i ∧
          FirstBinaryNeighbour (bidirectionalBits B) j p)) := by
  have hpi := generatedE_real_before_source k i n p r hinI
  have hpj := generatedE_real_before_source k j m p r hinJ
  have htbefore : ∀ u q : Nat, q ≤ k →
      hPosition k u q < hPosition k p r →
      bundledTrace (bidirectionalBits B) k i n u q =
        bundledTrace (bidirectionalBits B) k j m u q := by
    intro u q hq hpos
    have hup : u ≤ p := by
      by_contra h
      have hpu : p < u := by omega
      have hlt := hPosition_lt_of_block_lt k p u r q hrk hpu
      omega
    have hui : u < i := lt_of_le_of_lt hup hpi
    have huj : u < j := lt_of_le_of_lt hup hpj
    calc
      bundledTrace (bidirectionalBits B) k i n u q =
          bidirectionalBits (hNumericBinary B k)
            (hPosition k u q) (hPosition k i n) :=
        (hNumericBinary_bidirectional_matches_trace B k u i q n hui hq hnk).symm
      _ = bidirectionalBits (hNumericBinary B k)
            (hPosition k u q) (hPosition k j m) := hbefore _ hpos
      _ = bundledTrace (bidirectionalBits B) k j m u q :=
        hNumericBinary_bidirectional_matches_trace B k u j q m huj hq hmk
  have htdiff : bundledTrace (bidirectionalBits B) k i n p r ≠
      bundledTrace (bidirectionalBits B) k j m p r := by
    intro h
    apply hdiff
    calc
      bidirectionalBits (hNumericBinary B k)
          (hPosition k p r) (hPosition k i n) =
          bundledTrace (bidirectionalBits B) k i n p r :=
        hNumericBinary_bidirectional_matches_trace B k p i r n hpi hrk hnk
      _ = bundledTrace (bidirectionalBits B) k j m p r := h
      _ = bidirectionalBits (hNumericBinary B k)
            (hPosition k p r) (hPosition k j m) :=
        (hNumericBinary_bidirectional_matches_trace B k p j r m hpj hrk hmk).symm
  obtain ⟨_, _, hcases⟩ := firstPositiveDisagreement_classifies
    (bidirectionalBits B) k i j m n p r hm hn hmk hnk hr htbefore htdiff
  refine ⟨hpi, hpj, ?_⟩
  rcases hcases with ⟨hrm, hmn, hfirst⟩ | ⟨hrn, hnm, hfirst⟩
  · have hm_lt_k : m < k := lt_of_lt_of_le hmn hnk
    have hcut := (generatedE_nonTop_iff k j m (hPosition k p m)
      (by omega) hm hm_lt_k).mp (by simpa [hrm] using hinJ)
    exact Or.inl ⟨hrm, hmn,
      positiveMeet_lowerBlock_guard k p j m hm hm_lt_k (by omega) hcut, hfirst⟩
  · have hn_lt_k : n < k := lt_of_lt_of_le hnm hmk
    have hcut := (generatedE_nonTop_iff k i n (hPosition k p n)
      (by omega) hn hn_lt_k).mp (by simpa [hrn] using hinI)
    exact Or.inr ⟨hrn, hnm,
      positiveMeet_lowerBlock_guard k p i n hn hn_lt_k (by omega) hcut, hfirst⟩

end SuccessorTree.V10

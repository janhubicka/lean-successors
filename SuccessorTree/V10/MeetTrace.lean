import Mathlib.Tactic

/-!
# One-block relation traces in the v10 H-construction

The v10 meet repair compares the relations of two original vertices to the
block indexed by an earlier base vertex. Here the order of blocks is still
external: these are *local trace identities*, not the global first-disagreement
or meet lemma from the paper.

For source vertex \`iota(i,n)\`, the relation to \`iota(u,q)\` is copied from
the base pair \`(u,i)\` exactly if \`u<i\` and \`q<n\`, or \`q=n=k\`.
This is the bit-valued abstraction of all binary relation symbols, including
their directions and diagonal data (the latter are fixed at the roots).
-/

namespace SuccessorTree
namespace V10

/-- A single binary-relation bit of a partial type against an earlier
generation coordinate in the explicit H-construction. -/
def traceBit (pairBit : Nat → Nat → Bool)
    (k source gen earlier level : Nat) : Bool :=
  if earlier < source ∧
      (level < gen ∨ (level = gen ∧ gen = k))
    then pairBit earlier source else false

/-- Before the smaller positive generation, the two types have the same
relation bit whenever their base pair bits agree. -/
theorem traceBit_before_smaller
    (pairBit : Nat → Nat → Bool)
    (k i j m n u q : Nat)
    (huj : u < j) (hui : u < i) (hqm : q < m)
    (hmn : m < n)
    (heq : pairBit u i = pairBit u j) :
    traceBit pairBit k i n u q = traceBit pairBit k j m u q := by
  have hi : u < i ∧ (q < n ∨ (q = n ∧ n = k)) :=
    ⟨hui, Or.inl (lt_trans hqm hmn)⟩
  have hj : u < j ∧ (q < m ∨ (q = m ∧ m = k)) :=
    ⟨huj, Or.inl hqm⟩
  simp [traceBit, hi, hj, heq]

/-- At exactly the smaller generation m, the higher-generation original
retains the nonempty base relation, while the lower-generation original
has no relation there, provided m<k. -/
theorem traceBit_first_positive_difference
    (pairBit : Nat → Nat → Bool)
    (k i j m n u : Nat)
    (hui : u < i) (huj : u < j)
    (hmn : m < n) (hmk : m < k)
    (hbit : pairBit u i = true) :
    traceBit pairBit k i n u m = true ∧
    traceBit pairBit k j m u m = false := by
  have hi : u < i ∧ (m < n ∨ (m = n ∧ n = k)) :=
    ⟨hui, Or.inl hmn⟩
  have hj : ¬ (u < j ∧ (m < m ∨ (m = m ∧ m = k))) := by
    omega
  constructor
  · simp [traceBit, hi, hbit]
  · simp [traceBit, hj]

/-- With equal positive generations, any differing base relation bit is
already visible at generation zero. This excludes a *first* difference
at a positive coordinate within such a block. -/
theorem traceBit_equal_generation_zero
    (pairBit : Nat → Nat → Bool)
    (k i j m u : Nat)
    (hui : u < i) (huj : u < j) (hmpos : 0 < m)
    (hneq : pairBit u i ≠ pairBit u j) :
    traceBit pairBit k i m u 0 ≠ traceBit pairBit k j m u 0 := by
  have hi : u < i ∧ (0 < m ∨ (0 = m ∧ m = k)) :=
    ⟨hui, Or.inl hmpos⟩
  have hj : u < j ∧ (0 < m ∨ (0 = m ∧ m = k)) :=
    ⟨huj, Or.inl hmpos⟩
  simpa [traceBit, hi, hj] using hneq

/-- At its own generation, a lower (non-top) original has no
relation to a preceding block, regardless of the base pair. -/
theorem traceBit_small_at_own
    (pairBit : Nat → Nat → Bool)
    (k j m u : Nat) (hmk : m < k) :
    traceBit pairBit k j m u m = false := by
  have hfalse : ¬ (m < m ∨ (m = m ∧ m = k)) := by omega
  simp [traceBit, hfalse]

/-- If an H-trace of generation n first differs from an H-trace of smaller
generation m at block p and level m, then p is the **first base
neighbour** of the higher original. The first-disagreement assumption
is deliberately explicit; proving it from the actual meet operation is
the remaining geometric part of manuscript Lemma 6.4x. -/
theorem positiveMismatch_firstNeighbour
    (pairBit : Nat → Nat → Bool)
    (k i j m n p : Nat)
    (hmn : m < n) (hmk : m < k)
    (hearlier : ∀ u < p,
      traceBit pairBit k i n u m =
        traceBit pairBit k j m u m)
    (hdiff : traceBit pairBit k i n p m ≠
      traceBit pairBit k j m p m) :
    p < i ∧ pairBit p i = true ∧
      (∀ u < p, u < i → pairBit u i = false) := by
  have hsmall : traceBit pairBit k j m p m = false :=
    traceBit_small_at_own pairBit k j m p hmk
  have hhigh : traceBit pairBit k i n p m = true := by
    cases hb : traceBit pairBit k i n p m with
    | false => simp [hb, hsmall] at hdiff
    | true => exact hb
  have hpi : p < i := by
    by_contra hno
    simp [traceBit, hno] at hhigh
  have hbit : pairBit p i = true := by
    simpa [traceBit, hpi, hmn] using hhigh
  refine ⟨hpi, hbit, ?_⟩
  intro u hu hui
  have hzero : traceBit pairBit k i n u m = false := by
    rw [hearlier u hu]
    exact traceBit_small_at_own pairBit k j m u hmk
  simpa [traceBit, hui, hmn] using hzero

end V10
end SuccessorTree

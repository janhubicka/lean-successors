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

end V10
end SuccessorTree

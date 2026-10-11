import SuccessorTree.V10.BlockOrder
import Mathlib.Tactic

/-!
# Truncation bound for positive-generation H meets

The reconstructed v10 manuscript gives the free level of the original
at \`iota(j,m)\`, for 0 < j and 0 < m < k, as

  iota(j-1,m-1) + 1.

The earlier meet-trace theorem locates a putative positive disagreement at
\`iota(p,m)\`. For this coordinate to occur in the *shorter partial type*,
it must be strictly below that free level. This is equivalent to
\`p+1<j\` (a sharper restriction than \`p<j\`).

The numerical equivalence below is unconditional. The paper still has to
prove that its E-socle and full partial-type prefix realize this free-level
formula, and that its first differing record occurs within both domains.
-/

namespace SuccessorTree.V10

/-- The free cut of an H-original in a positive non-top generation.
This matches the manuscript construction only under 0<j, 0<m<k. -/
def nonTopFreeCut (k j m : Nat) : Nat :=
  hPosition k (j - 1) (m - 1) + 1

/-- The positive first disagreement can occur *inside* the shorter
non-top partial type precisely when its block lies strictly before
the immediately preceding original block. -/
theorem positivePosition_below_free_iff
    (k p j m : Nat) (hm : 0 < m) (hmk : m < k) (hj : 0 < j) :
    hPosition k p m < nonTopFreeCut k j m ↔ p + 1 < j := by
  have htail :
      nonTopFreeCut k j m ≤ hPosition k (j - 1) m := by
    dsimp [nonTopFreeCut, hPosition]
    omega
  constructor
  · intro hpos
    by_contra hn
    have hp : j - 1 ≤ p := by omega
    have hblock : hPosition k (j - 1) m ≤ hPosition k p m := by
      unfold hPosition
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_left (2 * (k + 1)) hp) (2 * m)
    have hcontr : nonTopFreeCut k j m ≤ hPosition k p m :=
      htail.trans hblock
    exact (Nat.not_lt_of_ge hcontr) hpos
  · intro hp
    have hp' : p < j - 1 := by omega
    have hlt : hPosition k p m < hPosition k (j - 1) (m - 1) :=
      hPosition_lt_of_block_lt k p (j - 1) m (m - 1)
        (Nat.le_of_lt hmk) hp'
    dsimp [nonTopFreeCut]
    omega

/-- A positive first disagreement actually appearing in the lower
original's partial type has the stronger side condition p+1<j. -/
theorem positiveMeet_lowerBlock_guard
    (k p j m : Nat)
    (hm : 0 < m) (hmk : m < k) (hj : 0 < j)
    (hwithin : hPosition k p m < nonTopFreeCut k j m) :
    p + 1 < j :=
  (positivePosition_below_free_iff k p j m hm hmk hj).mp hwithin

end SuccessorTree.V10

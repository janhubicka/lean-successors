import SuccessorTree.V10.MeetTrace
import Mathlib.Tactic

/-!
# Positions of original vertices in the v10 H-construction

The manuscript uses `iota(i,m) = 2*(k+1)*i+2*m`. These lemmas link the
natural-number order of real vertices to lexicographic block/generation
order. In conjunction with `firstPositiveDisagreement_block`, they produce
an exact first positive disagreement *among real coordinates*. The odd fake
vertices have empty relations and must be handled in the final partial-type
adapter.
-/

namespace SuccessorTree
namespace V10

/-- Position of the generation-`g` original in block `i`. -/
def hPosition (k i g : Nat) : Nat := 2 * (k + 1) * i + 2 * g

private theorem lexCode_lt_of_block_lt
    (w i j q r : Nat) (hq : q < w) (hij : i < j) :
    w * i + q < w * j + r := by
  have hsmall : w * i + q < w * (i + 1) := by
    have h : w * i + q < w * i + w :=
      Nat.add_lt_add_left hq (w * i)
    simpa [Nat.mul_succ] using h
  have hblock : w * (i + 1) ≤ w * j :=
    Nat.mul_le_mul_left w (Nat.succ_le_of_lt hij)
  omega

/-- All positions in a lower block precede those in any higher block. -/
theorem hPosition_lt_of_block_lt
    (k i j q r : Nat)
    (hq : q ≤ k) (hij : i < j) :
    hPosition k i q < hPosition k j r := by
  have hsmall : 2 * q < 2 * (k + 1) := by omega
  exact lexCode_lt_of_block_lt (2 * (k + 1)) i j (2 * q) (2 * r)
    hsmall hij

/-- Within a fixed block, generation order is numeric order. -/
theorem hPosition_lt_of_gen_lt
    (k i q r : Nat) (hqr : q < r) :
    hPosition k i q < hPosition k i r := by
  unfold hPosition
  omega

/-- A real coordinate preceding the proposed meet has either an earlier
block or the same block with smaller generation. -/
theorem hPosition_before
    (k u q p m : Nat) (hq : q ≤ k) (hm : m ≤ k)
    (hpos : hPosition k u q < hPosition k p m) :
    u < p ∨ (u = p ∧ q < m) := by
  rcases lt_trichotomy u p with hu | heq | hp
  · exact Or.inl hu
  · right
    constructor
    · exact heq
    · rw [heq] at hpos
      unfold hPosition at hpos
      omega
  · have hreverse := hPosition_lt_of_block_lt k p u m q hm hp
    omega

/-- A first positive block disagreement from the H-structure formula is
indeed first in the natural enumeration of *all real* predecessors. -/
theorem firstPositiveDisagreement_realPositions
    (pairBit : Nat → Nat → Bool)
    (k i j m n p : Nat)
    (hpi : p < i) (hpj : p < j)
    (hmn : m < n) (hmk : m < k)
    (hfirstI : ∀ u < p, pairBit u i = false)
    (hfirstJ : ∀ u < p, pairBit u j = false)
    (hmatch : pairBit p i = pairBit p j)
    (hbit : pairBit p i = true) :
    (∀ u q : Nat, q ≤ k →
        hPosition k u q < hPosition k p m →
        traceBit pairBit k i n u q =
          traceBit pairBit k j m u q) ∧
    traceBit pairBit k i n p m ≠
      traceBit pairBit k j m p m := by
  obtain ⟨hbefore, hdiff⟩ :=
    firstPositiveDisagreement_block pairBit k i j m n p
      hpi hpj hmn hmk hfirstI hfirstJ hmatch hbit
  refine ⟨?_, hdiff⟩
  intro u q hq hpos
  exact hbefore u q
    (hPosition_before k u q p m hq (Nat.le_of_lt hmk) hpos)

end V10
end SuccessorTree

import SuccessorTree.V10.Counting
import Mathlib.Tactic

/-!
# Numerical induction in the v10 big-Ramsey upper bound

Proposition 6.44 uses the downward generation recurrence
  R(t) = sum_F (t+1)^|F|,
  a_k = q+1,
  M_r = sum_{s>r} a_s,
  a_r = M_r + R(M_r).

To avoid subtraction in recursion, index generations by *distance
from the top*: index j=0 corresponds to generation k; index j+1
corresponds to the next lower positive generation. The cumulative
budget is the sum of the first j+1 budgets.

The theorem below proves the entire CARDINAL INDUCTION from its
explicit stage hypotheses. It does not pretend the still-open
geometric I3 signature/generation assertions are proved.

The author's proof treats q=0 by an empty-envelope convention.
This module covers its nonempty q stage, and the trivial empty case
should be obtained from that convention rather than a false positive
lower bound for an empty set.
-/

namespace SuccessorTree.V10

/-- The exact finite-family signature count in the manuscript,
with a forbidden-pattern arity assigned to each family member. -/
def ageSignatureCapacity {k : Nat}
    (sizes : Fin k → Nat) (M : Nat) : Nat :=
  ∑ i : Fin k, (M + 1) ^ (sizes i)

/-- Signature capacity is nondecreasing in the number of
higher-generation originals. -/
theorem ageSignatureCapacity_mono {k : Nat}
    (sizes : Fin k → Nat) :
    Monotone (ageSignatureCapacity sizes) := by
  intro a b hab
  unfold ageSignatureCapacity
  apply Finset.sum_le_sum
  intro i hi
  exact pow_le_pow_left₀ (by omega : (0 : Nat) ≤ a+1)
    (by omega : a+1 ≤ b+1) (sizes i)

/-- Sum of the per-generation budgets from the highest generation
down through generation-distance j. The successor equation uses
a_(next) = M + R(M), where M is the sum of all higher budgets. -/
def descendingCumulativeBudget
    (R : Nat → Nat) (q : Nat) : Nat → Nat
  | 0 => q + 1
  | j + 1 =>
      2 * descendingCumulativeBudget R q j +
        R (descendingCumulativeBudget R q j)

/-- The manuscript's a_k, a_(k-1), ... in descending order. -/
def descendingLevelBudget
    (R : Nat → Nat) (q : Nat) : Nat → Nat
  | 0 => q + 1
  | j + 1 =>
      descendingCumulativeBudget R q j +
        R (descendingCumulativeBudget R q j)

/-- The cumulative budget is precisely the sum of its per-level
budgets, not an independent overestimate. -/
theorem descendingCumulativeBudget_succ
    (R : Nat → Nat) (q j : Nat) :
    descendingCumulativeBudget R q (j+1) =
      descendingCumulativeBudget R q j +
        descendingLevelBudget R q (j+1) := by
  simp only [descendingCumulativeBudget, descendingLevelBudget]
  omega

theorem descendingCumulativeBudget_eq_sum
    (R : Nat → Nat) (q j : Nat) :
    descendingCumulativeBudget R q j =
      ∑ i ∈ Finset.range (j+1), descendingLevelBudget R q i := by
  induction j with
  | zero =>
      simp [descendingCumulativeBudget, descendingLevelBudget]
  | succ j ih =>
      rw [descendingCumulativeBudget_succ, ih]
      simp [Finset.sum_range_succ]

/-- The manuscript's complete numerical induction: if the top-level
originals number at most q+1, and each successive lower generation
has at most M+R(M) selected originals, with M the number in all higher
generations, then every generation is bounded by a_j and their sum
by the cumulative budget.

This is a theorem for actual finite SETS at each generation; it
does not assume those sets are disjoint, so it remains valid when
different levels contain overlapping original addresses. -/
theorem descendingGenerationCardinalityInduction
    {α : Type*} [DecidableEq α]
    (R : Nat → Nat) (hMono : Monotone R)
    (q : Nat)
    (levelOriginals : Nat → Finset α)
    (hTop : (levelOriginals 0).card ≤ q+1)
    (hLower : ∀ j : Nat,
      let M := ∑ i ∈ Finset.range (j+1), (levelOriginals i).card
      (levelOriginals (j+1)).card ≤ M + R M) :
    ∀ j : Nat,
      (levelOriginals j).card ≤ descendingLevelBudget R q j ∧
      (∑ i ∈ Finset.range (j+1), (levelOriginals i).card) ≤
        descendingCumulativeBudget R q j := by
  intro j
  induction j with
  | zero =>
      constructor
      · simpa [descendingLevelBudget] using hTop
      · simpa [descendingCumulativeBudget] using hTop
  | succ j ih =>
      obtain ⟨_hPreviousLevel,hPreviousSum⟩ := ih
      let M := ∑ i ∈ Finset.range (j+1), (levelOriginals i).card
      have hR : R M ≤ R (descendingCumulativeBudget R q j) :=
        hMono hPreviousSum
      have hNext :
          (levelOriginals (j+1)).card ≤
            descendingLevelBudget R q (j+1) := by
        calc
          (levelOriginals (j+1)).card ≤ M + R M := hLower j
          _ ≤ descendingCumulativeBudget R q j +
              R (descendingCumulativeBudget R q j) :=
              Nat.add_le_add hPreviousSum hR
          _ = descendingLevelBudget R q (j+1) := rfl
      refine ⟨hNext,?_⟩
      rw [Finset.sum_range_succ]
      calc
        (∑ i ∈ Finset.range (j+1), (levelOriginals i).card) +
            (levelOriginals (j+1)).card ≤
          descendingCumulativeBudget R q j +
            descendingLevelBudget R q (j+1) :=
              Nat.add_le_add hPreviousSum hNext
        _ = descendingCumulativeBudget R q (j+1) :=
              (descendingCumulativeBudget_succ R q j).symm

/-- Substitute the paper's concrete signature polynomial into the
numerical induction, retaining exactly its q+1 and M+R(M) bounds. -/
theorem descendingGenerationCardinalityInduction_signature
    {α : Type*} [DecidableEq α]
    {k : Nat} (sizes : Fin k → Nat) (q : Nat)
    (levelOriginals : Nat → Finset α)
    (hTop : (levelOriginals 0).card ≤ q+1)
    (hLower : ∀ j : Nat,
      let M := ∑ i ∈ Finset.range (j+1), (levelOriginals i).card
      (levelOriginals (j+1)).card ≤
        M + ageSignatureCapacity sizes M) :
    ∀ j : Nat,
      (levelOriginals j).card ≤
        descendingLevelBudget (ageSignatureCapacity sizes) q j ∧
      (∑ i ∈ Finset.range (j+1), (levelOriginals i).card) ≤
        descendingCumulativeBudget (ageSignatureCapacity sizes) q j := by
  exact descendingGenerationCardinalityInduction
    (ageSignatureCapacity sizes)
    (ageSignatureCapacity_mono sizes)
    q levelOriginals hTop hLower

/-- The numerical upper bound at the final step of Proposition 6.44.
Here the three terms correspond to (I1/I2), (I3), and generation zero;
their separate geometric cardinal bounds remain explicit hypotheses. -/
theorem finalEnvelopeLevelBound
    (q M ageBound : Nat)
    (meetOrClosureLevels ageChangeLevels rootLevels : Finset Nat)
    (hMeet : meetOrClosureLevels.card ≤ 2*(q+1+M))
    (hAge : ageChangeLevels.card ≤ ageBound)
    (hRoot : rootLevels.card ≤ 1) :
    (meetOrClosureLevels ∪ ageChangeLevels ∪ rootLevels).card ≤
      2*(q+1+M) + ageBound + 1 := by
  calc
    (meetOrClosureLevels ∪ ageChangeLevels ∪ rootLevels).card ≤
      (meetOrClosureLevels ∪ ageChangeLevels).card +
        rootLevels.card := Finset.card_union_le _ _
    _ ≤ meetOrClosureLevels.card + ageChangeLevels.card +
        rootLevels.card := by
      have := Finset.card_union_le meetOrClosureLevels ageChangeLevels
      omega
    _ ≤ 2*(q+1+M) + ageBound + 1 := by omega

end SuccessorTree.V10

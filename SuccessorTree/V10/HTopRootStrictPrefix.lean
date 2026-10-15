import SuccessorTree.V10.HTopRootFreeCut
import Mathlib.Tactic

/-!
# V10 Definition 6.43: strict containment of earlier top H positions

For a positive-generation top real numerical H+ vertex at block j,
the exact E free level is hPosition k (j-1) k + 1. Every earlier
top position i<j is <=hPosition k (j-1) k, hence is STRICTLY
below the free level.

The earlier lemma only exported the weak inequality
hPosition k i k <= freeLevel(root), sufficient for choosing an
ancestor, but NOT for a strict representing pair (S,T) in G+.
This file records the actual one-step slack, without changing
the constructor or assuming a stronger spacing axiom.

Consequently every selected earlier block has a genuine code
prefix of size hPosition k i k + 1 inside the root's ordinary
Kpt socle. This is the numeric precondition for the actual
Definition 6.43 common-upper seed-pair representation.
-/

namespace SuccessorTree.V10

/-- Actual earlier top-generation coordinates have ONE COORDINATE
of slack before the original root's precise E free cut. -/
theorem finiteNumericH_top_prior_strictly_inside_freeCut
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N i j : Nat) (hk : 0 < k) (hj : 0 < j)
    (hInside : hPosition k j k < N) (hij : i < j) :
    hPosition k i k + 1 ≤
      (finiteNumericH K k N).freeLevel (hPosition k j k) := by
  rw [finiteNumericH_top_real_freeLevel K k N j hk hj hInside]
  have hi : i ≤ j-1 := by omega
  have hMul :
      2 * (k+1) * i ≤ 2 * (k+1) * (j-1) :=
    Nat.mul_le_mul_left (2 * (k+1)) hi
  unfold hPosition
  omega

/-- Stronger genuine top-root constructor for a finite set of earlier
blocks: the selected source prefixes have sizes d+1 with d strictly
below the single root's ordinary Kpt socle length. -/
theorem finiteNumericH_top_root_for_earlier_blocks_strict
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k j : Nat) (hk : 0 < k) (hj : 0 < j)
    (blocks : Finset Nat)
    (hEarlier : ∀ i : Nat, i ∈ blocks → i < j) :
    ∃ c : Fin (hPosition k j k + 1),
      c.val = hPosition k j k ∧
      (∀ i : Nat, i ∈ blocks →
        hPosition k i k + 1 ≤
          (finiteNumericH K k (hPosition k j k + 1)).freeLevel c.val) := by
  let N := hPosition k j k + 1
  let c : Fin N := ⟨hPosition k j k, by dsimp [N]; omega⟩
  refine ⟨c, rfl, ?_⟩
  intro i hi
  exact finiteNumericH_top_prior_strictly_inside_freeCut
    K k N i j hk hj (by dsimp [N]; omega) (hEarlier i hi)

end SuccessorTree.V10

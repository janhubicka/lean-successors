import SuccessorTree.V10.HFinitePartial
import Mathlib.Tactic

/-!
# Genuine top-root E-free cut in finite numerical H

A top real vertex c=iota(j,k), j>0, k>0, has canonical
free level iota(j-1,k)+1 in the exact finite H constructor.
Hence every earlier top-generation real vertex iota(i,k),
i<j, lies below its real E-free cut. Taking the initial
segment N=iota(j,k)+1 constructs the literal ambient root
and the selected-prefix bound required by Definition 6.43.

This supplies a concrete geometric input to the v10
K→H+ embedding. It does not introduce arbitrary E on an
L-only finite forbidden witness or prove the G+ transfer.
-/

namespace SuccessorTree.V10

theorem finiteNumericH_top_real_freeLevel
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N j : Nat) (hk : 0 < k) (hj : 0 < j)
    (hInside : hPosition k j k < N) :
    (finiteNumericH K k N).freeLevel (hPosition k j k) =
      hPosition k (j-1) k + 1 := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let c : Nat := hPosition k j k
  let d : Nat := hPosition k (j-1) k + 1
  have hE : ∀ t : Nat, A.E t c = true ↔ generatedE k j k t := by
    intro t
    have hFinite := finiteNumericHE_true_iff k N t c
    have hExact := exactHEBool_at_real_iff k j k t le_rfl
    change finiteNumericHE k N t c = true ↔ generatedE k j k t
    constructor
    · intro h
      exact hExact.mp (hFinite.mp h).2
    · intro h
      exact hFinite.mpr ⟨hInside,hExact.mpr h⟩
  have hFirst := generatedE_top_firstMissing k j hj hk
  have hBelow : d ≤ A.freeLevel c := by
    by_contra h
    have hd : A.freeLevel c < d := by omega
    have hBit : A.E (A.freeLevel c) c = true :=
      (hE (A.freeLevel c)).2 (hFirst.1 _ hd)
    have hBad := (A.E_iff_freeLevel (A.freeLevel c) c).1 hBit
    exact (lt_irrefl _) hBad
  have hAbove : A.freeLevel c ≤ d := by
    by_contra h
    have hd : d < A.freeLevel c := by omega
    have hBit : A.E d c = true :=
      (A.E_iff_freeLevel d c).2 hd
    exact hFirst.2 ((hE d).1 hBit)
  exact le_antisymm hAbove hBelow

theorem finiteNumericH_top_prior_inside_freeCut
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k N i j : Nat) (hk : 0 < k) (hj : 0 < j)
    (hInside : hPosition k j k < N) (hij : i < j) :
    hPosition k i k ≤
      (finiteNumericH K k N).freeLevel (hPosition k j k) := by
  rw [finiteNumericH_top_real_freeLevel K k N j hk hj hInside]
  have hi : i ≤ j-1 := by omega
  have hMul :
      2 * (k+1) * i ≤ 2 * (k+1) * (j-1) :=
    Nat.mul_le_mul_left (2 * (k+1)) hi
  unfold hPosition
  omega

theorem finiteNumericH_top_root_for_earlier_blocks
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (k j : Nat) (hk : 0 < k) (hj : 0 < j)
    (blocks : Finset Nat)
    (hEarlier : ∀ i : Nat, i ∈ blocks → i < j) :
    ∃ c : Fin (hPosition k j k + 1),
      c.val = hPosition k j k ∧
      (∀ i : Nat, i ∈ blocks →
        hPosition k i k ≤
          (finiteNumericH K k (hPosition k j k + 1)).freeLevel c.val) := by
  let N := hPosition k j k + 1
  let c : Fin N := ⟨hPosition k j k,by dsimp [N]; omega⟩
  refine ⟨c,rfl,?_⟩
  intro i hi
  exact finiteNumericH_top_prior_inside_freeCut K k N i j hk hj
    (by dsimp [N]; omega) (hEarlier i hi)

end SuccessorTree.V10
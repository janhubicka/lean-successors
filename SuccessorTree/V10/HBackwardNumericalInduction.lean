import SuccessorTree.V10.EnvelopeNumericalRecurrence
import Mathlib.Tactic

/-!
# V10: exact backward induction from real-generation level counts

The verified geometric induction produces, at each real generation
0<r<k, the bound

  s_r <= H_r + R(H_r),
  H_r <= 1 + sum_{r<m<=k} s_m.

The top generation has s_k<=q, and the ONE initial root must
remain in the cumulative budget. This file proves directly that
these numerical hypotheses imply the exact v10 downward
recursion, with no extra +1 at every generation:

  C_r = 1 + sum_{r<=m<=k} s_m
  C_r <= 2*C_{r+1} + R(C_{r+1})
  C_k <= q+1.

The proof uses the explicit singleton decomposition of a finite
integer interval. It does not assume any unproved reindexing
bijection between generations and distance from top.

In particular, for j<k,

  1 + sum_{k-j<=m<=k} s_m
    <= descendingCumulativeBudget R q j.

The following actual-run application will use the checked
I1/I2/I3 partition and higher-original bound as inputs, rather
than assuming new geometric events.
-/

namespace SuccessorTree.V10

/-- The lower endpoint of a finite interval contributes one
additional summand. This is valid for Nat-valued sums and
does not require cancellation. -/
theorem sum_Icc_nat_succ_lower
    (s : Nat → Nat) (a b : Nat) (hab : a ≤ b) :
    (∑ m ∈ Finset.Icc a b, s m) =
      s a + ∑ m ∈ Finset.Icc (a+1) b, s m := by
  have hSet : Finset.Icc a b =
      insert a (Finset.Icc (a+1) b) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hNot : a ∉ Finset.Icc (a+1) b := by
    simp only [Finset.mem_Icc]
    omega
  rw [hSet, Finset.sum_insert hNot]

/-- Exact descending cumulative bound with the distinguished
root charged ONCE, at the highest generation. -/
theorem descending_real_generation_count_bound
    (R : Nat → Nat) (hMono : Monotone R)
    (q k : Nat) (hk : 0 < k)
    (s : Nat → Nat)
    (hTop : s k ≤ q)
    (hLower : ∀ r : Nat, 0 < r → r < k →
      let M := 1 + ∑ m ∈ Finset.Icc (r+1) k, s m
      s r ≤ M + R M) :
    ∀ j : Nat, j < k →
      1 + ∑ m ∈ Finset.Icc (k-j) k, s m ≤
        descendingCumulativeBudget R q j := by
  intro j
  induction j with
  | zero =>
      intro _hj
      have hBase : 1 + s k ≤ q + 1 := by omega
      simpa only [Nat.sub_zero, Finset.Icc_self,
        Finset.sum_singleton, descendingCumulativeBudget]
        using hBase
  | succ j ih =>
      intro hjsucc
      have hj : j < k := by omega
      have hIH := ih hj
      let r : Nat := k - (j+1)
      have hrPos : 0 < r := by dsimp [r]; omega
      have hrLe : r ≤ k := by dsimp [r]; omega
      have hrLt : r < k := by dsimp [r]; omega
      have hrNext : r+1 = k-j := by dsimp [r]; omega
      let M : Nat := 1 + ∑ m ∈ Finset.Icc (r+1) k, s m
      have hM : M ≤ descendingCumulativeBudget R q j := by
        simpa only [M, hrNext] using hIH
      have hNext : s r ≤ M + R M := hLower r hrPos hrLt
      have hRM : R M ≤ R (descendingCumulativeBudget R q j) :=
        hMono hM
      have hSum :
          1 + ∑ m ∈ Finset.Icc (k-(j+1)) k, s m =
            M + s r := by
        change 1 + ∑ m ∈ Finset.Icc r k, s m = M + s r
        rw [sum_Icc_nat_succ_lower s r k hrLe]
        dsimp [M]
        omega
      calc
        1 + ∑ m ∈ Finset.Icc (k-(j+1)) k, s m =
            M + s r := hSum
        _ ≤ 2 * descendingCumulativeBudget R q j +
              R (descendingCumulativeBudget R q j) := by omega
        _ = descendingCumulativeBudget R q (j+1) := rfl

/-- Direct paper-signature-polynomial specialization of the exact
backward induction. Its next caller supplies the actual-run event
bounds from I1/I2 and I3 and the actual top seed count. -/
theorem descending_real_generation_signature_bound
    {f : Nat} (sizes : Fin f → Nat)
    (q k : Nat) (hk : 0 < k)
    (s : Nat → Nat)
    (hTop : s k ≤ q)
    (hLower : ∀ r : Nat, 0 < r → r < k →
      let M := 1 + ∑ m ∈ Finset.Icc (r+1) k, s m
      s r ≤ M + ageSignatureCapacity sizes M) :
    ∀ j : Nat, j < k →
      1 + ∑ m ∈ Finset.Icc (k-j) k, s m ≤
        descendingCumulativeBudget
          (ageSignatureCapacity sizes) q j := by
  exact descending_real_generation_count_bound
    (ageSignatureCapacity sizes)
    (ageSignatureCapacity_mono sizes)
    q k hk s hTop hLower

end SuccessorTree.V10
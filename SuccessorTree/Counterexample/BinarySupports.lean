import Mathlib.Tactic

/-!
# An explicit continuum-sized almost-disjoint family of level sets

Every binary sequence b : ℕ → Bool determines a strictly increasing
sequence of retained image levels

  ℓ_b(n) = 2^n + ∑_{i<n, b(i)=true} 2^i.

The root image level is 1. Levels for each n lie in the disjoint
interval [2^n, 2^(n+1)), and the level encodes the first n bits of b.
Consequently distinct branches share only finitely many retained levels.

This explicit coding gives the support family for the ZFC counterexample
to the original direct shape-map Ellentuck statement, without needing
any choices or separate existence axioms for almost-disjoint families.
-/

namespace SuccessorTree.Counterexample

/-- The binary value of a finite prefix. -/
def prefixBits (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => prefixBits b n + if b n then 2 ^ n else 0

/-- A level in the disjoint band [2^n, 2^(n+1)),
encoding precisely the first n bits of b. -/
def branchLevel (b : ℕ → Bool) (n : ℕ) : ℕ :=
  2 ^ n + prefixBits b n

theorem pow_two_succ (n : ℕ) : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
  rw [pow_succ]
  omega

theorem pow_two_monotone : Monotone (fun n : ℕ => 2 ^ n) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [pow_two_succ]
  omega

/-- The prefix value occupies at most n binary places. -/
theorem prefixBits_lt_pow (b : ℕ → Bool) :
    ∀ n, prefixBits b n < 2 ^ n := by
  intro n
  induction n with
  | zero =>
      norm_num [prefixBits]
  | succ n ih =>
      rw [prefixBits, pow_two_succ]
      split_ifs <;> omega

theorem branchLevel_lower (b : ℕ → Bool) (n : ℕ) :
    2 ^ n ≤ branchLevel b n := by
  dsimp [branchLevel]
  omega

theorem branchLevel_upper (b : ℕ → Bool) (n : ℕ) :
    branchLevel b n < 2 ^ (n + 1) := by
  have h := prefixBits_lt_pow b n
  rw [pow_two_succ]
  dsimp [branchLevel]
  omega

theorem branchLevel_zero (b : ℕ → Bool) : branchLevel b 0 = 1 := by
  simp [branchLevel, prefixBits]

theorem branchLevel_strictMono (b : ℕ → Bool) :
    StrictMono (branchLevel b) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h1 := branchLevel_upper b n
  have h2 := branchLevel_lower b (n + 1)
  omega

/-- The level of a retained image uniquely determines the source depth
even if two different binary branches were used. -/
theorem branchLevel_index_eq
    (a b : ℕ → Bool) {n m : ℕ}
    (h : branchLevel a n = branchLevel b m) : n = m := by
  have ha1 := branchLevel_lower a n
  have ha2 := branchLevel_upper a n
  have hb1 := branchLevel_lower b m
  have hb2 := branchLevel_upper b m
  by_contra hne
  by_cases hnm : n < m
  · have hp : 2 ^ (n + 1) ≤ 2 ^ m :=
      pow_two_monotone (by omega)
    omega
  · have hmn : m < n := by omega
    have hp : 2 ^ (m + 1) ≤ 2 ^ n :=
      pow_two_monotone (by omega)
    omega

/-- Equal binary prefix codes imply equal source bits at each
earlier position. The proof uses the sharp prefix-value bound to
isolate the top bit of each finite binary word. -/
theorem prefixBits_eq_implies_prefix
    (a b : ℕ → Bool) :
    ∀ n : ℕ, prefixBits a n = prefixBits b n →
      ∀ i : ℕ, i < n → a i = b i := by
  intro n
  induction n with
  | zero =>
      intro h i hi
      omega
  | succ n ih =>
      intro heq i hi
      have ha_lt := prefixBits_lt_pow a n
      have hb_lt := prefixBits_lt_pow b n
      have hbit : a n = b n := by
        cases hba : a n <;> cases hbb : b n
        · rfl
        · simp [prefixBits, hba, hbb] at heq
          omega
        · simp [prefixBits, hba, hbb] at heq
          omega
        · rfl
      have hprev : prefixBits a n = prefixBits b n := by
        simp only [prefixBits, hbit] at heq
        omega
      by_cases hin : i < n
      · exact ih hprev i hin
      · have hieq : i = n := by omega
        subst i
        exact hbit

theorem branchLevel_eq_implies_prefix
    (a b : ℕ → Bool) (n : ℕ)
    (h : branchLevel a n = branchLevel b n) :
    ∀ i < n, a i = b i := by
  apply prefixBits_eq_implies_prefix a b n
  dsimp [branchLevel] at h
  omega

/-- The retained-level ranges of distinct binary branches have finite
intersection: after the first differing bit their codes cannot coincide
at the same depth, and different depths lie in disjoint power-of-two bands. -/
theorem branchLevel_almostDisjoint
    (a b : ℕ → Bool) (hab : a ≠ b) :
    (Set.range (branchLevel a) ∩
      Set.range (branchLevel b)).Finite := by
  classical
  have hex : ∃ k : ℕ, a k ≠ b k := by
    by_contra h
    have heq : a = b := by
      funext k
      by_contra hne
      exact h ⟨k, hne⟩
    exact hab heq
  obtain ⟨k, hk⟩ := hex
  have hsubset :
      (Set.range (branchLevel a) ∩ Set.range (branchLevel b)) ⊆
        Set.range (fun i : Fin (k + 1) => branchLevel a i.val) := by
    intro x hx
    rcases hx with ⟨⟨n, rfl⟩, ⟨m, hnm⟩⟩
    have hdepth : n = m :=
      branchLevel_index_eq a b hnm.symm
    subst m
    have hbound : n ≤ k := by
      by_contra h
      have hkn : k < n := by omega
      have heq : a k = b k :=
        branchLevel_eq_implies_prefix a b n hnm.symm k hkn
      exact hk heq
    exact ⟨⟨n, by omega⟩, rfl⟩
  exact (Set.finite_range _).subset hsubset

end SuccessorTree.Counterexample

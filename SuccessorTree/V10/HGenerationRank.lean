import SuccessorTree.V10.HAge
import Mathlib.Tactic

/-!
# The generation-rank estimate in the v10 signature repair

In the exact H model, any linked pair with strictly increasing first
indices has strictly increasing generations, except that both
generations may equal the special top value k. For an irreducible
ordered copy of r ≤ k+1 vertices, this implies that the a-th
generation n_a satisfies a ≤ n_a.

This validates the *arithmetic/rank* assertion in the proposed
signature lemma. It does not validate the later relocation
iota(j_a,n_a) ↦ iota(j_a,a), the common-socle age argument, or
the premise that the manuscript's actual H has exact copying.
-/

namespace SuccessorTree.V10

/-- A linked pair of real vertices, ordered by first index, has the
specified generation gate. -/
theorem linked_increasing_generation {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool) (k : Nat)
    (i j : Fin n) (q m : Nat)
    (hij : i < j)
    (hlink : HLinked B k (.real i q) (.real j m)) :
    q ≤ k ∧ m ≤ k ∧ (q < m ∨ (q = m ∧ m = k)) := by
  have hg := HLinked_gate B k i j q m hlink
  rcases hg with hforward | hbackward
  · exact ⟨hforward.2.1, hforward.2.2.1, hforward.2.2.2⟩
  · exact False.elim ((not_lt_of_ge (le_of_lt hij)) hbackward.1)

/-- Pure finite-rank lemma for nondecreasing generation sequences,
where all non-strict steps occur only at top generation k. -/
theorem generation_rank_lower_bound
    (k r : Nat) (hr : r ≤ k + 1)
    (generation : Fin r → Nat)
    (hgate : ∀ a b : Fin r, a < b →
      generation a < generation b ∨
      (generation a = k ∧ generation b = k)) :
    ∀ a : Fin r, a.val ≤ generation a := by
  have haux : ∀ j : Nat, ∀ hj : j < r,
      j ≤ generation ⟨j, hj⟩ := by
    intro j
    induction j with
    | zero =>
        intro hj
        omega
    | succ j ih =>
        intro hj
        have hprev : j < r := by omega
        have hab : (⟨j, hprev⟩ : Fin r) < ⟨j + 1, hj⟩ := by
          exact Fin.lt_def.mpr (by omega)
        rcases hgate ⟨j, hprev⟩ ⟨j + 1, hj⟩ hab with hlt | ⟨_, heq⟩
        · have hp := ih hprev
          omega
        · have hbound : j + 1 ≤ k := by omega
          simpa [heq] using hbound
  intro a
  exact haux a.val a.isLt

/-- The actual generation-rank consequence for an ordered
irreducible H configuration, assuming all pairs are linked. -/
theorem ordered_linked_generation_rank {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool)
    (k r : Nat) (hr : r ≤ k + 1)
    (first : Fin r → Fin n) (generation : Fin r → Nat)
    (hfirst : StrictMono first)
    (hlinked : ∀ a b : Fin r, a < b →
      HLinked B k
        (.real (first a) (generation a))
        (.real (first b) (generation b))) :
    ∀ a : Fin r, a.val ≤ generation a := by
  apply generation_rank_lower_bound k r hr generation
  intro a b hab
  exact (linked_increasing_generation B k
    (first a) (first b) (generation a) (generation b)
    (hfirst hab) (hlinked a b hab)).2.2

end SuccessorTree.V10

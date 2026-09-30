import SuccessorTree.HalesJewett.ForcingFusionLimit
import Mathlib.Tactic

/-!
# Proposition 1 from forcing Lemma 2

This file formalizes the second fusion in the Hubička--Smolík proof.
At stage i, Lemma 2 gives a subspace U_i for the current large set O_i,
then the outer subspace is refined by Shift(U_i,i).

The proof follows the two invariants in the paper and defines the final limit
structurally: its head is already fixed at stage 1, and block k is fixed from
stage k+2 onward.
-/

namespace SuccessorTree
namespace HalesJewett

open Set

/-- A large set bundled with its largeness proof. -/
structure LargeStage (α : Type u) where
  set : Set (List α)
  large : WordLarge set

/-- Chosen Lemma-2 witness for a large stage. -/
noncomputable def propositionRefiner
    [Fintype α] [DecidableEq α]
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α)
    (X : LargeStage α) : Subspace α :=
  Classical.choose
    (exists_hasLargePlus_of_schedule X.set X.large hjProduct S)

theorem propositionRefiner_spec
    [Fintype α] [DecidableEq α]
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α)
    (X : LargeStage α) :
    HasLargePlus (propositionRefiner hjProduct S X) X.set :=
  Classical.choose_spec
    (exists_hasLargePlus_of_schedule X.set X.large hjProduct S)

/-- Advance the sequence of large sets using the plus-set from Lemma 2. -/
noncomputable def nextLargeStage
    [Fintype α] [DecidableEq α]
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α)
    (X : LargeStage α) : LargeStage α where
  set := plusSet (propositionRefiner hjProduct S X) X.set
  large := (propositionRefiner_spec hjProduct S X).2

/-- Recursive large sets O_i. -/
noncomputable def propositionStages
    [Fintype α] [DecidableEq α]
    (A : Set (List α)) (hA : WordLarge A)
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α) : Nat → LargeStage α
  | 0 => ⟨A, hA⟩
  | i + 1 =>
      nextLargeStage hjProduct S
        (propositionStages A hA hjProduct S i)

/-- The chosen Lemma-2 subspace U_i. -/
noncomputable def propositionU
    [Fintype α] [DecidableEq α]
    (A : Set (List α)) (hA : WordLarge A)
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α) (i : Nat) : Subspace α :=
  propositionRefiner hjProduct S
    (propositionStages A hA hjProduct S i)

theorem propositionU_empty_mem
    [Fintype α] [DecidableEq α]
    (A : Set (List α)) (hA : WordLarge A)
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α) (i : Nat) :
    (propositionU A hA hjProduct S i).eval [] ∈
      (propositionStages A hA hjProduct S i).set := by
  exact (propositionRefiner_spec hjProduct S
    (propositionStages A hA hjProduct S i)).1

theorem propositionStages_succ_mem
    [Fintype α] [DecidableEq α]
    (A : Set (List α)) (hA : WordLarge A)
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α) (i : Nat) (v : List α)
    (hv : v ∈ (propositionStages A hA hjProduct S (i + 1)).set) :
    ∀ c : α,
      (propositionU A hA hjProduct S i).eval (c :: v) ∈
        (propositionStages A hA hjProduct S i).set := by
  change v ∈ plusSet
    (propositionU A hA hjProduct S i)
    (propositionStages A hA hjProduct S i).set at hv
  exact hv

/-- Recursive outer subspaces W_i from Proposition 1. -/
noncomputable def propositionSeq
    [Fintype α] [DecidableEq α]
    (A : Set (List α)) (hA : WordLarge A)
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α) : Nat → Subspace α
  | 0 => Subspace.identity
  | i + 1 =>
      (propositionSeq A hA hjProduct S i).compose
        ((propositionU A hA hjProduct S i).shift i)

@[simp] theorem propositionSeq_zero
    [Fintype α] [DecidableEq α]
    (A : Set (List α)) (hA : WordLarge A)
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α) :
    propositionSeq A hA hjProduct S 0 = Subspace.identity := rfl

@[simp] theorem propositionSeq_succ
    [Fintype α] [DecidableEq α]
    (A : Set (List α)) (hA : WordLarge A)
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α) (i : Nat) :
    propositionSeq A hA hjProduct S (i + 1) =
      (propositionSeq A hA hjProduct S i).compose
        ((propositionU A hA hjProduct S i).shift i) := rfl

/-- The two inductive invariants from the paper. -/
theorem proposition_invariants
    [Fintype α] [DecidableEq α]
    (A : Set (List α)) (hA : WordLarge A)
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α) :
    ∀ i : Nat,
      (∀ u : List α, u.length < i →
        (propositionSeq A hA hjProduct S i).eval u ∈ A) ∧
      (∀ u : List α, u.length = i →
        ∀ v : List α,
          v ∈ (propositionStages A hA hjProduct S i).set →
          (propositionSeq A hA hjProduct S i).eval (u ++ v) ∈ A) := by
  intro i
  induction i with
  | zero =>
      constructor
      · intro u hu
        omega
      · intro u hu v hv
        have hu0 : u = [] := List.length_eq_zero_iff.mp hu
        subst u
        change v ∈ A at hv
        change (Subspace.identity : Subspace α).eval ([] ++ v) ∈ A
        simpa using hv
  | succ i ih =>
      rcases ih with ⟨ihShort, ihTail⟩
      constructor
      · intro u hu
        by_cases hlt : u.length < i
        · have heq :=
            Subspace.compose_shift_eval_of_length_lt
              (propositionSeq A hA hjProduct S i)
              (propositionU A hA hjProduct S i)
              i u hlt
          change
            ((propositionSeq A hA hjProduct S i).compose
              ((propositionU A hA hjProduct S i).shift i)).eval u ∈ A
          rw [heq]
          exact ihShort u hlt
        · have hlen : u.length = i := by omega
          change
            ((propositionSeq A hA hjProduct S i).compose
              ((propositionU A hA hjProduct S i).shift i)).eval u ∈ A
          rw [Subspace.compose_eval]
          have hshift :=
            Subspace.shift_eval_append
              (propositionU A hA hjProduct S i) i u [] hlen
          simp only [List.append_nil] at hshift
          rw [hshift]
          exact ihTail u hlen
            ((propositionU A hA hjProduct S i).eval [])
            (propositionU_empty_mem A hA hjProduct S i)
      · intro u hu v hv
        have hi : i < u.length := by omega
        let w := u.take i
        let c : α := u[i]
        have hw : w.length = i := by
          dsimp [w]
          simp [List.length_take, Nat.min_eq_left (by omega : i ≤ u.length)]
        have hsplit : w ++ [c] = u := by
          dsimp [w, c]
          calc
            u.take i ++ [u[i]] = u.take (i + 1) :=
              List.take_concat_get' u i hi
            _ = u := by simp [hu]
        rw [← hsplit]
        change
          ((propositionSeq A hA hjProduct S i).compose
            ((propositionU A hA hjProduct S i).shift i)).eval
              ((w ++ [c]) ++ v) ∈ A
        rw [Subspace.compose_eval]
        have harg : (w ++ [c]) ++ v = w ++ (c :: v) := by
          simp [List.append_assoc]
        rw [harg]
        have hshift :=
          Subspace.shift_eval_append
            (propositionU A hA hjProduct S i)
            i w (c :: v) hw
        rw [hshift]
        have hmem :=
          propositionStages_succ_mem
            A hA hjProduct S i v hv c
        exact ihTail w hw
          ((propositionU A hA hjProduct S i).eval (c :: v)) hmem

/-- The head is fixed from stage 1 onward. -/
theorem propositionSeq_head_eq_one
    [Fintype α] [DecidableEq α]
    (A : Set (List α)) (hA : WordLarge A)
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α) :
    ∀ i : Nat, 1 ≤ i →
      (propositionSeq A hA hjProduct S i).head =
        (propositionSeq A hA hjProduct S 1).head := by
  intro i hi
  induction i with
  | zero =>
      omega
  | succ i ih =>
      by_cases hi0 : i = 0
      · subst i
        rfl
      · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
        rw [propositionSeq_succ]
        rw [Subspace.compose_shift_head_eq]
        · exact ih (by omega)
        · exact hipos

/-- One Proposition-1 step preserves blocks below the shift level. -/
theorem propositionSeq_block_succ_eq
    [Fintype α] [DecidableEq α]
    (A : Set (List α)) (hA : WordLarge A)
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α)
    (i k : Nat) (h : k + 1 < i) :
    (propositionSeq A hA hjProduct S (i + 1)).blocks k =
      (propositionSeq A hA hjProduct S i).blocks k := by
  rw [propositionSeq_succ]
  exact Subspace.compose_shift_blocks_eq
    (propositionSeq A hA hjProduct S i)
    (propositionU A hA hjProduct S i) i k h

/-- Block k is permanent from stage k+2 onward. -/
theorem propositionSeq_block_eq_of_le
    [Fintype α] [DecidableEq α]
    (A : Set (List α)) (hA : WordLarge A)
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α)
    (k p q : Nat)
    (hstable : k + 2 ≤ p) (hpq : p ≤ q) :
    (propositionSeq A hA hjProduct S q).blocks k =
      (propositionSeq A hA hjProduct S p).blocks k := by
  induction q generalizing p with
  | zero =>
      have hp : p = 0 := by omega
      subst p
      rfl
  | succ q ih =>
      by_cases hp : p = q + 1
      · subst p
        rfl
      · have hpq' : p ≤ q := by omega
        have hkq : k + 1 < q := by omega
        calc
          (propositionSeq A hA hjProduct S (q + 1)).blocks k =
              (propositionSeq A hA hjProduct S q).blocks k :=
            propositionSeq_block_succ_eq
              A hA hjProduct S q k hkq
          _ = (propositionSeq A hA hjProduct S p).blocks k :=
            ih p hstable hpq'

/-- Explicit blockwise limit for Proposition 1. -/
noncomputable def propositionLimit
    [Fintype α] [DecidableEq α]
    (A : Set (List α)) (hA : WordLarge A)
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α) : Subspace α where
  head := (propositionSeq A hA hjProduct S 1).head
  blocks := fun k => (propositionSeq A hA hjProduct S (k + 2)).blocks k

/-- Every finite evaluation of the limit agrees with stage length+1. -/
theorem propositionLimit_eval_eq
    [Fintype α] [DecidableEq α]
    (A : Set (List α)) (hA : WordLarge A)
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α) (u : List α) :
    (propositionLimit A hA hjProduct S).eval u =
      (propositionSeq A hA hjProduct S (u.length + 1)).eval u := by
  apply Subspace.eval_eq_of_head_blocks
  · change
      (propositionSeq A hA hjProduct S 1).head =
        (propositionSeq A hA hjProduct S (u.length + 1)).head
    exact (propositionSeq_head_eq_one
      A hA hjProduct S (u.length + 1) (by omega)).symm
  · intro k hk
    change
      (propositionSeq A hA hjProduct S (k + 2)).blocks k =
        (propositionSeq A hA hjProduct S (u.length + 1)).blocks k
    exact (propositionSeq_block_eq_of_le
      A hA hjProduct S k (k + 2) (u.length + 1)
      le_rfl (by omega)).symm

/-- Proposition 1, conditional only on the line schedule used in Lemma 2. -/
theorem largeSetTheorem_of_schedule
    [Fintype α] [DecidableEq α]
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α) :
    LargeSetTheorem α := by
  intro A hA
  let W := propositionLimit A hA hjProduct S
  refine ⟨W, ?_⟩
  intro u
  have hshort :=
    (proposition_invariants A hA hjProduct S (u.length + 1)).1
      u (by omega)
  have heq :=
    propositionLimit_eval_eq A hA hjProduct S u
  change W.eval u ∈ A
  rw [heq]
  exact hshort

end HalesJewett
end SuccessorTree

import SuccessorTree.Block.ParityFatObstruction

/-!
# Four-block obstruction to branch-first block-fat A4

For any four blocks with odd variable multiplicity and even constant
1-parity, freezing one among the last three to 0 leaves a legal
one-variable block in the ambient span whose variable count differs by
2 modulo 4 from the first block. This checks the finite algebraic core;
it is NOT a formalization of the infinite fat reduction or monoid M1-M4.
-/

namespace SuccessorTree.Block
namespace ParityFat

def frozenZero (w : List (Option Bool)) : List (Option Bool) :=
  (evaluate w false).map some

@[simp] theorem evaluate_frozenZero (w : List (Option Bool)) (a : Bool) :
    evaluate (frozenZero w) a = evaluate w false := by
  simp [frozenZero, evaluate, List.map_map, Function.comp_def]

@[simp] theorem varCount_frozenZero (w : List (Option Bool)) :
    varCount (frozenZero w) = 0 := by
  induction w with
  | nil => rfl
  | cons b ws ih =>
      cases b <;> simp [frozenZero, evaluate, varCount, ih]

theorem evaluate_append (u v : List (Option Bool)) (a : Bool) :
    evaluate (u ++ v) a = evaluate u a ++ evaluate v a := by
  simp [evaluate]

theorem varCount_append (u v : List (Option Bool)) :
    varCount (u ++ v) = varCount u + varCount v := by
  induction u with
  | nil => simp [varCount]
  | cons b bs ih => cases b <;> simp [varCount, ih, Nat.add_assoc]

theorem weight_eval_append (u v : List (Option Bool)) (a : Bool) :
    weight (evaluate (u ++ v) a) =
      weight (evaluate u a) + weight (evaluate v a) := by
  rw [evaluate_append, weight_append]

theorem equal_residue_among_three_odds (a b c : Nat)
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hc : c % 2 = 1) :
    a % 4 = b % 4 ∨ a % 4 = c % 4 ∨ b % 4 = c % 4 := by
  omega

theorem same_odd_pair_flips (base a b : Nat)
    (ha : a % 2 = 1) (hb : b % 2 = 1)
    (heq : a % 4 = b % 4) :
    (base + a + b) % 4 ≠ base % 4 := by
  omega

def grouped12 (w0 w1 w2 w3 : List (Option Bool)) : List (Option Bool) :=
  w0 ++ w1 ++ w2 ++ frozenZero w3

def grouped13 (w0 w1 w2 w3 : List (Option Bool)) : List (Option Bool) :=
  w0 ++ w1 ++ frozenZero w2 ++ w3

def grouped23 (w0 w1 w2 w3 : List (Option Bool)) : List (Option Bool) :=
  w0 ++ frozenZero w1 ++ w2 ++ w3

def span4 (w0 w1 w2 w3 : List (Option Bool)) : Set (List Bool) :=
  {t | ∃ a b c d : Bool,
    t = evaluate w0 a ++ evaluate w1 b ++
      evaluate w2 c ++ evaluate w3 d}

theorem grouped12_span (w0 w1 w2 w3 : List (Option Bool)) (a : Bool) :
    evaluate (grouped12 w0 w1 w2 w3) a ∈ span4 w0 w1 w2 w3 := by
  refine ⟨a, a, a, false, ?_⟩
  simp [grouped12, evaluate_append, List.append_assoc]

theorem grouped13_span (w0 w1 w2 w3 : List (Option Bool)) (a : Bool) :
    evaluate (grouped13 w0 w1 w2 w3) a ∈ span4 w0 w1 w2 w3 := by
  refine ⟨a, a, false, a, ?_⟩
  simp [grouped13, evaluate_append, List.append_assoc]

theorem grouped23_span (w0 w1 w2 w3 : List (Option Bool)) (a : Bool) :
    evaluate (grouped23 w0 w1 w2 w3) a ∈ span4 w0 w1 w2 w3 := by
  refine ⟨a, false, a, a, ?_⟩
  simp [grouped23, evaluate_append, List.append_assoc]

theorem grouped12_vars (w0 w1 w2 w3 : List (Option Bool)) :
    varCount (grouped12 w0 w1 w2 w3) =
      varCount w0 + varCount w1 + varCount w2 := by
  simp [grouped12, varCount_append, Nat.add_assoc]

theorem grouped13_vars (w0 w1 w2 w3 : List (Option Bool)) :
    varCount (grouped13 w0 w1 w2 w3) =
      varCount w0 + varCount w1 + varCount w3 := by
  simp [grouped13, varCount_append, Nat.add_assoc]

theorem grouped23_vars (w0 w1 w2 w3 : List (Option Bool)) :
    varCount (grouped23 w0 w1 w2 w3) =
      varCount w0 + varCount w2 + varCount w3 := by
  simp [grouped23, varCount_append, Nat.add_assoc]

def AllowedParity (w : List (Option Bool)) : Prop :=
  varCount w % 2 = 1 ∧ weight (evaluate w false) % 2 = 0

theorem four_blocks_flip
    (w0 w1 w2 w3 : List (Option Bool))
    (h0 : AllowedParity w0) (h1 : AllowedParity w1)
    (h2 : AllowedParity w2) (h3 : AllowedParity w3) :
    ∃ v : List (Option Bool),
      AllowedParity v ∧
      (∀ a : Bool, evaluate v a ∈ span4 w0 w1 w2 w3) ∧
      varCount v % 4 ≠ varCount w0 % 4 := by
  rcases equal_residue_among_three_odds
      (varCount w1) (varCount w2) (varCount w3)
      h1.1 h2.1 h3.1 with heq | heq | heq
  · refine ⟨grouped12 w0 w1 w2 w3, ?_, grouped12_span w0 w1 w2 w3, ?_⟩
    · constructor
      · rw [grouped12_vars]
        omega
      · simp only [grouped12, weight_eval_append, evaluate_frozenZero]
        omega
    · rw [grouped12_vars]
      exact same_odd_pair_flips _ _ _ h1.1 h2.1 heq
  · refine ⟨grouped13 w0 w1 w2 w3, ?_, grouped13_span w0 w1 w2 w3, ?_⟩
    · constructor
      · rw [grouped13_vars]
        omega
      · simp only [grouped13, weight_eval_append, evaluate_frozenZero]
        omega
    · rw [grouped13_vars]
      exact same_odd_pair_flips _ _ _ h1.1 h3.1 heq
  · refine ⟨grouped23 w0 w1 w2 w3, ?_, grouped23_span w0 w1 w2 w3, ?_⟩
    · constructor
      · rw [grouped23_vars]
        omega
      · simp only [grouped23, weight_eval_append, evaluate_frozenZero]
        omega
    · rw [grouped23_vars]
      exact same_odd_pair_flips _ _ _ h2.1 h3.1 heq

end ParityFat
end SuccessorTree.Block

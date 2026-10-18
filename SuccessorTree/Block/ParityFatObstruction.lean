import Mathlib.Tactic

/-!
# Binary parity obstruction in the old fat-tree row convention

Finite-coordinate core only: `none` denotes the live variable and
`some b` denotes a constant bit. The two-step old fat lift finishes
the previous variable and then appends a free successor.
The full infinitary reduction and concrete monoid axioms are separate
English arguments; this file does NOT claim to certify those instances.
-/

namespace SuccessorTree.Block
namespace ParityFat

def weight : List Bool → Nat
  | [] => 0
  | x :: xs => (if x then 1 else 0) + weight xs

def varCount : List (Option Bool) → Nat
  | [] => 0
  | none :: xs => 1 + varCount xs
  | some _ :: xs => varCount xs

def evaluate (w : List (Option Bool)) (a : Bool) : List Bool :=
  w.map (fun s => match s with | none => a | some b => b)

theorem weight_append (xs ys : List Bool) :
    weight (xs ++ ys) = weight xs + weight ys := by
  induction xs with
  | nil => simp [weight]
  | cons b bs ih => cases b <;> simp [weight, ih, Nat.add_assoc]

theorem weight_evaluate_true (w : List (Option Bool)) :
    weight (evaluate w true) =
      weight (evaluate w false) + varCount w := by
  induction w with
  | nil => rfl
  | cons sym xs ih =>
      cases sym with
      | none =>
          simp [evaluate, weight, varCount] at *
          omega
      | some b =>
          cases b <;> simp [evaluate, weight, varCount] at * <;> omega

theorem opposite_head_parity (head : List Bool) (w : List (Option Bool))
    (hOdd : varCount w % 2 = 1) :
    weight (head ++ evaluate w false) % 2 ≠
      weight (head ++ evaluate w true) % 2 := by
  rw [weight_append, weight_append, weight_evaluate_true]
  omega

def oneRowLift (head : List Bool) : Set (List Bool) :=
  {z | ∃ b : Bool, z = head ++ [b]}

def twoStepLift (head : List Bool) (w : List (Option Bool)) :
    Set (List Bool) :=
  {z | ∃ a b : Bool, z = (head ++ evaluate w a) ++ [b]}

theorem oneRowLift_subset_twoStep (head : List Bool)
    (w : List (Option Bool)) (a : Bool) :
    oneRowLift (head ++ evaluate w a) ⊆ twoStepLift head w := by
  intro z hz
  rcases hz with ⟨b, hb⟩
  exact ⟨a, b, hb⟩

theorem two_first_rows_opposite (head : List Bool)
    (w : List (Option Bool)) (hOdd : varCount w % 2 = 1) :
    ∃ h0 h1 : List Bool,
      oneRowLift h0 ⊆ twoStepLift head w ∧
      oneRowLift h1 ⊆ twoStepLift head w ∧
      weight h0 % 2 ≠ weight h1 % 2 := by
  refine ⟨head ++ evaluate w false, head ++ evaluate w true, ?_, ?_, ?_⟩
  · exact oneRowLift_subset_twoStep head w false
  · exact oneRowLift_subset_twoStep head w true
  · exact opposite_head_parity head w hOdd

def FirstRowHomogeneity {R : Type*} (le : R → R → Prop)
    (colour : R → Bool) : Prop :=
  ∀ U : R, ∃ V : R, le V U ∧
    ∀ W0 W1 : R, le W0 V → le W1 V → colour W0 = colour W1

theorem firstRowHomogeneity_false_of_splitting
    {R : Type*} (le : R → R → Prop) (colour : R → Bool)
    (hNonempty : Nonempty R)
    (hSplit : ∀ U : R, ∃ V0 V1 : R,
      le V0 U ∧ le V1 U ∧ colour V0 ≠ colour V1) :
    ¬ FirstRowHomogeneity le colour := by
  intro hHom
  obtain ⟨V, _, hMono⟩ := hHom (Classical.choice hNonempty)
  obtain ⟨V0, V1, hV0, hV1, hDifferent⟩ := hSplit V
  exact hDifferent (hMono V0 V1 hV0 hV1)

end ParityFat
end SuccessorTree.Block

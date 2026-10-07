import SuccessorTree.FreeAncestral
import SuccessorTree.Tree
import Mathlib.Tactic

/-! # Prefix order on free ancestral histories

This file equips the indexed free-history syntax with its natural prefix
relation. It deliberately stops just before the LevelTree instance: the
first milestone is to verify reflexivity, transitivity, antisymmetry,
comparability below a common branch, and existence of a prefix on every lower
level.
-/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat}

/-- Prefix relation between two indexed histories. -/
inductive Prefix :
    {m n : Nat} →
      History Label arity m →
      History Label arity n → Prop
  | refl {n : Nat} (h : History Label arity n) :
      Prefix h h
  | step {m n : Nat}
      {a : History Label arity m}
      {b : History Label arity n}
      (h : Prefix a b)
      (c : Code Label arity n) :
      Prefix a (History.step b c)

namespace Prefix

theorem level_le
    {m n : Nat}
    {a : History Label arity m}
    {b : History Label arity n}
    (h : Prefix a b) :
    m ≤ n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step h c ih =>
      exact Nat.le_trans ih (Nat.le_succ _)

theorem trans
    {l m n : Nat}
    {a : History Label arity l}
    {b : History Label arity m}
    {c : History Label arity n}
    (hab : Prefix a b)
    (hbc : Prefix b c) :
    Prefix a c := by
  induction hbc generalizing a with
  | refl => exact hab
  | step h d ih =>
      exact Prefix.step (ih hab) d

/-- A prefix relation on equal levels is equality. -/
theorem heq_of_level_eq
    {m n : Nat}
    {a : History Label arity m}
    {b : History Label arity n}
    (h : Prefix a b)
    (hmn : m = n) :
    HEq a b := by
  subst n
  cases h with
  | refl => rfl
  | step h c =>
      have hle := Prefix.level_le h
      omega

/-- Two prefixes of one history are comparable. -/
theorem comparable
    {l m n : Nat}
    {a : History Label arity l}
    {b : History Label arity m}
    {c : History Label arity n}
    (hac : Prefix a c)
    (hbc : Prefix b c) :
    Prefix a b ∨ Prefix b a := by
  induction hac generalizing b with
  | refl =>
      exact Or.inr hbc
  | step hac d ih =>
      cases hbc with
      | refl =>
          exact Or.inl (Prefix.step hac d)
      | step hbc d' =>
          exact ih hbc

/-- Every lower level occurs on a history spine. -/
theorem exists_at_level
    {n : Nat}
    (h : History Label arity n)
    (m : Nat)
    (hm : m ≤ n) :
    ∃ a : History Label arity m, Prefix a h := by
  induction h generalizing m with
  | root =>
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      exact ⟨History.root, Prefix.refl _⟩
  | step h c ih =>
      by_cases htop : m = _ + 1
      · subst m
        exact ⟨History.step h c, Prefix.refl _⟩
      · have hmn : m ≤ _ := by omega
        obtain ⟨a, ha⟩ := ih m hmn
        exact ⟨a, Prefix.step ha c⟩

end Prefix

/-- Natural prefix order on total history nodes. -/
def Node.IsPrefix (x y : Node Label arity) : Prop :=
  Prefix x.2 y.2

instance instPartialOrderNode : PartialOrder (Node Label arity) where
  le := Node.IsPrefix
  le_refl x := Prefix.refl x.2
  le_trans x y z hxy hyz :=
    Prefix.trans hxy hyz
  le_antisymm x y hxy hyx := by
    rcases x with ⟨m, a⟩
    rcases y with ⟨n, b⟩
    change Prefix a b at hxy
    change Prefix b a at hyx
    have hmn : m ≤ n := hxy.level_le
    have hnm : n ≤ m := hyx.level_le
    have hEq : m = n := Nat.le_antisymm hmn hnm
    have hab : HEq a b :=
      Prefix.heq_of_level_eq hxy hEq
    subst n
    have hab' : a = b := eq_of_heq hab
    subst b
    rfl

theorem node_level_le
    {x y : Node Label arity}
    (hxy : x ≤ y) :
    x.level ≤ y.level :=
  Prefix.level_le hxy

theorem node_eq_of_le_level_eq
    {x y : Node Label arity}
    (hxy : x ≤ y)
    (hlev : x.level = y.level) :
    x = y := by
  rcases x with ⟨m, a⟩
  rcases y with ⟨n, b⟩
  change Prefix a b at hxy
  change m = n at hlev
  have hab : HEq a b :=
    Prefix.heq_of_level_eq hxy hlev
  subst n
  have hab' : a = b := eq_of_heq hab
  subst b
  rfl

theorem node_lower_linear
    {x y z : Node Label arity}
    (hx : x ≤ z)
    (hy : y ≤ z) :
    x ≤ y ∨ y ≤ x :=
  Prefix.comparable hx hy

theorem node_ancestor_exists
    (x : Node Label arity)
    (m : Nat)
    (hm : m ≤ x.level) :
    ∃ y : Node Label arity, y ≤ x ∧ y.level = m := by
  rcases x with ⟨n, h⟩
  change m ≤ n at hm
  obtain ⟨a, ha⟩ := Prefix.exists_at_level h m hm
  exact ⟨⟨m, a⟩, ha, rfl⟩

end FreeAncestral
end SuccessorTree

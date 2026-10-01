import SuccessorTree.Monoid
import Mathlib.Tactic

/-!
# Finite approximations AM^n_k

This is the finite-restriction notation used in Section 3.1 of the paper.
An approximation is a function on T(< n+k) which is the restriction of a
member of M fixing T(< n).
-/

namespace SuccessorTree

variable {Node : Type u} {Char : Type v} [PartialOrder Node]

def Below (S : STree Node Char) (r : Nat) :=
  {a : Node // S.tree.level a < r}

def ShapeMap.FixesBelow (F : ShapeMap S) (n : Nat) : Prop :=
  ∀ a : Node, S.tree.level a < n → F a = a

structure Approximation (M : SMTree S) (n k : Nat) where
  toFun : Below S (n + k) → Node
  extendable :
    ∃ F : ShapeMap S,
      M.Contains F ∧
      F.FixesBelow n ∧
      ∀ a : Below S (n + k), F a.1 = toFun a

namespace Approximation

instance (M : SMTree S) (n k : Nat) :
    CoeFun (Approximation M n k) (fun _ => Below S (n + k) → Node) :=
  ⟨Approximation.toFun⟩

@[ext] theorem ext
    {A B : Approximation M n k}
    (h : ∀ a, A a = B a) :
    A = B := by
  cases A with
  | mk f hf =>
      cases B with
      | mk g hg =>
          have hfg : f = g := funext h
          subst g
          rfl

noncomputable def extension (A : Approximation M n k) : ShapeMap S :=
  Classical.choose A.extendable

theorem extension_mem (A : Approximation M n k) :
    M.Contains A.extension :=
  (Classical.choose_spec A.extendable).1

theorem extension_fixes (A : Approximation M n k) :
    A.extension.FixesBelow n :=
  (Classical.choose_spec A.extendable).2.1

theorem extension_agrees
    (A : Approximation M n k) (a : Below S (n + k)) :
    A.extension a.1 = A a :=
  (Classical.choose_spec A.extendable).2.2 a

theorem fixes
    (A : Approximation M n k)
    (a : Below S (n + k))
    (ha : S.tree.level a.1 < n) :
    A a = a.1 := by
  rw [← A.extension_agrees a]
  exact A.extension_fixes a.1 ha

/-- Restriction of an actual monoid member fixing T(<n). -/
def restrict
    (F : ShapeMap S)
    (hF : M.Contains F)
    (hfix : F.FixesBelow n) :
    Approximation M n k where
  toFun := fun a => F a.1
  extendable := ⟨F, hF, hfix, fun _ => rfl⟩

@[simp] theorem restrict_apply
    (F : ShapeMap S) (hF : M.Contains F) (hfix : F.FixesBelow n)
    (a : Below S (n + k)) :
    restrict (M := M) (k := k) F hF hfix a = F a.1 := rfl

/-- Identity approximation. -/
def identity (M : SMTree S) (n k : Nat) :
    Approximation M n k :=
  restrict (M := M) (n := n) (k := k)
    (ShapeMap.id S) M.id_contains (by
      intro a ha
      rfl)

@[simp] theorem identity_apply
    (M : SMTree S) (n k : Nat) (a : Below S (n + k)) :
    identity M n k a = a.1 := rfl

/-- The one-level approximations used as the Hales--Jewett alphabet. -/
abbrev AM1 (M : SMTree S) (n : Nat) := Approximation M n 1

/-- The two-level approximations produced by the pigeonhole lemma. -/
abbrev AM2 (M : SMTree S) (n : Nat) := Approximation M n 2

/-- Paper condition tilde g(n)=n+1, expressed through any full extension. -/
def IsLetter (A : AM1 M n) : Prop :=
  A.extension.levelMap n = n + 1

def Letter (M : SMTree S) (n : Nat) :=
  {A : AM1 M n // A.IsLetter}

instance (M : SMTree S) (n : Nat) :
    Coe (Letter M n) (AM1 M n) := ⟨Subtype.val⟩

theorem letter_level
    (e : Letter M n) :
    e.1.extension.levelMap n = n + 1 :=
  e.2

end Approximation

end SuccessorTree

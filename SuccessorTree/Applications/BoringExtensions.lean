import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
# Boring extensions on finite words

Formalisation of Definition `def:boringext` from the manuscript.

Finite words of length `n` are represented by tuples `Fin n → Σ`.  The
operation `insertAt` is exactly
`a ↦ a_prefix ⌢ e(a_prefix) ⌢ a_suffix` from (B2).
-/

namespace SuccessorTree
namespace Boring

universe u

/-- A word of length `n` over `Σ`. -/
abbrev Word (Σ : Type u) (n : Nat) := Fin n → Σ

/-- Concatenate a prefix of length `m` and a suffix of length `n-m`. -/
def concat {Σ : Type u} {m n : Nat} (h : m ≤ n)
    (a : Word Σ m) (b : Word Σ (n - m)) : Word Σ n :=
  fun i => Fin.append a b (Fin.cast (by omega) i)

/-- Insert one letter in position `m` of a word of length `n`. -/
def insertAt {Σ : Type u} {m n : Nat} (h : m ≤ n)
    (x : Σ) (w : Word Σ n) : Word Σ (n + 1) :=
  Fin.insertNth ⟨m, by omega⟩ x w

@[simp] theorem insertAt_old
    {Σ : Type u} {m n : Nat} (h : m ≤ n)
    (x : Σ) (w : Word Σ n) (j : Fin n) :
    insertAt h x w (⟨m, by omega⟩ : Fin (n + 1)).succAbove j = w j := by
  simp [insertAt, Fin.insertNth_apply_succAbove]

/-- A family of boring extensions. -/
structure Family (Σ : Type u) where
  extensions : (n : Nat) → Set (Word Σ n → Σ)
  /-- (B1): every earlier coordinate can be duplicated at every later level. -/
  duplication :
    ∀ {n m : Nat} (h : n < m),
      (fun w : Word Σ m => w ⟨n, h⟩) ∈ extensions m
  /-- (B2): an extension can be transported past insertion of another
  boring coordinate. -/
  insertion :
    ∀ {m n : Nat} (h : m ≤ n)
      {e₁ : Word Σ m → Σ} {e₂ : Word Σ n → Σ},
      e₁ ∈ extensions m →
      e₂ ∈ extensions n →
      ∃ e₃ : Word Σ (n + 1) → Σ,
        e₃ ∈ extensions (n + 1) ∧
        ∀ (a : Word Σ m) (b : Word Σ (n - m)),
          e₃ (insertAt h (e₁ a) (concat h a b)) =
            e₂ (concat h a b)

namespace Family

variable {Σ : Type u} (E : Family Σ)

/-- Paper notation `e ∈ E_n`. -/
abbrev Mem {n : Nat} (e : Word Σ n → Σ) : Prop :=
  e ∈ E.extensions n

/-- Named wrapper for (B1). -/
theorem projection_mem {n m : Nat} (h : n < m) :
    (fun w : Word Σ m => w ⟨n, h⟩) ∈ E.extensions m :=
  E.duplication h

/-- Named wrapper for (B2).  Notice that the extension lifted from level
`n` is the *current* extension `e₂ : E_n`; this is the typing which is
used at every step of the composition proof in the manuscript. -/
theorem exists_lift
    {m n : Nat} (h : m ≤ n)
    {e₁ : Word Σ m → Σ} {e₂ : Word Σ n → Σ}
    (he₁ : e₁ ∈ E.extensions m)
    (he₂ : e₂ ∈ E.extensions n) :
    ∃ e₃ : Word Σ (n + 1) → Σ,
      e₃ ∈ E.extensions (n + 1) ∧
      ∀ (a : Word Σ m) (b : Word Σ (n - m)),
        e₃ (insertAt h (e₁ a) (concat h a b)) =
          e₂ (concat h a b) :=
  E.insertion h he₁ he₂

end Family

/-- The maximal family: every extension is boring. -/
def maximal (Σ : Type u) : Family Σ where
  extensions _ := Set.univ
  duplication _ := Set.mem_univ _
  insertion _ _ _ := by
    refine ⟨_, Set.mem_univ _, ?_⟩
    intro a b
    rfl

/-- The family consisting only of coordinate projections.  This is a useful
sanity check that (B2) has the intended variance: transporting a projection
past an insertion is projection to the corresponding old coordinate. -/
def projections (Σ : Type u) : Family Σ where
  extensions n :=
    {e | ∃ i : Fin n, e = fun w : Word Σ n => w i}
  duplication h := by
    exact ⟨⟨_, h⟩, rfl⟩
  insertion h he₁ he₂ := by
    rcases he₂ with ⟨j, rfl⟩
    let p : Fin (n + 1) := ⟨m, by omega⟩
    refine ⟨(fun w : Word Σ (n + 1) => w (p.succAbove j)), ?_, ?_⟩
    · exact ⟨p.succAbove j, rfl⟩
    · intro a b
      simp [insertAt, p, Fin.insertNth_apply_succAbove]

end Boring
end SuccessorTree

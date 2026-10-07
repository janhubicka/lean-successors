import SuccessorTree.FreeAncestralGap
import Mathlib.Tactic

/-! # The raw one-gap map on free ancestral histories

For a fixed target gap level m, a choice function selects one immediate child
for every source node on level m.  The raw map is identity below m, takes the
chosen child at level m, and above m replays the old transition code with all
ancestral parameter levels shifted across the inserted gap.
-/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat} [Fintype Label]

/-- Level map for inserting one target gap at m. -/
def gapLevel (m n : Nat) : Nat :=
  if n < m then n else n + 1

@[simp] theorem gapLevel_of_lt
    {m n : Nat} (h : n < m) :
    gapLevel m n = n := by
  simp [gapLevel, h]

@[simp] theorem gapLevel_of_ge
    {m n : Nat} (h : m ≤ n) :
    gapLevel m n = n + 1 := by
  simp [gapLevel, Nat.not_lt.mpr h]

/-- Raw history map which inserts one level at m.

The choice function supplies the code used to move a source level-m history
to its chosen child. -/
noncomputable def gapHistory
    (m : Nat)
    (choose : History Label arity m → Code Label arity m) :
    (n : Nat) →
      History Label arity n →
      History Label arity (gapLevel m n)
  | 0, h => by
      have hroot : h = History.root := history_zero_unique h
      subst h
      by_cases hm : 0 < m
      · simpa [gapLevel, hm] using
          (History.root : History Label arity 0)
      · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        subst m
        simpa [gapLevel] using
          (History.step History.root (choose History.root) :
            History Label arity 1)
  | n + 1, h => by
      cases h with
      | step p c =>
          by_cases hlt : n + 1 < m
          · simpa [gapLevel, hlt] using
              (History.step p c : History Label arity (n + 1))
          · by_cases heq : n + 1 = m
            · subst m
              simpa [gapLevel] using
                (History.step (History.step p c)
                  (choose (History.step p c)) :
                    History Label arity (n + 2))
            · have hnge : m ≤ n := by omega
              let gp0 := gapHistory m choose n p
              have gp :
                  History Label arity (n + 1) := by
                simpa [gapLevel, Nat.not_lt.mpr hnge] using gp0
              have hge : m ≤ n + 1 := by omega
              simpa [gapLevel, Nat.not_lt.mpr hge] using
                (History.step gp (shiftCode m c) :
                  History Label arity (n + 2))

/-- Total-node version of gapHistory. -/
noncomputable def gapNode
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (x : Node Label arity) :
    Node Label arity :=
  ⟨gapLevel m x.level, gapHistory m choose x.level x.2⟩

@[simp] theorem gapNode_level
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (x : Node Label arity) :
    (gapNode m choose x).level = gapLevel m x.level := rfl

theorem gapNode_level_of_lt
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    {x : Node Label arity}
    (hx : x.level < m) :
    (gapNode m choose x).level = x.level := by
  simp [gapNode_level, gapLevel, hx]

theorem gapNode_level_of_ge
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    {x : Node Label arity}
    (hx : m ≤ x.level) :
    (gapNode m choose x).level = x.level + 1 := by
  simp [gapNode_level, gapLevel, Nat.not_lt.mpr hx]

end FreeAncestral
end SuccessorTree

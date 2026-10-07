import SuccessorTree.FreeAncestralGapShape
import SuccessorTree.Monoid
import Mathlib.Tactic

/-! # Monoid-facing facts for the free ancestral tree

This file first proves that every one-gap shape map omits exactly the chosen
target level.  The M2/M3 instance is built on top of this fact.
-/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat}
variable [Fintype Label] [Nonempty Label]

/-- Empty intrinsic parameter tuple. -/
def emptyParamTuple (arity n : Nat) : ParamTuple arity n where
  len := ⟨0, Nat.succ_pos _⟩
  value := Fin.elim0

/-- Fixed label used only to witness that every free-history level is
inhabited. -/
noncomputable def defaultLabel : Label :=
  Classical.choice (inferInstance : Nonempty Label)

/-- Canonical history witnessing one node on every level. -/
noncomputable def canonicalHistory :
    (n : Nat) → History Label arity n
  | 0 => History.root
  | n + 1 =>
      History.step (canonicalHistory n)
        ⟨defaultLabel, emptyParamTuple arity n⟩

noncomputable def canonicalNode (n : Nat) :
    Node Label arity :=
  ⟨n, canonicalHistory n⟩

@[simp] theorem canonicalNode_level (n : Nat) :
    (canonicalNode (Label := Label) (arity := arity) n).level = n := rfl

theorem oneGapShapeMap_skipsOnly
    (m : Nat)
    (choose : History Label arity m → Code Label arity m) :
    (oneGapShapeMap m choose).SkipsOnly m := by
  ext k
  change
    (∃ x : Node Label arity,
      (oneGapShapeMap m choose x).level = k) ↔
        k ≠ m
  constructor
  · rintro ⟨x, hx⟩ hkm
    have hxM :
        (gapNode m choose x).level = m := by
      rw [← oneGapShapeMap_apply]
      exact hx.trans hkm
    by_cases hlt : x.level < m
    · have hlev :=
        gapNode_level_of_lt m choose hlt
      rw [hlev] at hxM
      omega
    · have hge : m ≤ x.level :=
        Nat.le_of_not_gt hlt
      have hlev :=
        gapNode_level_of_ge m choose hge
      rw [hlev] at hxM
      omega
  · intro hkm
    by_cases hlt : k < m
    · refine
        ⟨canonicalNode (Label := Label) (arity := arity) k, ?_⟩
      rw [oneGapShapeMap_apply]
      exact gapNode_level_of_lt m choose (by simpa using hlt)
    · have hmk : m < k := by omega
      let n := k - 1
      have hn : m ≤ n := by
        dsimp [n]
        omega
      refine
        ⟨canonicalNode (Label := Label) (arity := arity) n, ?_⟩
      rw [oneGapShapeMap_apply]
      have hlev :=
        gapNode_level_of_ge m choose
          (x := canonicalNode (Label := Label) (arity := arity) n)
          (by simpa using hn)
      dsimp [n] at hlev ⊢
      omega

end FreeAncestral
end SuccessorTree

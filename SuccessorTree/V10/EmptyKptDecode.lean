import SuccessorTree.V10.EmptyKptAdmissible
import Mathlib.Tactic

/-!
# Inverting empty-Kpt numerical parameter cuts

A positive E-column free cut is zero or the successor of exactly one
earlier ancestor index. This is an actual equivalence of the one-parameter
free-ancestral tuple type with the allowable numeric cuts, not merely a
count of their cardinalities.
-/

namespace SuccessorTree.V10.EmptyKpt

/-- Decode the free cut of a newly inserted ordinary vertex into its unique
empty or singleton ancestral-parameter tuple. -/
def parameterOfCut {n : Nat} (d : Fin (n + 1)) :
    SuccessorTree.FreeAncestral.ParamTuple 1 n :=
  if h : d.val = 0 then emptyParameter n
  else ancestorParameter ⟨d.val - 1, by have := d.isLt; omega⟩

@[simp] theorem parameterCut_parameterOfCut {n : Nat} (d : Fin (n + 1)) :
    parameterCut (parameterOfCut d) = d.val := by
  by_cases h : d.val = 0
  · simp [parameterOfCut, h]
  · have hpos : 0 < d.val := by omega
    simp only [parameterOfCut, dif_neg h, parameterCut_ancestor]
    omega

def toFinCut {n : Nat}
    (p : SuccessorTree.FreeAncestral.ParamTuple 1 n) : Fin (n + 1) :=
  ⟨parameterCut p, by have := parameterCut_le p; omega⟩

@[simp] theorem toFinCut_parameterOfCut {n : Nat} (d : Fin (n + 1)) :
    toFinCut (parameterOfCut d) = d := by
  apply Fin.ext
  exact parameterCut_parameterOfCut d

/-- For arity one the cut remembers the full parameter tuple, including
the distinction between no parameter and one parameter at ancestor zero. -/
theorem parameterCut_injective {n : Nat} :
    Function.Injective (parameterCut :
      SuccessorTree.FreeAncestral.ParamTuple 1 n → Nat) := by
  intro p q hpq
  rcases p with ⟨lp, vp⟩
  rcases q with ⟨lq, vq⟩
  fin_cases lp <;> fin_cases lq
  · have hval : vp = vq := by
      funext i
      exact Fin.elim0 i
    cases hval
    rfl
  · simp [parameterCut] at hpq
  · simp [parameterCut] at hpq
  · have h0 : vp (0 : Fin 1) = vq (0 : Fin 1) := by
      apply Fin.ext
      have hn : (vp (0 : Fin 1)).val + 1 =
          (vq (0 : Fin 1)).val + 1 := by
        simpa [parameterCut] using hpq
      omega
    have hval : vp = vq := by
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact h0
    cases hval
    rfl

@[simp] theorem parameterOfCut_toFinCut {n : Nat}
    (p : SuccessorTree.FreeAncestral.ParamTuple 1 n) :
    parameterOfCut (toFinCut p) = p := by
  apply parameterCut_injective
  simpa [toFinCut] using parameterCut_parameterOfCut (toFinCut p)

/-- The exact one-step E-column choice equivalence. -/
def parameterEquiv (n : Nat) :
    SuccessorTree.FreeAncestral.ParamTuple 1 n ≃ Fin (n + 1) where
  toFun := toFinCut
  invFun := parameterOfCut
  left_inv := parameterOfCut_toFinCut
  right_inv := toFinCut_parameterOfCut

end SuccessorTree.V10.EmptyKpt

import SuccessorTree.V10.HFinitePartial
import Mathlib.Tactic

/-!
# Numerical H: positive E-free cuts are necessarily odd

In the exact v10 H construction every generator of a positive
E-column is a REAL coordinate iota(i,q), hence even. If an
odd lower coordinate 2a+1 is generated, the following even
coordinate 2a+2 is generated as well. Consequently the first
missing coordinate of any nonempty generated E-column cannot
be even: every positive H free level is ODD.

This statement covers arbitrary finite H carrier vertices,
including fake ones and both top/non-top real generations.
It avoids a case-by-case division into H blocks and does not
assume an informal description of free levels: the proof
uses the ACTUAL finiteNumericH E predicate and the checked
canonical E-free-cut theorem.

This is the parameter half of excluding (I1) at intermediate
positive real generations in Proposition 6.44. The initial
seed-level exclusion is a separate application-specific input.
-/

namespace SuccessorTree.V10

/-- An odd lower H-coordinate in a generated E-column forces
its next even coordinate. Every generator itself is even. -/
theorem exactHEBool_odd_lower_forces_next_even
    (k a v : Nat)
    (h : exactHEBool k (2*a+1) v = true) :
    exactHEBool k (2*a+2) v = true := by
  obtain ⟨j,m,hm,hV,i,q,hi,hq,hGate,hLower⟩ :=
    (exactHEBool_true_iff k (2*a+1) v).1 h
  obtain ⟨t,hEven⟩ := hPosition_even k i q
  have hNext : 2*a+2 ≤ hPosition k i q := by omega
  exact (exactHEBool_true_iff k (2*a+2) v).2
    ⟨j,m,hm,hV,i,q,hi,hq,hGate,hNext⟩

/-- The ACTUAL enumerated finite H has no positive even
free level. Its free cut is canonical, not a caller-provided
numerical generation label. -/
theorem finiteNumericH_positive_freeLevel_odd
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N v : Nat) (hv : v < N)
    (hPos : 0 < (finiteNumericH K k N).freeLevel v) :
    ∃ a : Nat,
      (finiteNumericH K k N).freeLevel v = 2*a+1 := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let f : Nat := A.freeLevel v
  have hfPos : 0 < f := hPos
  by_cases hOdd : f % 2 = 1
  · refine ⟨f / 2, ?_⟩
    omega
  · have hEvenRem : f % 2 = 0 := by omega
    let a : Nat := f / 2
    have hEven : f = 2*a := by omega
    have haPos : 0 < a := by omega
    let b : Nat := a - 1
    have hBefore : f - 1 = 2*b+1 := by
      dsimp [b]
      omega
    have hAfter : f = 2*b+2 := by
      dsimp [b]
      omega
    have hEPrev : A.E (f-1) v = true :=
      (A.E_iff_freeLevel (f-1) v).2 (by dsimp [f]; omega)
    have hExactBefore : exactHEBool k (2*b+1) v = true := by
      have hFinite : finiteNumericHE k N (f-1) v = true := hEPrev
      have hExact : exactHEBool k (f-1) v = true :=
        ((finiteNumericHE_true_iff k N (f-1) v).1 hFinite).2
      rw [hBefore] at hExact
      exact hExact
    have hExactAfter : exactHEBool k (2*b+2) v = true :=
      exactHEBool_odd_lower_forces_next_even k b v hExactBefore
    have hENext : A.E f v = true := by
      change finiteNumericHE k N f v = true
      exact (finiteNumericHE_true_iff k N f v).2
        ⟨hv,by simpa only [hAfter] using hExactAfter⟩
    have hContradiction := (A.E_iff_freeLevel f v).1 hENext
    exact False.elim ((Nat.lt_irrefl f) hContradiction)

/-- A nonempty canonical E-socle cannot terminate at an even
real numerical H-position. Hence an actual selected parameter
whose free level is positive is never situated at positive
real generation r, independently of the forbidden language. -/
theorem finiteNumericH_positive_freeLevel_ne_realPosition
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N v i r : Nat)
    (hv : v < N)
    (hPos : 0 < (finiteNumericH K k N).freeLevel v) :
    (finiteNumericH K k N).freeLevel v ≠ hPosition k i r := by
  obtain ⟨a,hOdd⟩ := finiteNumericH_positive_freeLevel_odd K k N v hv hPos
  obtain ⟨t,hEven⟩ := hPosition_even k i r
  intro h
  omega

end SuccessorTree.V10

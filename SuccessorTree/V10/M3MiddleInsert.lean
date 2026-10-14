import SuccessorTree.V10.M3CloneProjection
import SuccessorTree.V10.LocalAgePartialInsertion
import Mathlib.Tactic

/-!
# Actual finite L+ insertion of the n-th canonical clone at level ell

The canonical M3 construction duplicates an earlier ordinary vertex n
at a later positive ordinary coordinate ell. Its new free E cut is the
genuine cut d=freeLevel_A(n). Both directed lower binary columns are
copied only below d; between d and ell they are false. At an upper
old vertex u the pair with the new vertex is copied from the old n-u
pair only if the E-cut of u reaches ell, and is zero otherwise.

This last gate is essential: omitting it would break E3. It is derived
from the original finite partial structure, not a new age hypothesis.
The ordinary singleton labels are copied exactly from n.

The module constructs an actual EnumeratedPartialStructure using the
existing one-coordinate insertPartial theorem, thus checking E spacing,
downward closure and the linked-pair axiom. Forbidden-age preservation
and identification of the canonical successor inputs are subsequent
steps, not conclusions of this file.
-/

namespace SuccessorTree.V10

/-- All L-data of the new coordinate ell that duplicates the existing
vertex n. New-to-old and old-to-new are separate Boolean functions;
both directions above ell are gated by the OLD free E cut of that vertex. -/
noncomputable def middleCloneInsertedLData
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) : InsertedLData db du dd :=
  { loop := A.L.binary n n
    unary := A.L.unary n
    diagonal := A.L.diagonal n
    incoming := fun x t =>
      if x < ell then
        if x < A.freeLevel n then A.L.binary x n t else false
      else if ell ≤ A.freeLevel x then A.L.binary x n t else false
    outgoing := fun x t =>
      if x < ell then
        if x < A.freeLevel n then A.L.binary n x t else false
      else if ell ≤ A.freeLevel x then A.L.binary n x t else false }

/-- Both directed lower bits agree with the earlier vertex n exactly
through its own free socle. No positive relation is inserted elsewhere
below ell. -/
theorem middleCloneInsertedLData_lower
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell n x : Nat) (hx : x < ell)
    (t : Fin db) :
    (middleCloneInsertedLData A ell n).incoming x t =
      (if x < A.freeLevel n then A.L.binary x n t else false) ∧
    (middleCloneInsertedLData A ell n).outgoing x t =
      (if x < A.freeLevel n then A.L.binary n x t else false) := by
  constructor <;> simp [middleCloneInsertedLData, hx]

/-- All pairs to an upper vertex u are copied iff its original
free cut reaches the new ordinary level. This is the exact E3 gate. -/
theorem middleCloneInsertedLData_upper
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell n x : Nat) (hx : ell ≤ x)
    (t : Fin db) :
    (middleCloneInsertedLData A ell n).incoming x t =
      (if ell ≤ A.freeLevel x then A.L.binary x n t else false) ∧
    (middleCloneInsertedLData A ell n).outgoing x t =
      (if ell ≤ A.freeLevel x then A.L.binary n x t else false) := by
  have hNot : ¬ x < ell := Nat.not_lt.mpr hx
  constructor <;> simp [middleCloneInsertedLData, hNot]

/-- Actual M3 one-level finite insertion, not an assumed embedding.
The new E cut is the source vertex n's unique old cut, so it satisfies
the spacing gate automatically for n<ell. The gated L data give both
required E3 linkage implications and all remaining partial-structure
axioms are supplied by insertPartial. -/
noncomputable def middleCloneInsertPartial
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell) :
    EnumeratedPartialStructure db du dd := by
  let d := A.freeLevel n
  let D := middleCloneInsertedLData A ell n
  have hPos : 0 < ell := by omega
  have hd : d ≤ ell :=
    (A.freeLevel_le n).trans (Nat.le_of_lt hn)
  have hGate : d = 0 ∨ d < ell :=
    Or.inr (lt_of_le_of_lt (A.freeLevel_le n) hn)
  have hBelow : ∀ x, x < ell →
      (∃ t : Fin db, D.incoming x t = true ∨
        D.outgoing x t = true) → x < d := by
    intro x hx hlink
    by_contra hnot
    have hGateNeg : ¬ x < A.freeLevel n := Nat.not_lt.mpr (by omega)
    simp [D, middleCloneInsertedLData, hx, hGateNeg] at hlink
  have hAbove : ∀ y, ell ≤ y → y < A.size →
      (∃ t : Fin db, D.outgoing y t = true ∨
        D.incoming y t = true) → ell ≤ A.freeLevel y := by
    intro y hy hySize hlink
    by_contra hnot
    have hyNot : ¬ y < ell := Nat.not_lt.mpr hy
    have hGateNeg : ¬ ell ≤ A.freeLevel y := by omega
    simp [D, middleCloneInsertedLData, hyNot, hGateNeg] at hlink
  exact insertPartial A ell d D hell hPos hd hGate hBelow hAbove

/-- The inserted structure has exactly one more ordinary coordinate,
and the original L-structure is copied under the literal insertion
address. All negative directed L atoms are preserved too. -/
theorem middleCloneInsertPartial_isLInsertion
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell) :
    IsLInsertion A (middleCloneInsertPartial A ell n hell hn) ell := by
  unfold middleCloneInsertPartial
  exact insertPartial_isLInsertion A ell (A.freeLevel n)
    (middleCloneInsertedLData A ell n)
    hell (by omega)
    ((A.freeLevel_le n).trans (Nat.le_of_lt hn))
    (Or.inr (lt_of_le_of_lt (A.freeLevel_le n) hn))
    (by
      intro x hx hlink
      by_contra hnot
      have hGateNeg : ¬ x < A.freeLevel n := Nat.not_lt.mpr (by omega)
      simp [middleCloneInsertedLData, hx, hGateNeg] at hlink)
    (by
      intro y hy hySize hlink
      by_contra hnot
      have hyNot : ¬ y < ell := Nat.not_lt.mpr hy
      have hGateNeg : ¬ ell ≤ A.freeLevel y := by omega
      simp [middleCloneInsertedLData, hyNot, hGateNeg] at hlink)

end SuccessorTree.V10

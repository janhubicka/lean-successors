import SuccessorTree.V10.EmptyKptCutHistory
import SuccessorTree.V10.RawTypeMeet
import Mathlib.Tactic

/-!
# Empty-language Kpt partial types from ancestral cut histories

The ordinary E-column at position `j` is the initial segment
`{i : i < cut(j)}`. There is no ordinary L-data, and the designated
type vertex has the entire initial E-socle as incoming column.

This proves the literal partial-type record and its spacing/downward
properties; realizing these records inside an admissible finite partial
structure is the next bridge, not an assumption made here.
-/

namespace SuccessorTree.V10.EmptyKpt

/-- Actual free cut of a numbered ordinary column. The extra initial
column has cut zero. -/
def ordinaryCutAt : {n : Nat} → (h : CutHistory n) → Fin (n + 1) → Nat
  | _, .root, _ => 0
  | _, .step (n := n) h p, j =>
      if hlast : j.val = n + 1 then
        parameterCut p
      else
        ordinaryCutAt h ⟨j.val, by omega⟩

@[simp] theorem ordinaryCutAt_zero :
    ∀ {n : Nat} (h : CutHistory n),
      ordinaryCutAt h ⟨0, by omega⟩ = 0 := by
  intro n h
  induction h with
  | root => rfl
  | @step n h p ih =>
      simp [ordinaryCutAt, ih]

/-- On positive columns the free cut is strictly smaller than the
column position, as required by the E spacing axiom. -/
theorem ordinaryCutAt_lt_of_pos :
    ∀ {n : Nat} (h : CutHistory n) (j : Fin (n + 1)),
      0 < j.val → ordinaryCutAt h j < j.val := by
  intro n h
  induction h with
  | root =>
      intro j hj
      have := j.isLt
      omega
  | @step n h p ih =>
      intro j hj
      unfold ordinaryCutAt
      split_ifs with hlast
      · have hcut := parameterCut_le p
        omega
      · have hle : j.val < n + 1 := by
          have := j.isLt
          omega
        exact ih ⟨j.val, hle⟩ hj

/-- Complete finite partial L+ record with empty L-signature. -/
def emptyPartialType {n : Nat} (h : CutHistory n) :
    PartialTypeWithE (n + 1) 0 0 0 where
  lReduct :=
    { binary := fun _ _ r => Fin.elim0 r
      unary := fun _ r => Fin.elim0 r
      diagonal := fun _ r => Fin.elim0 r }
  eRelation := fun x y =>
    match x, y with
    | some i, some j => decide (i.val < ordinaryCutAt h j)
    | some _, none => true
    | _, _ => false

/-- The corresponding raw partial-type node is one level beyond the
free-ancestral history. -/
def rawEmptyNode {n : Nat} (h : CutHistory n) :
    RawPartialTypeNode 0 0 0 :=
  ⟨n + 1, emptyPartialType h⟩

@[simp] theorem emptyPartialType_ordinaryE {n : Nat}
    (h : CutHistory n) (i j : Fin (n + 1)) :
    (emptyPartialType h).eRelation (some i) (some j) =
      decide (i.val < ordinaryCutAt h j) := rfl

@[simp] theorem emptyPartialType_typeE {n : Nat}
    (h : CutHistory n) (i : Fin (n + 1)) :
    (emptyPartialType h).eRelation (some i) none = true := rfl

@[simp] theorem emptyPartialType_reverseE {n : Nat}
    (h : CutHistory n) (i : Fin (n + 1)) :
    (emptyPartialType h).eRelation none (some i) = false := rfl

@[simp] theorem emptyPartialType_typeLoop {n : Nat}
    (h : CutHistory n) :
    (emptyPartialType h).eRelation none none = false := rfl

/-- The ordinary E-columns satisfy the required spacing. -/
theorem emptyPartialType_spaced {n : Nat}
    (h : CutHistory n) (i j : Fin (n + 1))
    (hE : (emptyPartialType h).eRelation (some i) (some j) = true) :
    i.val + 1 < j.val := by
  have hi : i.val < ordinaryCutAt h j := by
    simpa [emptyPartialType, decide_eq_true_eq] using hE
  have hjpos : 0 < j.val := by
    by_contra hneg
    have hjzero : j.val = 0 := by omega
    have hjindex : j = ⟨0, by omega⟩ := Fin.ext hjzero
    rw [hjindex, ordinaryCutAt_zero] at hi
    omega
  have hcut := ordinaryCutAt_lt_of_pos h j hjpos
  omega

/-- Every smaller ordinary predecessor belongs to the same E-column. -/
theorem emptyPartialType_downward {n : Nat}
    (h : CutHistory n) (i i' j : Fin (n + 1))
    (hsmaller : i'.val < i.val)
    (hE : (emptyPartialType h).eRelation (some i) (some j) = true) :
    (emptyPartialType h).eRelation (some i') (some j) = true := by
  have hi : i.val < ordinaryCutAt h j := by
    simpa [emptyPartialType, decide_eq_true_eq] using hE
  simp [emptyPartialType, decide_eq_true_eq]
  omega

end SuccessorTree.V10.EmptyKpt

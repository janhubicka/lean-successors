import SuccessorTree.FreeAncestral
import Mathlib.Tactic

/-!
# The empty-language partial-type tree: finite free-cut histories

For the empty relational signature and empty forbidden family, an ordinary
E-column in a partial type is specified by its cut. At the first ordinary
position the cut is zero; at position `n+1` the cut is either zero or the
successor of an ancestor index `k < n`.

This module identifies the *finite successor codes* with the intrinsic
one-parameter, one-letter free-ancestral histories. The further equivalence
with `admissibleKptSTree []`, and the resulting shape-map and Ellentuck
neighborhood transport, are separate proof obligations; they are not assumed
here. In particular, finite-code agreement alone does not prove the EA
obstruction.
-/

namespace SuccessorTree.V10.EmptyKpt

open SuccessorTree.FreeAncestral

/-- The free cut of the new ordinary E-column, read from a possible single
ancestral parameter. The index is shifted by one because Kpt has a fixed
extra ordinary vertex in its initial socle. -/
def parameterCut {n : Nat} (p : ParamTuple 1 n) : Nat :=
  if h : p.len.val = 0 then 0 else (p.value ⟨0, by omega⟩).val + 1

/-- The canonical E-cut never reaches the vertex itself; this is exactly
what the spacing axiom requires at the next ordinary column. -/
theorem parameterCut_le {n : Nat} (p : ParamTuple 1 n) :
    parameterCut p ≤ n := by
  classical
  unfold parameterCut
  split_ifs with h
  · omega
  · have hv := (p.value ⟨0, by omega⟩).isLt
    omega

/-- The no-parameter successor has cut zero. -/
def emptyParameter (n : Nat) : ParamTuple 1 n where
  len := ⟨0, by decide⟩
  value := fun i => Fin.elim0 i

/-- A single ancestral parameter with index `k<n` has E-cut `k+1`. -/
def ancestorParameter {n : Nat} (k : Fin n) : ParamTuple 1 n where
  len := ⟨1, by decide⟩
  value := fun _ => k

@[simp] theorem parameterCut_empty (n : Nat) :
    parameterCut (emptyParameter n) = 0 := by
  simp [parameterCut, emptyParameter]

@[simp] theorem parameterCut_ancestor {n : Nat} (k : Fin n) :
    parameterCut (ancestorParameter k) = k.val + 1 := by
  simp [parameterCut, ancestorParameter]

/-- The finite Kpt column-history codes. A step at history level `n`
chooses the next cut `0` or `k+1` for an earlier ancestor `k<n`.
Keeping the actual `ParamTuple` avoids quotienting its canonical
empty/singleton source representation. -/
inductive CutHistory : Nat → Type
  | root : CutHistory 0
  | step {n : Nat} : CutHistory n → ParamTuple 1 n → CutHistory (n + 1)

/-- Encode a one-letter, one-parameter free history as E-column data. -/
def toCutHistory : {n : Nat} → History Unit 1 n → CutHistory n
  | _, .root => .root
  | _, .step h c => .step (toCutHistory h) c.params

/-- Every finite E-column history can be read as a free-ancestral history.
The terminal letter is unique in the empty relational signature. -/
def fromCutHistory : {n : Nat} → CutHistory n → History Unit 1 n
  | _, .root => .root
  | _, .step h p => .step (fromCutHistory h) ⟨(), p⟩

@[simp] theorem to_from :
    ∀ {n : Nat} (h : CutHistory n),
      toCutHistory (fromCutHistory h) = h := by
  intro n h
  induction h with
  | root => rfl
  | step h p ih =>
      simp [toCutHistory, fromCutHistory, ih]

@[simp] theorem from_to :
    ∀ {n : Nat} (h : History Unit 1 n),
      fromCutHistory (toCutHistory h) = h := by
  intro n h
  induction h with
  | root => rfl
  | step h c ih =>
      rcases c with ⟨label, p⟩
      cases label
      simp [toCutHistory, fromCutHistory, ih]

/-- Exact finite-level bijection, including the level-zero history. -/
def historyEquiv (n : Nat) : History Unit 1 n ≃ CutHistory n where
  toFun := toCutHistory
  invFun := fromCutHistory
  left_inv := from_to
  right_inv := to_from

@[simp] theorem historyEquiv_root :
    historyEquiv 0 History.root = CutHistory.root := rfl

/-- The complete sequence of free cuts on the ordinary vertices of a
partial type of level `n+1`: first `d₀=0`, then one cut per history step. -/
def ordinaryCuts : {n : Nat} → CutHistory n → List Nat
  | _, .root => [0]
  | _, .step h p => ordinaryCuts h ++ [parameterCut p]

@[simp] theorem ordinaryCuts_length :
    ∀ {n : Nat} (h : CutHistory n),
      (ordinaryCuts h).length = n + 1 := by
  intro n h
  induction h with
  | root => rfl
  | @step n h p ih =>
      simp [ordinaryCuts, ih]

@[simp] theorem ordinaryCuts_step {n : Nat}
    (h : CutHistory n) (p : ParamTuple 1 n) :
    ordinaryCuts (CutHistory.step h p) =
      ordinaryCuts h ++ [parameterCut p] := rfl

/-- The actual numerical cut inserted at the successor step fits below
its new ordinary position `n+1`, leaving the mandatory E-gap. -/
theorem insertedCut_spaced {n : Nat}
    (h : CutHistory n) (p : ParamTuple 1 n) :
    parameterCut p < n + 1 := by
  have := parameterCut_le p
  omega

end SuccessorTree.V10.EmptyKpt

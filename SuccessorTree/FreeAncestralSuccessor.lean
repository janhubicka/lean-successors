import SuccessorTree.FreeAncestralLevelTree
import SuccessorTree.Successor
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-! # Successor helpers for the free ancestral tree

The intrinsic code stores only an ordered tuple of ancestor levels. This file
decodes that tuple to the actual predecessor nodes expected by the successor
API and defines the corresponding immediate child.
-/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat} [Fintype Label]

/-- Decode an intrinsic ancestral parameter tuple at the base node a to the
ordered list of actual predecessor nodes used by the external successor API. -/
noncomputable def paramNodes
    (a : Node Label arity)
    (t : ParamTuple arity a.level) :
    List (Node Label arity) :=
  List.ofFn fun j =>
    LevelTree.ancestor a (t.value j).val
      (Nat.le_of_lt (t.value j).isLt)

@[simp] theorem length_paramNodes
    (a : Node Label arity)
    (t : ParamTuple arity a.level) :
    (paramNodes a t).length = t.len.val := by
  simp [paramNodes]

theorem mem_paramNodes_level_lt
    {a x : Node Label arity}
    {t : ParamTuple arity a.level}
    (hx : x ∈ paramNodes a t) :
    LevelTree.lev x < LevelTree.lev a := by
  simp only [paramNodes, List.mem_ofFn] at hx
  obtain ⟨j, rfl⟩ := hx
  rw [LevelTree.level_ancestor]
  exact (t.value j).isLt

/-- The immediate history child coded by one intrinsic transition. -/
def child :
    (a : Node Label arity) →
    ParamTuple arity a.level →
    Label →
    Node Label arity
  | ⟨n, h⟩, t, c =>
      ⟨n + 1, History.step h ⟨c, t⟩⟩

@[simp] theorem child_level
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (c : Label) :
    (child a t c).level = a.level + 1 := by
  rcases a with ⟨n, h⟩
  rfl

theorem base_le_child
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (c : Label) :
    a ≤ child a t c := by
  rcases a with ⟨n, h⟩
  exact Prefix.step (Prefix.refl h) ⟨c, t⟩

theorem base_covBy_child
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (c : Label) :
    a ⋖ child a t c := by
  apply LevelTree.covBy_of_le_level_succ
    (base_le_child a t c)
  simp [child_level]

/-- A parameter list is intrinsic at a when it is the canonical decoding of
one bounded ancestral tuple. -/
def HasParams
    (a : Node Label arity)
    (p : List (Node Label arity)) : Prop :=
  ∃ t : ParamTuple arity a.level, paramNodes a t = p

noncomputable def chosenTuple
    (a : Node Label arity)
    (p : List (Node Label arity))
    (h : HasParams a p) :
    ParamTuple arity a.level :=
  Classical.choose h

theorem chosenTuple_spec
    (a : Node Label arity)
    (p : List (Node Label arity))
    (h : HasParams a p) :
    paramNodes a (chosenTuple a p h) = p :=
  Classical.choose_spec h

/-- Canonical free successor. It is defined exactly on canonical ancestral
parameter lists. -/
noncomputable def freeSucc
    (a : Node Label arity)
    (p : List (Node Label arity))
    (c : Label) :
    Option (Node Label arity) :=
  if h : HasParams a p then
    some (child a (chosenTuple a p h) c)
  else
    none

theorem freeSucc_eq_some_data
    {a b : Node Label arity}
    {p : List (Node Label arity)}
    {c : Label}
    (h : freeSucc a p c = some b) :
    ∃ t : ParamTuple arity a.level,
      paramNodes a t = p ∧ b = child a t c := by
  classical
  unfold freeSucc at h
  split at h
  next hp =>
    refine ⟨chosenTuple a p hp, chosenTuple_spec a p hp, ?_⟩
    exact (Option.some.inj h).symm
  next hp =>
    simp at h

theorem freeSucc_s1
    {a b : Node Label arity}
    {p : List (Node Label arity)}
    {c : Label}
    (h : freeSucc a p c = some b) :
    a ⋖ b ∧
      ∀ x ∈ p, LevelTree.lev x < LevelTree.lev a := by
  obtain ⟨t, htp, rfl⟩ := freeSucc_eq_some_data h
  refine ⟨base_covBy_child a t c, ?_⟩
  intro x hx
  apply mem_paramNodes_level_lt (t := t)
  simpa [htp] using hx

end FreeAncestral
end SuccessorTree

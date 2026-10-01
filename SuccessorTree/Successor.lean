import SuccessorTree.Tree

/-!
# Trees with a successor operation

Formalization of Definition `def:successor` (S1--S3) from the paper.

The partial successor operation is represented by an `Option`.  The paper's
parameter bound “level at most level(a)-1” is written equivalently as
`lev p < lev a`; this avoids truncated subtraction at level zero.
-/

namespace SuccessorTree

/-- An S-tree on a fixed levelled tree and alphabet. -/
structure STree (T : Type u) (Label : Type v)
    [PartialOrder T] [LevelTree T] where
  succ : T → List T → Label → Option T
  s1 : ∀ {a : T} {p : List T} {c : Label} {b : T},
    succ a p c = some b →
      a ⋖ b ∧ ∀ x ∈ p, LevelTree.lev x < LevelTree.lev a
  s2 : ∀ {a b x : T} {p q : List T} {c d : Label},
    succ a p c = some x →
    succ b q d = some x →
    a = b ∧ p = q ∧ c = d
  s3 : ∀ {a b : T}, a ⋖ b → ∃ p : List T, ∃ c : Label, succ a p c = some b

namespace STree

variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable (S : STree T Label)

/-- The successor operation is defined at `(a,p,c)`. -/
def Defined (a : T) (p : List T) (c : Label) : Prop :=
  ∃ b : T, S.succ a p c = some b

/-- S1: a defined successor is an immediate successor of its base. -/
theorem covBy_of_succ_eq_some {a b : T} {p : List T} {c : Label}
    (h : S.succ a p c = some b) : a ⋖ b :=
  (S.s1 h).1

/-- S1: all parameters lie strictly below the base level. -/
theorem parameter_level_lt {a b : T} {p : List T} {c : Label}
    (h : S.succ a p c = some b) {x : T} (hx : x ∈ p) :
    LevelTree.lev x < LevelTree.lev a :=
  (S.s1 h).2 x hx

/-- At level zero, S1 forces the parameter list to be empty. -/
theorem parameters_nil_at_level_zero {a b : T} {p : List T} {c : Label}
    (ha : LevelTree.lev a = 0) (h : S.succ a p c = some b) : p = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  have hp := S.parameter_level_lt h hx
  simpa [ha] using hp

/-- In the injectivity axiom S2, equality of the bases is already forced by
S1 and uniqueness of immediate predecessors in a tree. -/
theorem base_eq_of_same_successor
    {a b x : T} {p q : List T} {c d : Label}
    (ha : S.succ a p c = some x)
    (hb : S.succ b q d = some x) : a = b := by
  have hax : a ⋖ x := S.covBy_of_succ_eq_some ha
  have hbx : b ⋖ x := S.covBy_of_succ_eq_some hb
  rcases LevelTree.comparable_below hax.le hbx.le with hab | hba
  · rcases hab.eq_or_lt with h | h
    · exact h
    · exact False.elim ((not_covBy_of_lt_of_lt h hbx.lt) hax)
  · rcases hba.eq_or_lt with h | h
    · exact h.symm
    · exact False.elim ((not_covBy_of_lt_of_lt h hax.lt) hbx)

end STree

end SuccessorTree

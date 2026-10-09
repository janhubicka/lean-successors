import SuccessorTree.V10.EndDuplicateE
import SuccessorTree.V10.PartialTypeRestriction
import Mathlib.Tactic

/-!
# Complete L-reduct of a terminal M3 duplicate

Append a new ordinary vertex N=|A|. It has the same singleton
type as an earlier vertex n, and its directed L-relations to old
vertices u are copied from those of n precisely for
u<fl_A(n). All pairs involving the new vertex and an old
u>=fl_A(n) have no L-relations. The full old structure is kept.

We prove exact copying of all old tuples, both directions
of every permitted crossing, absence of all other old/new
tuples, and literal equality of the duplicated vertex's
type through the old source free cut.

This is the L component of the one-step duplication underlying
M3 of Proposition 6.39. It is not yet a global one-level skip
shape-preserving map on the Kpt tree.
-/

namespace SuccessorTree.V10

/-- The exact L-reduct with one final duplicate vertex. -/
noncomputable def duplicateEndL
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) : AgeTestModel db du dd :=
  { carrier := {x | x < A.size + 1}
    binary := fun x y r =>
      if x = A.size then
        if y = A.size then A.L.binary n n r
        else if y < A.freeLevel n then A.L.binary n y r
        else false
      else if y = A.size then
        if x < A.freeLevel n then A.L.binary x n r
        else false
      else A.L.binary x y r
    unary := fun x r =>
      if x = A.size then A.L.unary n r else A.L.unary x r
    diagonal := fun x r =>
      if x = A.size then A.L.diagonal n r else A.L.diagonal x r }

/-- The old L-reduct is an EXACT induced initial substructure, not
merely a weak substructure or preservation of positive tuples. -/
theorem duplicateEndL_old
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n x y : Nat) (hx : x < A.size) (hy : y < A.size) :
    (∀ r : Fin db,
      (duplicateEndL A n).binary x y r = A.L.binary x y r) ∧
    (∀ r : Fin du,
      (duplicateEndL A n).unary x r = A.L.unary x r) ∧
    (∀ r : Fin dd,
      (duplicateEndL A n).diagonal x r = A.L.diagonal x r) := by
  have hxn : x ≠ A.size := Nat.ne_of_lt hx
  have hyn : y ≠ A.size := Nat.ne_of_lt hy
  constructor
  · intro r
    simp [duplicateEndL, hxn, hyn]
  constructor
  · intro r
    simp [duplicateEndL, hxn]
  · intro r
    simp [duplicateEndL, hxn]

/-- All unary, diagonal and self-binary atoms of the new ordinary
vertex are exactly the singleton atoms of its earlier original. -/
theorem duplicateEndL_newSingleton
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) :
    (∀ r : Fin db,
      (duplicateEndL A n).binary A.size A.size r =
        A.L.binary n n r) ∧
    (∀ r : Fin du,
      (duplicateEndL A n).unary A.size r = A.L.unary n r) ∧
    (∀ r : Fin dd,
      (duplicateEndL A n).diagonal A.size r =
        A.L.diagonal n r) := by
  constructor
  · intro r
    simp [duplicateEndL]
  constructor
  · intro r
    simp [duplicateEndL]
  · intro r
    simp [duplicateEndL]

/-- Every directed old-new bit below the original free cut is
copied from the older vertex n, including nonedges. -/
theorem duplicateEndL_cross_below
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n u : Nat) (hn : n < A.size)
    (hu : u < A.freeLevel n)
    (r : Fin db) :
    (duplicateEndL A n).binary u A.size r =
      A.L.binary u n r ∧
    (duplicateEndL A n).binary A.size u r =
      A.L.binary n u r := by
  have hun : u ≠ A.size := by
    have hfree := A.freeLevel_le n
    omega
  constructor
  · simp [duplicateEndL, hun, hu]
  · simp [duplicateEndL, hun, hu]

/-- Every directed relation between the new vertex and an old
coordinate at or above the free cut is absent. -/
theorem duplicateEndL_cross_above
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n u : Nat)
    (hn : n < A.size)
    (hu : A.freeLevel n ≤ u) (huold : u < A.size)
    (r : Fin db) :
    (duplicateEndL A n).binary u A.size r = false ∧
    (duplicateEndL A n).binary A.size u r = false := by
  have hun : u ≠ A.size := Nat.ne_of_lt huold
  have hnot : ¬ u < A.freeLevel n := Nat.not_lt.mpr hu
  constructor
  · simp [duplicateEndL, hun, hnot]
  · simp [duplicateEndL, hun, hnot]

/-- The complete induced L-type of the cloned final vertex over
the original E-socle agrees with that of its older original. -/
theorem duplicateEndL_newType
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) (hn : n < A.size) :
    RelationalPrefixType.ofAgeModel
        (duplicateEndL A n) (A.freeLevel n) A.size =
      RelationalPrefixType.ofAgeModel A.L (A.freeLevel n) n := by
  apply RelationalPrefixType.eq_of_atoms
  · intro x y r
    cases x with
    | none =>
      cases y with
      | none => exact (duplicateEndL_newSingleton A n).1 r
      | some y =>
        exact (duplicateEndL_cross_below A n y.val hn y.isLt r).2
    | some x =>
      cases y with
      | none =>
        exact (duplicateEndL_cross_below A n x.val hn x.isLt r).1
      | some y =>
        have hx : x.val < A.size :=
          lt_trans (lt_of_lt_of_le x.isLt (A.freeLevel_le n)) hn
        have hy : y.val < A.size :=
          lt_trans (lt_of_lt_of_le y.isLt (A.freeLevel_le n)) hn
        exact (duplicateEndL_old A n x.val y.val hx hy).1 r
  · intro x r
    cases x with
    | none => exact (duplicateEndL_newSingleton A n).2.1 r
    | some x =>
      have hx : x.val < A.size :=
        lt_trans (lt_of_lt_of_le x.isLt (A.freeLevel_le n)) hn
      exact (duplicateEndL_old A n x.val x.val hx hx).2.1 r
  · intro x r
    cases x with
    | none => exact (duplicateEndL_newSingleton A n).2.2 r
    | some x =>
      have hx : x.val < A.size :=
        lt_trans (lt_of_lt_of_le x.isLt (A.freeLevel_le n)) hn
      exact (duplicateEndL_old A n x.val x.val hx hx).2.2 r

end SuccessorTree.V10

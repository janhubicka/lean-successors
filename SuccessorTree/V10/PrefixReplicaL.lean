import SuccessorTree.V10.PrefixReplicaE
import SuccessorTree.V10.RelationalTypeReduct
import Mathlib.Tactic

/-!
# Copying the complete L-reduct into a one-filler partial-type replica

Let A be an ambient enumerated partial structure and let d be a
shortened type cut of its vertex v. Retain coordinates below d, place
one neutral filler at d and relocate v to d+1.

The exact L relations of the replica are obtained by a partial
address map: old coordinates map to themselves, d+1 maps to v, and
the filler has no address. This preserves every directed binary
atom (present or absent), every unary and diagonal atomic fact, and
every complete induced L type through d. The filler is neutral.

This module does not yet prove the combined replica's E3 axiom or
preservation of the forbidden-free age. Those require further
arguments, and the neutral singleton must be allowed.
-/

namespace SuccessorTree.V10

/-- The order-preserving partial address map from the replica into
the original ambient structure, undefined precisely at the filler
coordinate and outside the replica's domain. -/
def prefixReplicaAddress (d v x : Nat) : Option Nat :=
  if x < d then some x
  else if x = d + 1 then some v
  else none

theorem prefixReplicaAddress_old
    (d v x : Nat) (hx : x < d) :
    prefixReplicaAddress d v x = some x := by
  simp [prefixReplicaAddress, hx]

theorem prefixReplicaAddress_last
    (d v : Nat) :
    prefixReplicaAddress d v (d + 1) = some v := by
  have h : ¬ d + 1 < d := by omega
  simp [prefixReplicaAddress, h]

theorem prefixReplicaAddress_filler
    (d v : Nat) :
    prefixReplicaAddress d v d = none := by
  simp [prefixReplicaAddress]

/-- The exact L-reduct on the old initial socle, neutral filler and
relocated type vertex. Every directed binary tuple is copied only
when BOTH coordinates have original addresses. -/
def prefixReplicaL
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (d v : Nat) : AgeTestModel db du dd :=
  { carrier := {x | x < d + 2}
    binary := fun x y r =>
      match prefixReplicaAddress d v x, prefixReplicaAddress d v y with
      | some a, some b => A.L.binary a b r
      | _, _ => false
    unary := fun x r =>
      match prefixReplicaAddress d v x with
      | some a => A.L.unary a r
      | none => false
    diagonal := fun x r =>
      match prefixReplicaAddress d v x with
      | some a => A.L.diagonal a r
      | none => false }

/-- The old socle's full L-structure is retained, including all
binary directions and singleton data. -/
theorem prefixReplicaL_old
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (d v : Nat) (i j : Fin d) :
    (∀ r : Fin db,
      (prefixReplicaL A d v).binary i.val j.val r =
        A.L.binary i.val j.val r) ∧
    (∀ r : Fin du,
      (prefixReplicaL A d v).unary i.val r =
        A.L.unary i.val r) ∧
    (∀ r : Fin dd,
      (prefixReplicaL A d v).diagonal i.val r =
        A.L.diagonal i.val r) := by
  constructor
  · intro r
    simp [prefixReplicaL,
      prefixReplicaAddress_old d v i.val i.isLt,
      prefixReplicaAddress_old d v j.val j.isLt]
  constructor
  · intro r
    simp [prefixReplicaL,
      prefixReplicaAddress_old d v i.val i.isLt]
  · intro r
    simp [prefixReplicaL,
      prefixReplicaAddress_old d v i.val i.isLt]

/-- The L singleton at the new type vertex equals the original
singleton, including diagonal loops. -/
theorem prefixReplicaL_last_singleton
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (d v : Nat) :
    (∀ r : Fin db,
      (prefixReplicaL A d v).binary (d + 1) (d + 1) r =
        A.L.binary v v r) ∧
    (∀ r : Fin du,
      (prefixReplicaL A d v).unary (d + 1) r =
        A.L.unary v r) ∧
    (∀ r : Fin dd,
      (prefixReplicaL A d v).diagonal (d + 1) r =
        A.L.diagonal v r) := by
  constructor
  · intro r
    simp [prefixReplicaL, prefixReplicaAddress_last]
  constructor
  · intro r
    simp [prefixReplicaL, prefixReplicaAddress_last]
  · intro r
    simp [prefixReplicaL, prefixReplicaAddress_last]

/-- Both ordered orientations of every relation between the
relocated vertex and the original initial socle are copied exactly. -/
theorem prefixReplicaL_cross
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (d v : Nat) (i : Fin d) (r : Fin db) :
    (prefixReplicaL A d v).binary i.val (d + 1) r =
        A.L.binary i.val v r ∧
      (prefixReplicaL A d v).binary (d + 1) i.val r =
        A.L.binary v i.val r := by
  constructor
  · simp [prefixReplicaL,
      prefixReplicaAddress_old d v i.val i.isLt,
      prefixReplicaAddress_last]
  · simp [prefixReplicaL,
      prefixReplicaAddress_old d v i.val i.isLt,
      prefixReplicaAddress_last]

/-- The filler vertex carries no L unary, diagonal, or off-diagonal
binary facts: it has the chosen empty singleton type. -/
theorem prefixReplicaL_filler_neutral
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (d v x : Nat) :
    (∀ r : Fin db,
      (prefixReplicaL A d v).binary d x r = false ∧
      (prefixReplicaL A d v).binary x d r = false) ∧
    (∀ r : Fin du,
      (prefixReplicaL A d v).unary d r = false) ∧
    (∀ r : Fin dd,
      (prefixReplicaL A d v).diagonal d r = false) := by
  constructor
  · intro r
    constructor
    · simp [prefixReplicaL, prefixReplicaAddress_filler]
    · simp [prefixReplicaL, prefixReplicaAddress_filler]
  constructor
  · intro r
    simp [prefixReplicaL, prefixReplicaAddress_filler]
  · intro r
    simp [prefixReplicaL, prefixReplicaAddress_filler]

/-- The complete L-type over the shorter socle, with the new type
vertex at d+1, is precisely the original type through d.
This is equality of whole induced L-reducts, not just positive
binary relations involving the type vertex. -/
theorem prefixReplicaL_type_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (d v : Nat) :
    RelationalPrefixType.ofAgeModel (prefixReplicaL A d v) d (d + 1) =
      RelationalPrefixType.ofAgeModel A.L d v := by
  apply RelationalPrefixType.eq_of_atoms
  · intro x y r
    cases x with
    | none =>
      cases y with
      | none =>
          exact (prefixReplicaL_last_singleton A d v).1 r
      | some y =>
          exact (prefixReplicaL_cross A d v y r).2
    | some x =>
      cases y with
      | none =>
          exact (prefixReplicaL_cross A d v x r).1
      | some y =>
          exact (prefixReplicaL_old A d v x y).1 r
  · intro x r
    cases x with
    | none =>
        exact (prefixReplicaL_last_singleton A d v).2.1 r
    | some x =>
        exact (prefixReplicaL_old A d v x x).2.1 r
  · intro x r
    cases x with
    | none =>
        exact (prefixReplicaL_last_singleton A d v).2.2 r
    | some x =>
        exact (prefixReplicaL_old A d v x x).2.2 r

end SuccessorTree.V10

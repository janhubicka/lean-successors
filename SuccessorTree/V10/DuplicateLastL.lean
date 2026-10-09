import SuccessorTree.V10.DuplicateLastE
import SuccessorTree.V10.PrefixReplicaAge
import Mathlib.Tactic

/-!
# Duplicating an ordinary vertex at a later level: exact L-reduct

Given a finite enumerated partial structure A, an old vertex n
and a new last vertex m>n, retain the original induced L-reduct
on vertices below m. The new vertex m has the unary/diagonal
singleton type of n; for old vertices u<n it copies both directed
binary L relations between u and n; for n<=u<m there are NO
binary relations to m in either direction.

This construction duplicates the *earlier predecessor crossing*,
not the entire L-neighbourhood of n. In particular n and m are
not linked, so irreducible forbidden configurations containing
both vertices cannot arise.

The old/new E relation is handled in DuplicateLastE. The
age-preservation and E3 combination follow in a separate module.
-/

namespace SuccessorTree.V10

/-- Decode an old vertex to itself, and the new vertex m to its
original predecessor n. No addresses exist beyond the new end. -/
def duplicateLastAddress (n m x : Nat) : Option Nat :=
  if x < m then some x else if x = m then some n else none

/-- Relations involving the new vertex are permitted only with
the earlier portion below n, or on its own singleton. Old-old
relations are always copied. -/
def duplicateLastRelationGate (n m x y : Nat) : Bool :=
  if x = m then decide (y = m ∨ y < n)
  else if y = m then decide (x < n)
  else true

/-- The exact directed L-reduct of the duplicate extension. -/
def duplicateLastL
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n m : Nat) : AgeTestModel db du dd :=
  { carrier := {x | x < m + 1}
    binary := fun x y r =>
      if duplicateLastRelationGate n m x y then
        match duplicateLastAddress n m x, duplicateLastAddress n m y with
        | some a, some b => A.L.binary a b r
        | _, _ => false
      else false
    unary := fun x r =>
      match duplicateLastAddress n m x with
      | some a => A.L.unary a r
      | none => false
    diagonal := fun x r =>
      match duplicateLastAddress n m x with
      | some a => A.L.diagonal a r
      | none => false }

/-- All old directed binary, unary and diagonal data is copied
inducedly, including every negative relation bit. -/
theorem duplicateLastL_old
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n m u v : Nat) (hu : u < m) (hv : v < m) :
    (∀ r : Fin db,
      (duplicateLastL A n m).binary u v r =
        A.L.binary u v r) ∧
    (∀ r : Fin du,
      (duplicateLastL A n m).unary u r =
        A.L.unary u r) ∧
    (∀ r : Fin dd,
      (duplicateLastL A n m).diagonal u r =
        A.L.diagonal u r) := by
  have hum : u ≠ m := Nat.ne_of_lt hu
  have hvm : v ≠ m := Nat.ne_of_lt hv
  constructor
  · intro r
    simp [duplicateLastL, duplicateLastRelationGate,
      duplicateLastAddress, hu, hv, hum, hvm]
  constructor
  · intro r
    simp [duplicateLastL, duplicateLastAddress, hu]
  · intro r
    simp [duplicateLastL, duplicateLastAddress, hu]

/-- The new vertex has exactly the old original's complete
singleton type, with loops kept separate from unary data. -/
theorem duplicateLastL_newSingleton
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n m : Nat) :
    (∀ r : Fin db,
      (duplicateLastL A n m).binary m m r =
        A.L.binary n n r) ∧
    (∀ r : Fin du,
      (duplicateLastL A n m).unary m r =
        A.L.unary n r) ∧
    (∀ r : Fin dd,
      (duplicateLastL A n m).diagonal m r =
        A.L.diagonal n r) := by
  constructor
  · intro r
    simp [duplicateLastL, duplicateLastRelationGate,
      duplicateLastAddress]
  constructor
  · intro r
    simp [duplicateLastL, duplicateLastAddress]
  · intro r
    simp [duplicateLastL, duplicateLastAddress]

/-- Every lower old vertex u<n gets exactly the original
directed binary pair with n, in both orientations. -/
theorem duplicateLastL_cross_low
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n m u : Nat) (hnm : n < m) (hun : u < n)
    (r : Fin db) :
    (duplicateLastL A n m).binary u m r =
        A.L.binary u n r ∧
      (duplicateLastL A n m).binary m u r =
        A.L.binary n u r := by
  have hum : u < m := hun.trans hnm
  have hune : u ≠ m := Nat.ne_of_lt hum
  have hmnu : m ≠ u := hune.symm
  constructor
  · simp [duplicateLastL, duplicateLastRelationGate,
      duplicateLastAddress, hum, hune, hun]
  · simp [duplicateLastL, duplicateLastRelationGate,
      duplicateLastAddress, hum, hmnu, hun]

/-- There are NO binary links from the duplicate m to any old
vertex in the closed interval [n,m), even if the original
n did have links to those intermediate old vertices. -/
theorem duplicateLastL_cross_blocked
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n m u : Nat) (hnu : n ≤ u) (hum : u < m)
    (r : Fin db) :
    (duplicateLastL A n m).binary u m r = false ∧
      (duplicateLastL A n m).binary m u r = false := by
  have hne : u ≠ m := Nat.ne_of_lt hum
  have hne' : m ≠ u := hne.symm
  have hnot : ¬ u < n := not_lt.mpr hnu
  constructor
  · simp [duplicateLastL, duplicateLastRelationGate,
      duplicateLastAddress, hum, hne, hnot]
  · simp [duplicateLastL, duplicateLastRelationGate,
      duplicateLastAddress, hum, hne', hnot]

/-- In particular the new vertex m is not linked to its
original predecessor n. This prevents a nontrivial irreducible
forbidden copy from containing both. -/
theorem duplicateLastL_original_not_linked
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n m : Nat) (hnm : n < m)
    (r : Fin db) :
    (duplicateLastL A n m).binary n m r = false ∧
      (duplicateLastL A n m).binary m n r = false := by
  exact duplicateLastL_cross_blocked A n m n le_rfl hnm r

end SuccessorTree.V10

import SuccessorTree.V10.EFreeLevel
import SuccessorTree.V10.RelationalTypeReduct

/-!
# Finite enumerated L+ partial structures and extracted partial types

This is a direct Boolean-vector presentation of Definition 6.28 for
a unary/binary relational language. The ordinary vertices are
0,...,size-1, the auxiliary E relation obeys spacing and downward
closure, and a linked pair of ordinary vertices must be in E.

Theorem e_iff_lt_canonicalFreeLevel already derives free levels from
the first two axioms. The new partialTypeAt construction is the
literal structure induced on the initial socle and the distinguished
type vertex, with L-relations renamed and E retained independently.

This file does not yet prove the concrete class of forbidden-free
partial types is an S-tree, or that the H model in Section 6.3 is
an instance of this structure. Those are separate obligations.
-/

namespace SuccessorTree.V10

/-- Definition 6.28, with directed off-diagonal binary bits and
separate unary/diagonal bits for an arbitrary finite relational
language. Nullary symbols are fixed at the class level. -/
structure EnumeratedPartialStructure (db du dd : Nat) where
  size : Nat
  L : AgeTestModel db du dd
  carrier_iff : ∀ v, v ∈ L.carrier ↔ v < size
  E : Nat → Nat → Bool
  E_inside : ∀ u v, E u v = true → u < size ∧ v < size
  spaced : SpacedE E
  downward : DownwardE E
  linked_E : ∀ u v, u < v → u < size → v < size →
    (∃ r : Fin db,
      L.binary u v r = true ∨ L.binary v u r = true) →
    E u v = true

/-- The free level is not stored in the partial structure:
it is determined uniquely from its actual E relation. -/
noncomputable def EnumeratedPartialStructure.freeLevel
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (v : Nat) : Nat :=
  canonicalFreeLevel A.E A.spaced A.downward v

/-- E-incidences are precisely those below the determined free level. -/
theorem EnumeratedPartialStructure.E_iff_freeLevel
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (u v : Nat) :
    A.E u v = true ↔ u < A.freeLevel v :=
  e_iff_lt_canonicalFreeLevel A.E A.spaced A.downward u v

/-- The free level belongs to the original ordinal of the vertex. -/
theorem EnumeratedPartialStructure.freeLevel_le
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (v : Nat) :
    A.freeLevel v ≤ v :=
  canonicalFreeLevel_le A.E A.spaced A.downward v

/-- Extract type^cut_A(v) by renaming v to the distinguished type
vertex. The L-reduct is literally the induced original L-structure;
the independent E component is kept for structural decompositions. -/
def EnumeratedPartialStructure.partialTypeAt
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (cut v : Nat) : PartialTypeWithE cut db du dd :=
  { lReduct := RelationalPrefixType.ofAgeModel A.L cut v
    eRelation := fun x y =>
      A.E (prefixVertexIndex v x) (prefixVertexIndex v y) }

/-- Projection of the extracted full L+ type to its L-reduct recovers
exactly the paper's type over the selected initial socle. -/
@[simp] theorem EnumeratedPartialStructure.partialTypeAt_lReduct
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (cut v : Nat) :
    (A.partialTypeAt cut v).lReduct =
      RelationalPrefixType.ofAgeModel A.L cut v := rfl

/-- The distinguished type vertex is E-linked to EVERY coordinate of
the extracted socle, provided cut ≤ fl_A(v). This is the explicit
E-component of the actual partial type, not a new class axiom. -/
theorem EnumeratedPartialStructure.partialTypeAt_fullESocle
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (cut v : Nat) (hcut : cut ≤ A.freeLevel v)
    (u : Fin cut) :
    (A.partialTypeAt cut v).eRelation (some u) none = true := by
  change A.E u.val v = true
  exact (A.E_iff_freeLevel u.val v).2
    (lt_of_lt_of_le u.isLt hcut)

/-- The distinguished type vertex has no E-edge TO an ordinary socle
vertex; the spacing axiom rules out this reverse orientation. -/
theorem EnumeratedPartialStructure.partialTypeAt_no_reverseE
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (cut v : Nat) (hcut : cut ≤ A.freeLevel v)
    (u : Fin cut) :
    (A.partialTypeAt cut v).eRelation none (some u) = false := by
  change A.E v u.val = false
  have hu : u.val < v := by
    have hfv := A.freeLevel_le v
    omega
  cases h : A.E v u.val with
  | false => rfl
  | true =>
      have bad := A.spaced v u.val h
      omega

/-- There is no E loop at the distinguished type vertex. -/
theorem EnumeratedPartialStructure.partialTypeAt_no_typeE_loop
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (cut v : Nat) :
    (A.partialTypeAt cut v).eRelation none none = false := by
  change A.E v v = false
  cases h : A.E v v with
  | false => rfl
  | true =>
      have bad := A.spaced v v h
      omega

/-- At the first missing E coordinate itself, the original vertex
has no E-edge. This is the exact convention behind type_A(v). -/
theorem EnumeratedPartialStructure.freeLevel_firstMissing
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (v : Nat) :
    A.E (A.freeLevel v) v = false :=
  (canonicalFreeLevel_isFreeCut A.E A.spaced A.downward v).2

end SuccessorTree.V10

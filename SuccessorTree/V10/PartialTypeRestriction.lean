import SuccessorTree.V10.PartialStructureE

/-!
# Literal restrictions of complete partial-type records

The partial-type tree Kpt is ordered by induced restriction to the
initial numbered socle, retaining its distinguished type vertex t.
This module implements this restriction on the complete finite L+
record: all unary, diagonal and ordered binary L atoms, together with
all E pairs.

A restriction of type_A(v) computed at a longer cut is exactly the
type computed at the shorter cut, not merely equal in its relation
patterns to t. This checks the basic predecessor coding needed for
the first-record-difference / meet transfer.

It does not yet instantiate LevelTree on the quotient set of all
forbidden-free partial types. That is a separate representation
obligation in the manuscript, as are the E-socle/free-level
constraints on admissible nodes.
-/

namespace SuccessorTree.V10

/-- Inclusion of the shorter socle together with the same type
vertex into the longer one. -/
def liftTypeCoordinate {small large : Nat} (h : small ≤ large) :
    Option (Fin small) → Option (Fin large)
  | none => none
  | some i => some ⟨i.val, lt_of_lt_of_le i.isLt h⟩

/-- Renaming the type vertex to its original position commutes with
inclusion of the initial socle. -/
@[simp] theorem prefixVertexIndex_lift
    {small large : Nat} (h : small ≤ large) (v : Nat)
    (x : Option (Fin small)) :
    prefixVertexIndex v (liftTypeCoordinate h x) =
      prefixVertexIndex v x := by
  cases x with
  | none => rfl
  | some x => rfl

/-- Full induced restriction of an L-type; the initial socle
continues to carry its internal relations. -/
def RelationalPrefixType.restrict
    {small large db du dd : Nat}
    (T : RelationalPrefixType large db du dd)
    (h : small ≤ large) : RelationalPrefixType small db du dd :=
  { binary := fun a b r =>
      T.binary (liftTypeCoordinate h a) (liftTypeCoordinate h b) r
    unary := fun a r => T.unary (liftTypeCoordinate h a) r
    diagonal := fun a r => T.diagonal (liftTypeCoordinate h a) r }

/-- Equality of every L-atom is equality of the complete L-reduct
record on the socle plus the type vertex. -/
theorem RelationalPrefixType.eq_of_atoms
    {cut db du dd : Nat}
    {T U : RelationalPrefixType cut db du dd}
    (hB : ∀ a b r, T.binary a b r = U.binary a b r)
    (hU : ∀ a r, T.unary a r = U.unary a r)
    (hD : ∀ a r, T.diagonal a r = U.diagonal a r) :
    T = U := by
  cases T with
  | mk tB tU tD =>
    cases U with
    | mk uB uU uD =>
      have hb : tB = uB := by
        funext a b r
        exact hB a b r
      have hu : tU = uU := by
        funext a r
        exact hU a r
      have hd : tD = uD := by
        funext a r
        exact hD a r
      cases hb
      cases hu
      cases hd
      rfl

/-- Exact L-type extraction commutes with shorter initial socles. -/
theorem RelationalPrefixType.ofAgeModel_restrict
    {db du dd : Nat}
    (A : AgeTestModel db du dd)
    (small large v : Nat) (h : small ≤ large) :
    (RelationalPrefixType.ofAgeModel A large v).restrict h =
      RelationalPrefixType.ofAgeModel A small v := by
  apply RelationalPrefixType.eq_of_atoms
  · intro a b r
    cases a <;> cases b <;> rfl
  · intro a r
    cases a <;> rfl
  · intro a r
    cases a <;> rfl

/-- Full induced restriction of an L+ type; the auxiliary E bits are
retained but do not contaminate the L-reduct. -/
def PartialTypeWithE.restrict
    {small large db du dd : Nat}
    (T : PartialTypeWithE large db du dd)
    (h : small ≤ large) : PartialTypeWithE small db du dd :=
  { lReduct := T.lReduct.restrict h
    eRelation := fun a b =>
      T.eRelation (liftTypeCoordinate h a) (liftTypeCoordinate h b) }

/-- Complete equality of two L+ type records follows from the
corresponding L-reduct and all E bits. -/
theorem PartialTypeWithE.eq_of_atoms
    {cut db du dd : Nat}
    {T U : PartialTypeWithE cut db du dd}
    (hL : T.lReduct = U.lReduct)
    (hE : ∀ a b, T.eRelation a b = U.eRelation a b) :
    T = U := by
  cases T with
  | mk tL tE =>
    cases U with
    | mk uL uE =>
      have he : tE = uE := by
        funext a b
        exact hE a b
      cases hL
      cases he
      rfl

/-- The complete L+ type computed at a long socle restricts
exactly to the type computed at the shorter socle. This checks
the E component as well as every L component. -/
theorem EnumeratedPartialStructure.partialTypeAt_restrict
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (small large v : Nat) (h : small ≤ large) :
    (A.partialTypeAt large v).restrict h =
      A.partialTypeAt small v := by
  apply PartialTypeWithE.eq_of_atoms
  · exact RelationalPrefixType.ofAgeModel_restrict A.L
      small large v h
  · intro a b
    cases a <;> cases b <;> rfl

end SuccessorTree.V10

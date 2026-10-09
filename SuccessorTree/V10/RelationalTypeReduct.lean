import SuccessorTree.V10.AmbientSignature

/-!
# The literal finite L-reduct of a type vertex over an initial socle

The manuscript's type of a vertex over cut c is the induced structure on
the first c numbered vertices together with one distinguished type vertex
t. In this file the distinguished vertex is none and socle coordinate i
is some i : Option (Fin c). Both ordered binary orientations and all
unary/diagonal facts are present.

This record contains the FULL induced L-reduct, not merely the cross
relations. In contrast, E is an auxiliary relation in L+, and the
forbidden structures of the signature argument are L-structures. An
L+ partial type can forget E to obtain the following L-reduct; no
equality of E-relations in two different age-test witnesses is required.

We prove that equality of these concrete L-reducts gives exactly the
FullAtomicTypePrefix equality used by the checked signature collision.
The KFpt successor construction still has to prove the separate
prescribed-crossing equality of these L-reducts.
-/

namespace SuccessorTree.V10

/-- Decode a socle coordinate or the distinguished type vertex. -/
def prefixVertexIndex {cut : Nat}
    (upper : Nat) : Option (Fin cut) → Nat
  | none => upper
  | some i => i.val

/-- The entire induced L-reduct over the initial socle together with
a distinguished type vertex. Each directed binary atom is included. -/
structure RelationalPrefixType (cut db du dd : Nat) where
  binary : Option (Fin cut) → Option (Fin cut) → Fin db → Bool
  unary : Option (Fin cut) → Fin du → Bool
  diagonal : Option (Fin cut) → Fin dd → Bool

/-- Explicitly extract the L-type of a vertex in a numbered age-test
structure by renaming that vertex to the distinguished type vertex. -/
def RelationalPrefixType.ofAgeModel {db du dd : Nat}
    (A : AgeTestModel db du dd) (cut upper : Nat) :
    RelationalPrefixType cut db du dd :=
  { binary := fun x y t =>
      A.binary (prefixVertexIndex upper x)
        (prefixVertexIndex upper y) t
    unary := fun x t => A.unary (prefixVertexIndex upper x) t
    diagonal := fun x t => A.diagonal (prefixVertexIndex upper x) t }

/-- The smaller record needed to compare type vertices discards only
their common socle's internal relations; it retains every singleton
fact and every incoming/outgoing cross relation. -/
def RelationalPrefixType.toAtomic {cut db du dd : Nat}
    (T : RelationalPrefixType cut db du dd) :
    FullAtomicTypePrefix cut db du dd :=
  { unary := T.unary none
    diagonal := T.diagonal none
    fromSocle := fun x t => T.binary (some x) none t
    toSocle := fun x t => T.binary none (some x) t }

/-- The actual finite induced L-reduct computes the same complete
cross-type record as the previous signature interfaces. -/
@[simp] theorem RelationalPrefixType.ofAgeModel_toAtomic
    {db du dd : Nat} (A : AgeTestModel db du dd)
    (cut upper : Nat) :
    (RelationalPrefixType.ofAgeModel A cut upper).toAtomic =
      fullAtomicTypePrefix A.binary A.unary A.diagonal
        cut upper := rfl

/-- Literal equality of the paper-style type L-reducts implies the
all-atom equality used in the signature proof. There is no dependence
on E-socle data or a forbidden relation between later upper vertices. -/
theorem equal_reduct_types_imply_fullAtomic
    {db du dd : Nat} (A C : AgeTestModel db du dd)
    (cut upper original : Nat)
    (hType :
      RelationalPrefixType.ofAgeModel A cut upper =
        RelationalPrefixType.ofAgeModel C cut original) :
    fullAtomicTypePrefix A.binary A.unary A.diagonal cut upper =
      fullAtomicTypePrefix C.binary C.unary C.diagonal
        cut original := by
  have h := congrArg
    (fun T : RelationalPrefixType cut db du dd => T.toAtomic) hType
  simpa only [RelationalPrefixType.ofAgeModel_toAtomic] using h

/-- Two explicit pieces of the paper's one-level prescription:
an upper witness realizes its chosen crossing, and that crossing is
the initial L-type of the named ambient original. This already gives
the exact atomic equality needed by the collision argument. -/
theorem prescribed_crossing_implies_fullAtomic
    {db du dd : Nat} (A C : AgeTestModel db du dd)
    (cut upper original : Nat)
    (crossing : RelationalPrefixType cut db du dd)
    (hWitness :
      RelationalPrefixType.ofAgeModel A cut upper = crossing)
    (hAmbient :
      crossing = RelationalPrefixType.ofAgeModel C cut original) :
    fullAtomicTypePrefix A.binary A.unary A.diagonal cut upper =
      fullAtomicTypePrefix C.binary C.unary C.diagonal
        cut original :=
  equal_reduct_types_imply_fullAtomic A C cut upper original
    (hWitness.trans hAmbient)

/-- Auxiliary E-socle information belongs to L+ rather than to the
age-test L-reduct. It may be forgotten without changing any L-atom. -/
structure PartialTypeWithE (cut db du dd : Nat) where
  lReduct : RelationalPrefixType cut db du dd
  eRelation : Option (Fin cut) → Option (Fin cut) → Bool

/-- Equality of complete L+ type records implies equality of their
L-reducts; conversely no equality of E is needed for age obstructions. -/
theorem PartialTypeWithE.eq_implies_lReduct
    {cut db du dd : Nat}
    {T U : PartialTypeWithE cut db du dd} (h : T = U) :
    T.lReduct = U.lReduct := congrArg PartialTypeWithE.lReduct h

end SuccessorTree.V10

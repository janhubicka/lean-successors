import SuccessorTree.V10.PartialStructureE
import Mathlib.Tactic

/-!
# Canonical finite partial codes: the countable vertices of G+

Definition 6.40 of successor v10 uses all finite enumerated L+
partial structures of forbidden-free L-age as vertices of G+.

A raw EnumeratedPartialStructure in the Lean API contains
functions on all Nat, although only its finite carrier matters.
Two such records can differ outside the carrier while
representing the SAME finite partial structure. Therefore
G+ must be coded by the finite on-carrier data, rather than
by equality of the unrestricted raw Lean records.

The canonical code below records the size and all directed
binary, unary, diagonal, and E bits on Fin size. These are
the only atoms relevant to the original structure. Its
finite-data type is countable. The subset of codes coming
from actual forbidden-free finite partial structures is
also countable and has explicit constructors.

The induced G+ relations and the H+→G+ transfer will be
defined using these codes. No quotient by partial types or
new axiom about E is introduced.
-/

namespace SuccessorTree.V10

/-- The entire finite L+ atomic table, with no off-carrier
coordinates. Off-diagonal directed binary and diagonal binary
atoms remain distinct fields of the existing normalized model. -/
structure FinitePartialCode (db du dd : Nat) where
  size : Nat
  binary : Fin size → Fin size → Fin db → Bool
  unary : Fin size → Fin du → Bool
  diagonal : Fin size → Fin dd → Bool
  eRelation : Fin size → Fin size → Bool

/-- The tuple type of all finite atomic tables at one length. -/
abbrev FinitePartialTables (db du dd n : Nat) :=
  (Fin n → Fin n → Fin db → Bool) ×
  (Fin n → Fin du → Bool) ×
  (Fin n → Fin dd → Bool) ×
  (Fin n → Fin n → Bool)

/-- Forget only off-carrier values of the raw finite
partial-structure representation. Its E and full induced L
table are evaluated on the finite vertex coordinates. -/
def FinitePartialCode.ofEnumerated
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd) :
    FinitePartialCode db du dd where
  size := A.size
  binary := fun i j a => A.L.binary i.val j.val a
  unary := fun i a => A.L.unary i.val a
  diagonal := fun i a => A.L.diagonal i.val a
  eRelation := fun i j => A.E i.val j.val

@[simp] theorem FinitePartialCode.ofEnumerated_size
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd) :
    (FinitePartialCode.ofEnumerated A).size = A.size := rfl

@[simp] theorem FinitePartialCode.ofEnumerated_binary
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (i j : Fin A.size) (a : Fin db) :
    (FinitePartialCode.ofEnumerated A).binary i j a =
      A.L.binary i.val j.val a := rfl

@[simp] theorem FinitePartialCode.ofEnumerated_unary
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (i : Fin A.size) (a : Fin du) :
    (FinitePartialCode.ofEnumerated A).unary i a =
      A.L.unary i.val a := rfl

@[simp] theorem FinitePartialCode.ofEnumerated_diagonal
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (i : Fin A.size) (a : Fin dd) :
    (FinitePartialCode.ofEnumerated A).diagonal i a =
      A.L.diagonal i.val a := rfl

@[simp] theorem FinitePartialCode.ofEnumerated_E
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (i j : Fin A.size) :
    (FinitePartialCode.ofEnumerated A).eRelation i j =
      A.E i.val j.val := rfl

/-- Finite atomic tables are a COUNTABLE type. This is not
true of the unrestricted raw records with arbitrary values
outside their carrier. -/
instance finitePartialCodeCountable (db du dd : Nat) :
    Countable (FinitePartialCode db du dd) := by
  classical
  let e : FinitePartialCode db du dd →
      (Σ n : Nat, FinitePartialTables db du dd n) :=
    fun C => ⟨C.size,(C.binary,C.unary,C.diagonal,C.eRelation)⟩
  have hCountable :
      Countable (Σ n : Nat, FinitePartialTables db du dd n) := by
    infer_instance
  letI := hCountable
  have hInjective : Function.Injective e := by
    intro A B hAB
    cases A with
    | mk n aB aU aD aE =>
      cases B with
      | mk m bB bU bD bE =>
        cases hAB
        rfl
  exact Function.Injective.countable hInjective

/-- The canonical vertex type of Definition 6.40.
Existence of a finite forbidden-free witness is a mere
property of the finite code, not extra potentially
uncountable structure stored in the vertex. -/
def FiniteGPlusVertex
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :=
  {C : FinitePartialCode db du dd //
    ∃ A : EnumeratedPartialStructure db du dd,
      C = FinitePartialCode.ofEnumerated A ∧
      0 < A.size ∧
      ∀ bad, bad ∈ family → bad.Avoids A.L}

/-- Despite the existence property referring to raw finite
structures, the vertex TYPE remains countable because the
witness is not part of its data. -/
instance finiteGPlusVertexCountable
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    Countable (FiniteGPlusVertex family) := by
  unfold FiniteGPlusVertex
  infer_instance

/-- Produce the genuine G+ vertex of a finite partial
structure with positive carrier and forbidden-free L-age. -/
noncomputable def finiteGPlusVertexOfEnumerated
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hPositive : 0 < A.size)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    FiniteGPlusVertex family :=
  ⟨FinitePartialCode.ofEnumerated A,
    ⟨A,rfl,hPositive,hAvoid⟩⟩

/-- The index of a G+ vertex is exactly the size of the
finite original it represents. -/
@[simp] theorem finiteGPlusVertexOfEnumerated_size
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hPositive : 0 < A.size)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    (finiteGPlusVertexOfEnumerated family A hPositive hAvoid).val.size =
      A.size := rfl

end SuccessorTree.V10
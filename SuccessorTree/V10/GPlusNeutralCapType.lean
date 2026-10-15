import SuccessorTree.V10.GPlusShapeImageInjective
import Mathlib.Tactic

/-!
# Observation 6.42: the canonical neutral cap's COMPLETE type

A finite admissible G+ code C has a completely determined
canonical neutral capped partial type: its ordinary part has all
four source finite atomic tables; the new distinguished type
vertex has no L atoms at all, has incoming E from every ordinary
coordinate, and has no outgoing or diagonal E atoms.

This file proves that the genuine NonedgePadding.socleCapNode
construction has exactly this record, rather than just the
ordinary code already checked. The model is compatible with
initial-segment restriction, which is the reusable input to
prefix preservation of the induced G+ ShapeMap action.

No new forbidden-age, E-expansion, higher arity or ShapeMap axiom
is introduced: every atom is compared with the actual two-neutral
padding and actual prefixReplicaE already validated.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- Full neutral terminal type over an existing finite L+ code,
including the negative L atoms and the fixed incoming E-column. -/
def FinitePartialCode.neutralCapType (C : FinitePartialCode db du dd) :
    PartialTypeWithE C.size db du dd where
  lReduct := {
    binary := fun x y t =>
      match x, y with
      | some i, some j => C.binary i j t
      | _, _ => false
    unary := fun x t =>
      match x with
      | some i => C.unary i t
      | none => false
    diagonal := fun x t =>
      match x with
      | some i => C.diagonal i t
      | none => false }
  eRelation := fun x y =>
    match x, y with
    | some i, some j => C.eRelation i j
    | some _, none => true
    | _, _ => false

/-- The neutral terminal type commutes with finite code
restriction on ALL ordinary, distinguished-vertex and E atoms. -/
theorem FinitePartialCode.neutralCapType_restrict
    (C : FinitePartialCode db du dd)
    (n : Nat) (hn : n ≤ C.size) :
    (C.neutralCapType).restrict hn =
      (C.restrict n hn).neutralCapType := by
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y t
      cases x <;> cases y <;> rfl
    · intro x t
      cases x <;> rfl
    · intro x t
      cases x <;> rfl
  · intro x y
    cases x <;> cases y <;> rfl

/-- At the last neutral vertex of the genuine cap the unary and
diagonal L tables, including all possible positive singleton
atoms, are the canonical false records. -/
theorem NonedgePadding.socleCap_neutral_unary
    (A : EnumeratedPartialStructure db du dd) (t : Fin du) :
    (NonedgePadding.socleCap A).L.unary (A.size+1) t = false := by
  have hNot : ¬ NonedgePadding.Real (A.size+1) (A.size+1) := by
    simp [NonedgePadding.Real]
  simp [NonedgePadding.socleCap, NonedgePadding.twoNeutralL,
    NonedgePadding.model, hNot]

theorem NonedgePadding.socleCap_neutral_diagonal
    (A : EnumeratedPartialStructure db du dd) (t : Fin dd) :
    (NonedgePadding.socleCap A).L.diagonal (A.size+1) t = false := by
  have hNot : ¬ NonedgePadding.Real (A.size+1) (A.size+1) := by
    simp [NonedgePadding.Real]
  simp [NonedgePadding.socleCap, NonedgePadding.twoNeutralL,
    NonedgePadding.model, hNot]

/-- The actual two-neutral cap produces EXACTLY the finite-code
neutral terminal L+ record, including all four complete tables. -/
theorem NonedgePadding.socleCapNode_neutralCapType
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    (NonedgePadding.socleCapNode family A hAvoid).1.2 =
      (FinitePartialCode.ofEnumerated A).neutralCapType := by
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y t
      cases x with
      | none =>
          cases y with
          | none =>
              change (NonedgePadding.twoNeutralL A).binary
                (A.size+1) (A.size+1) t = false
              exact NonedgePadding.twoNeutralL_binary_new A
                (A.size+1) (A.size+1) (by omega) (by omega)
                (Or.inl (by omega)) t
          | some j =>
              change (NonedgePadding.twoNeutralL A).binary
                (A.size+1) j.val t = false
              have hj := j.isLt
              change j.val < A.size at hj
              exact NonedgePadding.twoNeutralL_binary_new A
                (A.size+1) j.val (by omega) (by omega)
                (Or.inl (by omega)) t
      | some i =>
          cases y with
          | none =>
              change (NonedgePadding.twoNeutralL A).binary
                i.val (A.size+1) t = false
              have hi := i.isLt
              change i.val < A.size at hi
              exact NonedgePadding.twoNeutralL_binary_new A
                i.val (A.size+1) (by omega) (by omega)
                (Or.inr (by omega)) t
          | some j =>
              change (NonedgePadding.twoNeutralL A).binary
                i.val j.val t = A.L.binary i.val j.val t
              exact NonedgePadding.twoNeutralL_old_binary A
                i.val j.val i.isLt j.isLt t
    · intro x t
      cases x with
      | none =>
          change (NonedgePadding.socleCap A).L.unary (A.size+1) t = false
          exact NonedgePadding.socleCap_neutral_unary A t
      | some i =>
          change (NonedgePadding.twoNeutralL A).unary i.val t =
            A.L.unary i.val t
          exact NonedgePadding.twoNeutralL_old_unary A i.val i.isLt t
    · intro x t
      cases x with
      | none =>
          change (NonedgePadding.socleCap A).L.diagonal (A.size+1) t = false
          exact NonedgePadding.socleCap_neutral_diagonal A t
      | some i =>
          change (NonedgePadding.twoNeutralL A).diagonal i.val t =
            A.L.diagonal i.val t
          exact NonedgePadding.twoNeutralL_old_diagonal A i.val i.isLt t
  · intro x y
    cases x with
    | none =>
        cases y with
        | none =>
            change (NonedgePadding.socleCap A).E
              (A.size+1) (A.size+1) = false
            simp [NonedgePadding.socleCap, prefixReplicaE]
        | some j =>
            change (NonedgePadding.socleCap A).E
              (A.size+1) j.val = false
            have hOld := NonedgePadding.socleCap_old_E A
              (A.size+1) j.val j.isLt
            have hFalse : A.E (A.size+1) j.val = false := by
              cases he : A.E (A.size+1) j.val with
              | false => rfl
              | true =>
                  have hIn := A.E_inside _ _ he
                  omega
            exact hOld.trans hFalse
    | some i =>
        cases y with
        | none =>
            change (NonedgePadding.socleCap A).E
              i.val (A.size+1) = true
            exact (prefixReplicaE_last_iff A A.size i.val).2 i.isLt
        | some j =>
            change (NonedgePadding.socleCap A).E i.val j.val =
              A.E i.val j.val
            exact NonedgePadding.socleCap_old_E A i.val j.val j.isLt

/-- The canonical cap of an arbitrary genuine finite G+ vertex is
fully neutral, independently of which finite witness was chosen. -/
theorem FiniteGPlusVertex.canonicalCap_neutralCapType
    (A : FiniteGPlusVertex family) :
    A.canonicalCap.1.2 =
      (FinitePartialCode.ofEnumerated A.chosenStructure).neutralCapType := by
  change (NonedgePadding.socleCapNode family A.chosenStructure
    (A.chosenStructure_spec).2.2).1.2 =
      (FinitePartialCode.ofEnumerated A.chosenStructure).neutralCapType
  exact NonedgePadding.socleCapNode_neutralCapType
    A.chosenStructure (A.chosenStructure_spec).2.2

end SuccessorTree.V10

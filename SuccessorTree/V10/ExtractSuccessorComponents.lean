import SuccessorTree.V10.CompleteNextColumn
import SuccessorTree.V10.CanonicalCrossing
import SuccessorTree.V10.PartialTypeRestriction
import Mathlib.Tactic

/-!
# Exact predecessor, parameter and Sigma-letter extraction from one cover

Definition 6.30 recovers a cover Q at level ell+1 from its predecessor,
the empty-or-singleton parameter describing the last ordinary vertex
ell over its E-socle, and the letter describing ell and the
distinguished type vertex t.

This module defines the three components on complete L+ records,
with no information discarded and no additional axioms:
* restriction through ell is the predecessor;
* extraction of the last ordinary vertex with its initial free
  socle of length f is the singleton parameter when f>0;
* restriction to the pair {ell,t}, with ell renamed 0, is the
  terminal Sigma-letter.

For a genuine type Q=type_A(v) through ell+1, the extracted
parameter equals the actual induced type_A(ell) through f.
The letter's E-link to t is necessarily present. The complete
forward construction, admissibility of arbitrary displayed letters,
and uniqueness of the resulting full column from (parameter,letter)
are still separate proof obligations for S2 and S3.
-/

namespace SuccessorTree.V10

/-- Coordinates in a shortened type of the last ordinary vertex.
The new type vertex represents ell, while old coordinates remain
the original numbered socle vertices. -/
def lastOrdinaryCoordinate (ell f : Nat) (hf : f ≤ ell) :
    Option (Fin f) → Option (Fin (ell + 1))
  | none => some (Fin.last ell)
  | some i =>
      some ⟨i.val, Nat.lt_succ_of_le
        (le_trans (Nat.le_of_lt i.isLt) hf)⟩

/-- The exact singleton-parameter candidate supplied by a new
ordinary vertex, before imposing the positive-free-level rule. -/
def PartialTypeWithE.lastOrdinaryParameter
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (f : Nat) (hf : f ≤ ell) :
    PartialTypeWithE f db du dd :=
  { lReduct :=
      { binary := fun a b r =>
          Q.lReduct.binary
            (lastOrdinaryCoordinate ell f hf a)
            (lastOrdinaryCoordinate ell f hf b) r
        unary := fun a r =>
          Q.lReduct.unary (lastOrdinaryCoordinate ell f hf a) r
        diagonal := fun a r =>
          Q.lReduct.diagonal (lastOrdinaryCoordinate ell f hf a) r }
    eRelation := fun a b =>
      Q.eRelation
        (lastOrdinaryCoordinate ell f hf a)
        (lastOrdinaryCoordinate ell f hf b) }

/-- The level-one Sigma letter describing the newly introduced
ordinary vertex ell and the distinguished type vertex t. -/
def terminalCoordinate (ell : Nat) :
    Option (Fin 1) → Option (Fin (ell + 1))
  | none => none
  | some _ => some (Fin.last ell)

def PartialTypeWithE.terminalLetter
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd) :
    PartialTypeWithE 1 db du dd :=
  { lReduct :=
      { binary := fun a b r =>
          Q.lReduct.binary
            (terminalCoordinate ell a) (terminalCoordinate ell b) r
        unary := fun a r =>
          Q.lReduct.unary (terminalCoordinate ell a) r
        diagonal := fun a r =>
          Q.lReduct.diagonal (terminalCoordinate ell a) r }
    eRelation := fun a b =>
      Q.eRelation (terminalCoordinate ell a)
        (terminalCoordinate ell b) }

/-- Extraction of a long genuine type and then of its last ordinary
vertex recovers exactly the original ordinary vertex's shorter type.
This includes every L and E atom, not merely the positive tuples. -/
theorem partialTypeAt_lastOrdinaryParameter
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v ell f : Nat) (hf : f ≤ ell) :
    (A.partialTypeAt (ell + 1) v).lastOrdinaryParameter f hf =
      A.partialTypeAt f ell := by
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      cases a <;> cases b <;> rfl
    · intro a r
      cases a <;> rfl
    · intro a r
      cases a <;> rfl
  · intro a b
    cases a <;> cases b <;> rfl

/-- The old complete predecessor of a genuine successor is exactly
the shorter induced partial type. -/
theorem partialTypeAt_predecessor
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v ell : Nat) :
    (A.partialTypeAt (ell + 1) v).restrict (Nat.le_succ ell) =
      A.partialTypeAt ell v :=
  A.partialTypeAt_restrict ell (ell + 1) v (Nat.le_succ ell)

/-- The terminal Sigma-letter of a genuine type contains the required
auxiliary E relation from the newly introduced ordinary vertex
to the distinguished type vertex. -/
theorem terminalLetter_has_E
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v ell : Nat) (h : ell + 1 ≤ A.freeLevel v) :
    ((A.partialTypeAt (ell + 1) v).terminalLetter).eRelation
      (some 0) none = true := by
  change A.E ell v = true
  exact (A.E_iff_freeLevel ell v).2 (by omega)

/-- A positive free level of the newly introduced ordinary vertex
is strictly below ell, and its extracted parameter equals its
actual canonical partial type. This is the S1/S3 decomposition
input, not the whole S-tree operation. -/
theorem extracted_nonempty_parameter_is_canonical
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v ell : Nat) (h : ell + 1 ≤ A.freeLevel v)
    (hPos : 0 < A.freeLevel ell) :
    ∃ hf : A.freeLevel ell ≤ ell,
      (A.partialTypeAt (ell + 1) v).lastOrdinaryParameter
          (A.freeLevel ell) hf =
        A.partialTypeAt (A.freeLevel ell) ell ∧
      A.freeLevel ell < ell := by
  refine ⟨A.freeLevel_le ell, ?_, ?_⟩
  · exact partialTypeAt_lastOrdinaryParameter A v ell
      (A.freeLevel ell) (A.freeLevel_le ell)
  · exact freeLevel_pos_lt_vertex A ell hPos

end SuccessorTree.V10

import SuccessorTree.V10.LocalAgeNeutral
import Mathlib.Tactic

/-!
# Transport complete old L+ atoms through a neutral insertion

For the global map in Lemma 6.51, insertion must be determined by a finite
partial type, not by a choice of ambient witness. The first necessary fact is
that every old L+ atom in type_A(v) is preserved after shifting coordinates
past the new level and replacing A by the forbidden-free neutral insertion.

The statements below retain all four components: both directed binary L
tables, the unary/diagonal singleton tables and the auxiliary E table.
They compare the full type vertex as well as every old socle vertex.

This is only the OLD-coordinate part of the intended uniform insertion
record. The new coordinate's atoms and the common-socle prescribed branch
are deliberately separate proof obligations.
-/

namespace SuccessorTree.V10

/-- Lift a socle vertex across the inserted address, leaving the distinguished
type vertex unchanged. It works for every cut, including cuts below ell. -/
def insertedTypeCoordinate
    {cut : Nat} (ell : Nat) :
    Option (Fin cut) → Option (Fin (cut + 1))
  | none => none
  | some i =>
      some ⟨insertAddress ell i.val, by
        unfold insertAddress
        split_ifs <;> omega⟩

/-- The two ways of locating an old type-coordinate after insertion coincide
literally, including the distinguished type vertex. -/
@[simp] theorem prefixVertexIndex_insertedTypeCoordinate
    {cut : Nat} (ell v : Nat) (a : Option (Fin cut)) :
    prefixVertexIndex (insertAddress ell v)
        (insertedTypeCoordinate ell a) =
      insertAddress ell (prefixVertexIndex v a) := by
  cases a with
  | none => rfl
  | some a => rfl

/-- Every original coordinate in a genuine extracted type lies in the
original finite carrier. -/
theorem prefixVertexIndex_inside
    {cut : Nat} (v : Nat) (size : Nat)
    (hv : v < size) (hcut : cut ≤ size)
    (a : Option (Fin cut)) :
    prefixVertexIndex v a < size := by
  cases a with
  | none => exact hv
  | some a => exact lt_of_lt_of_le a.isLt hcut

/-- The exact inserted E relation on two old finite vertices is identical
to the old relation. This includes false E bits, and uses the transported
initial-segment cuts rather than an arbitrary E extension. -/
theorem neutralInsert_old_E_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (x y : Nat) (hx : x < A.size) (hy : y < A.size) :
    (neutralInsert A ell hell hellPos).E
        (insertAddress ell x) (insertAddress ell y) =
      A.E x y := by
  have hyNew : insertAddress ell y < A.size + 1 := by
    by_cases hyell : y < ell
    · rw [insertAddress_below ell y hyell]
      omega
    · rw [insertAddress_above ell y (by omega)]
      omega
  have hIff :
      insertE A ell 0 (insertAddress ell x) (insertAddress ell y) = true ↔
        A.E x y = true := by
    constructor
    · intro h
      have hlt := (insertE_true_iff A ell 0 _ _).1 h
      exact (A.E_iff_freeLevel x y).2
        ((insertAddress_lt_insertedCut_iff A ell 0 x y).1 hlt.2)
    · intro h
      exact (insertE_true_iff A ell 0 _ _).2
        ⟨hyNew, (insertAddress_lt_insertedCut_iff A ell 0 x y).2
          ((A.E_iff_freeLevel x y).1 h)⟩
  change insertE A ell 0 (insertAddress ell x) (insertAddress ell y) =
    A.E x y
  cases hNew : insertE A ell 0 (insertAddress ell x) (insertAddress ell y) with
  | true =>
      exact (hIff.mp hNew).symm
  | false =>
      have hOld : A.E x y = false := by
        cases ho : A.E x y with
        | false => rfl
        | true =>
            have hcontra := hIff.mpr ho
            rw [hNew] at hcontra
            cases hcontra
      exact hOld.symm

/-- The full induced type of a shifted old vertex agrees with its source
on EVERY pair of old coordinates, including incoming and outgoing binary
L bits, unary facts, diagonal facts and all auxiliary E bits. This is the
record identity needed before constructing the one-coordinate map. -/
theorem neutralInsert_partialType_old_atoms
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (cut v : Nat) (hcut : cut ≤ A.size) (hv : v < A.size) :
    let B := neutralInsert A ell hell hellPos
    (∀ (a b : Option (Fin cut)) (t : Fin db),
      (B.partialTypeAt (cut + 1) (insertAddress ell v)).lReduct.binary
        (insertedTypeCoordinate ell a) (insertedTypeCoordinate ell b) t =
      (A.partialTypeAt cut v).lReduct.binary a b t) ∧
    (∀ (a : Option (Fin cut)) (t : Fin du),
      (B.partialTypeAt (cut + 1) (insertAddress ell v)).lReduct.unary
        (insertedTypeCoordinate ell a) t =
      (A.partialTypeAt cut v).lReduct.unary a t) ∧
    (∀ (a : Option (Fin cut)) (t : Fin dd),
      (B.partialTypeAt (cut + 1) (insertAddress ell v)).lReduct.diagonal
        (insertedTypeCoordinate ell a) t =
      (A.partialTypeAt cut v).lReduct.diagonal a t) ∧
    (∀ a b : Option (Fin cut),
      (B.partialTypeAt (cut + 1) (insertAddress ell v)).eRelation
        (insertedTypeCoordinate ell a) (insertedTypeCoordinate ell b) =
      (A.partialTypeAt cut v).eRelation a b) := by
  let B := neutralInsert A ell hell hellPos
  -- The proof below only inspects the old coordinates of B's actual records.
  have hIns : IsLInsertion A (neutralInsert A ell hell hellPos) ell :=
    neutralInsert_isLInsertion A ell hell hellPos
  have hIn : ∀ a : Option (Fin cut),
      prefixVertexIndex v a < A.size :=
    fun a => prefixVertexIndex_inside v A.size hv hcut a
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b t
    change (neutralInsert A ell hell hellPos).L.binary
        (prefixVertexIndex (insertAddress ell v) (insertedTypeCoordinate ell a))
        (prefixVertexIndex (insertAddress ell v) (insertedTypeCoordinate ell b)) t =
      A.L.binary (prefixVertexIndex v a) (prefixVertexIndex v b) t
    rw [prefixVertexIndex_insertedTypeCoordinate,
      prefixVertexIndex_insertedTypeCoordinate]
    exact hIns.binary _ _ (hIn a) (hIn b) t
  · intro a t
    change (neutralInsert A ell hell hellPos).L.unary
        (prefixVertexIndex (insertAddress ell v) (insertedTypeCoordinate ell a)) t =
      A.L.unary (prefixVertexIndex v a) t
    rw [prefixVertexIndex_insertedTypeCoordinate]
    exact hIns.unary _ (hIn a) t
  · intro a t
    change (neutralInsert A ell hell hellPos).L.diagonal
        (prefixVertexIndex (insertAddress ell v) (insertedTypeCoordinate ell a)) t =
      A.L.diagonal (prefixVertexIndex v a) t
    rw [prefixVertexIndex_insertedTypeCoordinate]
    exact hIns.diagonal _ (hIn a) t
  · intro a b
    change (neutralInsert A ell hell hellPos).E
        (prefixVertexIndex (insertAddress ell v) (insertedTypeCoordinate ell a))
        (prefixVertexIndex (insertAddress ell v) (insertedTypeCoordinate ell b)) =
      A.E (prefixVertexIndex v a) (prefixVertexIndex v b)
    rw [prefixVertexIndex_insertedTypeCoordinate,
      prefixVertexIndex_insertedTypeCoordinate]
    exact neutralInsert_old_E_eq A ell hell hellPos
      _ _ (hIn a) (hIn b)

end SuccessorTree.V10

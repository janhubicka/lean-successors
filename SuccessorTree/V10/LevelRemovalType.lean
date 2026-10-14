import SuccessorTree.V10.LevelRemovalFreeCut
import Mathlib.Tactic

/-!
# Complete L+ type transport across a guarded coordinate deletion

The existing LevelRemovalPartial / LevelRemovalFreeCut proof supplies the
genuine shortened partial structure and its canonical E cut. This file
checks that extracting a type after deletion equals deleting that ordinary
coordinate from the *complete* old type. Every positive/absent directed
binary atom, unary fact, diagonal fact and E pair is retained.

The type vertex itself is not deleted: its new enumeration address v is
represented by old address deleteAt m v. This is the precise finite
ingredient needed before proving Lemma 6.34 uniformly for a ShapeMap;
it does NOT assume or conclude the global M2 factorization.
-/

namespace SuccessorTree.V10

/-- Map the shortened initial socle into the original one, omitting m.
The original initial socle is cut and m<cut. -/
def deletedSocleCoordinate (m cut : Nat) (hm : m < cut)
    (i : Fin (cut - 1)) : Fin cut :=
  ⟨deleteAt m i.val, by
    have hi : i.val < cut - 1 := i.isLt
    by_cases him : i.val < m
    · rw [deleteAt_below m i.val him]
      omega
    · rw [deleteAt_above m i.val (by omega)]
      omega⟩

/-- Include both ordinary vertices and the distinguished type vertex. -/
def deleteTypeCoordinate (m cut : Nat) (hm : m < cut) :
    Option (Fin (cut - 1)) → Option (Fin cut)
  | none => none
  | some i => some (deletedSocleCoordinate m cut hm i)

/-- Renaming the distinguished vertex commutes with the ordinary
address-deletion map. -/
@[simp] theorem prefixVertexIndex_deleteTypeCoordinate
    (m cut v : Nat) (hm : m < cut)
    (x : Option (Fin (cut - 1))) :
    prefixVertexIndex (deleteAt m v) (deleteTypeCoordinate m cut hm x) =
      deleteAt m (prefixVertexIndex v x) := by
  cases x with
  | none => rfl
  | some i => rfl

/-- Delete one ordinary socle coordinate, but keep the distinguished
type vertex. No E values are assumed from the L-reduct. -/
def PartialTypeWithE.deleteOrdinary
    {cut db du dd : Nat}
    (T : PartialTypeWithE cut db du dd)
    (m : Nat) (hm : m < cut) :
    PartialTypeWithE (cut - 1) db du dd :=
  { lReduct :=
      { binary := fun a b r =>
          T.lReduct.binary
            (deleteTypeCoordinate m cut hm a)
            (deleteTypeCoordinate m cut hm b) r
        unary := fun a r =>
          T.lReduct.unary (deleteTypeCoordinate m cut hm a) r
        diagonal := fun a r =>
          T.lReduct.diagonal (deleteTypeCoordinate m cut hm a) r }
    eRelation := fun a b =>
      T.eRelation
        (deleteTypeCoordinate m cut hm a)
        (deleteTypeCoordinate m cut hm b) }

/-- The complete type of a retained vertex in the guarded, deleted
finite partial structure is exactly the old L+ type with coordinate
m removed. This includes the E-component and both binary orientations,
not only the induced L-reduct or terminal letter. -/
theorem deleteAtPartial_partialTypeAt_eq_deleteOrdinary
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (m cut v : Nat)
    (hnext : m + 1 < A.size)
    (hfree : A.freeLevel (m + 1) < m)
    (hm : m < cut) :
    (deleteAtPartial A m hnext hfree).partialTypeAt (cut - 1) v =
      (A.partialTypeAt cut (deleteAt m v)).deleteOrdinary m hm := by
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

end SuccessorTree.V10

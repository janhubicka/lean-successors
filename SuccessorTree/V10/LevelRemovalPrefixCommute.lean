import SuccessorTree.V10.LevelRemovalType
import Mathlib.Tactic

/-!
# Ordinary-coordinate deletion commutes with complete L+ prefix restriction

For m<small<=large, the result of deleting m from a longer complete
L+ record and then restricting the shortened socle equals first
restricting the original complete record and then deleting m.
The calculation covers every positive and absent directed binary bit,
all unary/diagonal data and the auxiliary E relation.

This is the local prefix-transport identity needed for the predecessor
clause in Lemma 6.34. It assumes neither admissibility of a particular
source record nor a global level-removal map or M2 factorization.
-/

namespace SuccessorTree.V10

/-- Inclusion of shortened socles followed by skipping m is literally
the same coordinate map as skipping m before ordinary inclusion.
The distinguished type vertex remains fixed in both composites. -/
theorem deleteTypeCoordinate_lift
    (m small large : Nat) (h : small ≤ large) (hm : m < small)
    (x : Option (Fin (small - 1))) :
    deleteTypeCoordinate m large (lt_of_lt_of_le hm h)
        (liftTypeCoordinate (Nat.sub_le_sub_right h 1) x) =
      liftTypeCoordinate h
        (deleteTypeCoordinate m small hm x) := by
  cases x with
  | none => rfl
  | some x =>
      apply congrArg some
      apply Fin.ext
      rfl

/-- Exact naturality of the complete L+ deletion construction under
initial-socle restrictions. No weak/incomplete relational reducts
are used and nothing is assumed about absence of forbidden age. -/
theorem PartialTypeWithE.deleteOrdinary_restrict
    {small large db du dd : Nat}
    (T : PartialTypeWithE large db du dd)
    (h : small ≤ large) (m : Nat) (hm : m < small) :
    (T.deleteOrdinary m (lt_of_lt_of_le hm h)).restrict
        (Nat.sub_le_sub_right h 1) =
      (T.restrict h).deleteOrdinary m hm := by
  let hs : small - 1 ≤ large - 1 := Nat.sub_le_sub_right h 1
  let hl : m < large := lt_of_lt_of_le hm h
  have hCoord (x : Option (Fin (small - 1))) :
      deleteTypeCoordinate m large hl
          (liftTypeCoordinate hs x) =
        liftTypeCoordinate h (deleteTypeCoordinate m small hm x) :=
    deleteTypeCoordinate_lift m small large h hm x
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      change T.lReduct.binary
          (deleteTypeCoordinate m large hl (liftTypeCoordinate hs a))
          (deleteTypeCoordinate m large hl (liftTypeCoordinate hs b)) r =
        T.lReduct.binary
          (liftTypeCoordinate h (deleteTypeCoordinate m small hm a))
          (liftTypeCoordinate h (deleteTypeCoordinate m small hm b)) r
      rw [hCoord a, hCoord b]
    · intro a r
      change T.lReduct.unary
          (deleteTypeCoordinate m large hl (liftTypeCoordinate hs a)) r =
        T.lReduct.unary
          (liftTypeCoordinate h (deleteTypeCoordinate m small hm a)) r
      rw [hCoord a]
    · intro a r
      change T.lReduct.diagonal
          (deleteTypeCoordinate m large hl (liftTypeCoordinate hs a)) r =
        T.lReduct.diagonal
          (liftTypeCoordinate h (deleteTypeCoordinate m small hm a)) r
      rw [hCoord a]
  · intro a b
    change T.eRelation
        (deleteTypeCoordinate m large hl (liftTypeCoordinate hs a))
        (deleteTypeCoordinate m large hl (liftTypeCoordinate hs b)) =
      T.eRelation
        (liftTypeCoordinate h (deleteTypeCoordinate m small hm a))
        (liftTypeCoordinate h (deleteTypeCoordinate m small hm b))
    rw [hCoord a, hCoord b]

end SuccessorTree.V10

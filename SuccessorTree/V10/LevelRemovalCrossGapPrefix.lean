import SuccessorTree.V10.LevelRemovalRawPrefix
import Mathlib.Tactic

/-!
# Complete prefixes below the deleted coordinate remain unchanged

The upper branch of a uniform M2 deletion map removes ordinary
coordinate m from target levels above m. Below the gap, no source
levels are deleted. Hence a complete lower Kpt type whose cut
does not exceed m must remain a prefix of the deleted upper type.

This is the complementary case to LevelRemovalRawPrefix, which
handled two cuts both STRICTLY greater than m. All complete L+
atoms, including E and absent directed binary tuples, are retained.
-/

namespace SuccessorTree.V10

/-- Lifting a shortened initial socle of length at most m and
then deleting m maps each of its ordinary coordinates to itself,
and never changes the distinguished type vertex. -/
theorem deleteTypeCoordinate_lift_below
    (m small large : Nat)
    (hm : m < large) (hsmall : small ≤ m)
    (x : Option (Fin small)) :
    deleteTypeCoordinate m large hm
        (liftTypeCoordinate (show small ≤ large - 1 by omega) x) =
      liftTypeCoordinate (show small ≤ large by omega) x := by
  cases x with
  | none => rfl
  | some i =>
      apply congrArg some
      apply Fin.ext
      have hi : i.val < m := lt_of_lt_of_le i.isLt hsmall
      simp [deleteTypeCoordinate, deletedSocleCoordinate,
        liftTypeCoordinate, deleteAt_below m i.val hi]

/-- If the retained cut is at most the deleted coordinate m, the
complete L+ initial prefix is entirely unaffected by deletion.
The equality covers all unary, diagonal, directed binary and E bits. -/
theorem PartialTypeWithE.deleteOrdinary_restrict_below
    {large db du dd : Nat}
    (T : PartialTypeWithE large db du dd)
    (m : Nat) (hm : m < large)
    (small : Nat) (hSmall : small ≤ m) :
    (T.deleteOrdinary m hm).restrict
        (show small ≤ large - 1 by omega) =
      T.restrict (show small ≤ large by omega) := by
  let hShort : small ≤ large - 1 := by omega
  let hFull : small ≤ large := by omega
  have hCoord (x : Option (Fin small)) :
      deleteTypeCoordinate m large hm
          (liftTypeCoordinate hShort x) =
        liftTypeCoordinate hFull x :=
    deleteTypeCoordinate_lift_below m small large hm hSmall x
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      change T.lReduct.binary
          (deleteTypeCoordinate m large hm (liftTypeCoordinate hShort a))
          (deleteTypeCoordinate m large hm (liftTypeCoordinate hShort b)) r =
        T.lReduct.binary
          (liftTypeCoordinate hFull a) (liftTypeCoordinate hFull b) r
      rw [hCoord a, hCoord b]
    · intro a r
      change T.lReduct.unary
          (deleteTypeCoordinate m large hm (liftTypeCoordinate hShort a)) r =
        T.lReduct.unary (liftTypeCoordinate hFull a) r
      rw [hCoord a]
    · intro a r
      change T.lReduct.diagonal
          (deleteTypeCoordinate m large hm (liftTypeCoordinate hShort a)) r =
        T.lReduct.diagonal (liftTypeCoordinate hFull a) r
      rw [hCoord a]
  · intro a b
    change T.eRelation
        (deleteTypeCoordinate m large hm (liftTypeCoordinate hShort a))
        (deleteTypeCoordinate m large hm (liftTypeCoordinate hShort b)) =
      T.eRelation
        (liftTypeCoordinate hFull a) (liftTypeCoordinate hFull b)
    rw [hCoord a, hCoord b]

/-- The crossing case of prefix preservation: when the shorter
complete raw type ends at or before m, it remains literally a
prefix of the upper type AFTER m is deleted. -/
theorem rawPartialTypePrefix_delete_above_cut
    {db du dd : Nat}
    {a b : RawPartialTypeNode db du dd}
    (hab : a ≤ b)
    (m : Nat)
    (hLow : a.1 ≤ m)
    (hHigh : m < b.1) :
    a ≤ rawPartialTypeDeleteAt b m hHigh := by
  have hShort : a.1 ≤ b.1 - 1 := by omega
  refine ⟨hShort, ?_⟩
  change a.2 = (b.2.deleteOrdinary m hHigh).restrict hShort
  calc
    a.2 = b.2.restrict hab.1 := hab.2
    _ = (b.2.deleteOrdinary m hHigh).restrict hShort :=
      (PartialTypeWithE.deleteOrdinary_restrict_below
        b.2 m hHigh a.1 hLow).symm

end SuccessorTree.V10

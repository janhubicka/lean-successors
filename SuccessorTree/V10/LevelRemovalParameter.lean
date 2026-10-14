import SuccessorTree.V10.LevelRemovalType
import SuccessorTree.V10.ExtractSuccessorComponents
import Mathlib.Tactic

/-!
# Complete successor-parameter transport under earlier coordinate deletion

A one-step successor with last ordinary coordinate ell+1 has its
shortened parameter at free cut f≤ell+1. After deleting an earlier
ordinary coordinate m<ell+1, the last ordinary vertex is renumbered
to ell. Its canonical parameter is:
* the old parameter with coordinate m deleted, when m<f;
* literally the old parameter, when f≤m.

This treats all directed positive/absent L atoms, unary/diagonal
facts and every E pair, including the distinguished type vertex.
It is an independent finite L+ identity, not yet the
uniform M2 successor law or corrected finite L-only B3 necessity.
-/

namespace SuccessorTree.V10

/-- When the deleted coordinate belongs to the old parameter's
initial socle, extracting the new last-ordinary parameter and
mapping its coordinates back to the old full type agrees with
first extracting the old parameter and then deleting that
coordinate from the parameter. -/
theorem deleteTypeCoordinate_lastOrdinary_inside
    (ell m f : Nat)
    (hm : m < ell + 1)
    (hf : f ≤ ell + 1)
    (hmf : m < f)
    (x : Option (Fin (f - 1))) :
    deleteTypeCoordinate m (ell + 2) (by omega)
        (lastOrdinaryCoordinate ell (f - 1) (by omega) x) =
      lastOrdinaryCoordinate (ell + 1) f hf
        (deleteTypeCoordinate m f hmf x) := by
  cases x with
  | none =>
      apply congrArg some
      apply Fin.ext
      change deleteAt m ell = ell + 1
      rw [deleteAt_above m ell (by omega)]
  | some i =>
      apply congrArg some
      apply Fin.ext
      rfl

/-- If the deleted coordinate was within the free E-socle of the
last ordinary vertex, its complete canonical parameter is exactly
the coordinate-deleted former parameter. -/
theorem PartialTypeWithE.deleteOrdinary_lastOrdinary_inside
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 2) db du dd)
    (m f : Nat) (hm : m < ell + 1)
    (hf : f ≤ ell + 1) (hmf : m < f) :
    ((Q.deleteOrdinary m (by omega)).lastOrdinaryParameter
       (f - 1) (by omega)) =
      (Q.lastOrdinaryParameter f hf).deleteOrdinary m hmf := by
  have hCoord (x : Option (Fin (f - 1))) :
      deleteTypeCoordinate m (ell + 2) (by omega)
          (lastOrdinaryCoordinate ell (f - 1) (by omega) x) =
        lastOrdinaryCoordinate (ell + 1) f hf
          (deleteTypeCoordinate m f hmf x) :=
    deleteTypeCoordinate_lastOrdinary_inside ell m f hm hf hmf x
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      change Q.lReduct.binary
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (lastOrdinaryCoordinate ell (f - 1) (by omega) a))
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (lastOrdinaryCoordinate ell (f - 1) (by omega) b)) r =
        Q.lReduct.binary
          (lastOrdinaryCoordinate (ell + 1) f hf
            (deleteTypeCoordinate m f hmf a))
          (lastOrdinaryCoordinate (ell + 1) f hf
            (deleteTypeCoordinate m f hmf b)) r
      rw [hCoord a, hCoord b]
    · intro a r
      change Q.lReduct.unary
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (lastOrdinaryCoordinate ell (f - 1) (by omega) a)) r =
        Q.lReduct.unary
          (lastOrdinaryCoordinate (ell + 1) f hf
            (deleteTypeCoordinate m f hmf a)) r
      rw [hCoord a]
    · intro a r
      change Q.lReduct.diagonal
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (lastOrdinaryCoordinate ell (f - 1) (by omega) a)) r =
        Q.lReduct.diagonal
          (lastOrdinaryCoordinate (ell + 1) f hf
            (deleteTypeCoordinate m f hmf a)) r
      rw [hCoord a]
  · intro a b
    change Q.eRelation
        (deleteTypeCoordinate m (ell + 2) (by omega)
          (lastOrdinaryCoordinate ell (f - 1) (by omega) a))
        (deleteTypeCoordinate m (ell + 2) (by omega)
          (lastOrdinaryCoordinate ell (f - 1) (by omega) b)) =
      Q.eRelation
        (lastOrdinaryCoordinate (ell + 1) f hf
          (deleteTypeCoordinate m f hmf a))
        (lastOrdinaryCoordinate (ell + 1) f hf
          (deleteTypeCoordinate m f hmf b))
    rw [hCoord a, hCoord b]

/-- When the deleted coordinate is outside the old free socle,
all its parameter coordinates are retained at the same addresses;
only the last ordinary vertex's number decreases. -/
theorem deleteTypeCoordinate_lastOrdinary_outside
    (ell m f : Nat) (hm : m < ell + 1)
    (hf : f ≤ m)
    (x : Option (Fin f)) :
    deleteTypeCoordinate m (ell + 2) (by omega)
        (lastOrdinaryCoordinate ell f (by omega) x) =
      lastOrdinaryCoordinate (ell + 1) f (by omega) x := by
  cases x with
  | none =>
      apply congrArg some
      apply Fin.ext
      change deleteAt m ell = ell + 1
      rw [deleteAt_above m ell (by omega)]
  | some i =>
      apply congrArg some
      apply Fin.ext
      change deleteAt m i.val = i.val
      exact deleteAt_below m i.val (by omega)

/-- When the deleted coordinate lies at or above the free cut,
the full canonical parameter record is literally unchanged. -/
theorem PartialTypeWithE.deleteOrdinary_lastOrdinary_outside
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 2) db du dd)
    (m f : Nat) (hm : m < ell + 1)
    (hf : f ≤ m) :
    ((Q.deleteOrdinary m (by omega)).lastOrdinaryParameter
       f (by omega)) =
      Q.lastOrdinaryParameter f (by omega) := by
  have hCoord (x : Option (Fin f)) :
      deleteTypeCoordinate m (ell + 2) (by omega)
          (lastOrdinaryCoordinate ell f (by omega) x) =
        lastOrdinaryCoordinate (ell + 1) f (by omega) x :=
    deleteTypeCoordinate_lastOrdinary_outside ell m f hm hf x
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      change Q.lReduct.binary
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (lastOrdinaryCoordinate ell f (by omega) a))
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (lastOrdinaryCoordinate ell f (by omega) b)) r =
        Q.lReduct.binary
          (lastOrdinaryCoordinate (ell + 1) f (by omega) a)
          (lastOrdinaryCoordinate (ell + 1) f (by omega) b) r
      rw [hCoord a, hCoord b]
    · intro a r
      change Q.lReduct.unary
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (lastOrdinaryCoordinate ell f (by omega) a)) r =
        Q.lReduct.unary
          (lastOrdinaryCoordinate (ell + 1) f (by omega) a) r
      rw [hCoord a]
    · intro a r
      change Q.lReduct.diagonal
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (lastOrdinaryCoordinate ell f (by omega) a)) r =
        Q.lReduct.diagonal
          (lastOrdinaryCoordinate (ell + 1) f (by omega) a) r
      rw [hCoord a]
  · intro a b
    change Q.eRelation
        (deleteTypeCoordinate m (ell + 2) (by omega)
          (lastOrdinaryCoordinate ell f (by omega) a))
        (deleteTypeCoordinate m (ell + 2) (by omega)
          (lastOrdinaryCoordinate ell f (by omega) b)) =
      Q.eRelation
        (lastOrdinaryCoordinate (ell + 1) f (by omega) a)
        (lastOrdinaryCoordinate (ell + 1) f (by omega) b)
    rw [hCoord a, hCoord b]

end SuccessorTree.V10

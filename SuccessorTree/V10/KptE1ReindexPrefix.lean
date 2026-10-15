import SuccessorTree.V10.KptE1OldPrefixGeometry
import SuccessorTree.V10.KptE1ShapeLevelCut
import SuccessorTree.V10.ShapeMapFullRecovery
import Mathlib.Tactic

/-!
# Retained-coordinate reindexing commutes with the old Kpt predecessor

A genuine one-step target type Q at level ell+1 has predecessor
Q.restrict ell. Pulling Q back to the source coordinates including
the new last ordinary vertex, then restricting to the old n vertices,
must be the SAME complete L+ record as first taking the target old
predecessor and then retaining just the source old levels.

This is a literal identity of all L, E, true and false atomic tables,
not merely an induced embedding. It uses the previously verified
PartialTypeWithE.reindexOrdinary API without a compatibility shim.

The real shape-level retained indices automatically satisfy the
needed commutation equation. The next step identifies the restricted
target predecessor with the ACTUAL image of the source predecessor,
then applies shapeMap_recovers_complete_record to recover its
literal original L+ type.
-/

namespace SuccessorTree.V10

/-- Full reindexing commutes with predecessor restriction whenever
the enlarged index map agrees with the old one on every OLD
coordinate. No E1, shape-map or admissibility assumption. -/
theorem PartialTypeWithE.reindexOrdinary_restrict_last
    {n ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (rho : Fin n → Fin ell)
    (rhoPlus : Fin (n + 1) → Fin (ell + 1))
    (hCompat : ∀ i : Fin n,
      rhoPlus i.castSucc = (rho i).castSucc) :
    (Q.reindexOrdinary rhoPlus).restrict (Nat.le_succ n) =
      (Q.restrict (Nat.le_succ ell)).reindexOrdinary rho := by
  have hCoordinate (x : Option (Fin n)) :
      (liftTypeCoordinate (Nat.le_succ n) x).map rhoPlus =
        liftTypeCoordinate (Nat.le_succ ell) (x.map rho) := by
    cases x with
    | none => rfl
    | some i =>
        change some (rhoPlus i.castSucc) =
          some ((rho i).castSucc)
        exact congrArg some (hCompat i)
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y r
      change Q.lReduct.binary
          ((liftTypeCoordinate (Nat.le_succ n) x).map rhoPlus)
          ((liftTypeCoordinate (Nat.le_succ n) y).map rhoPlus) r =
        Q.lReduct.binary
          (liftTypeCoordinate (Nat.le_succ ell) (x.map rho))
          (liftTypeCoordinate (Nat.le_succ ell) (y.map rho)) r
      rw [hCoordinate x, hCoordinate y]
    · intro x r
      change Q.lReduct.unary
          ((liftTypeCoordinate (Nat.le_succ n) x).map rhoPlus) r =
        Q.lReduct.unary
          (liftTypeCoordinate (Nat.le_succ ell) (x.map rho)) r
      rw [hCoordinate x]
    · intro x r
      change Q.lReduct.diagonal
          ((liftTypeCoordinate (Nat.le_succ n) x).map rhoPlus) r =
        Q.lReduct.diagonal
          (liftTypeCoordinate (Nat.le_succ ell) (x.map rho)) r
      rw [hCoordinate x]
  · intro x y
    change Q.eRelation
        ((liftTypeCoordinate (Nat.le_succ n) x).map rhoPlus)
        ((liftTypeCoordinate (Nat.le_succ n) y).map rhoPlus) =
      Q.eRelation
        (liftTypeCoordinate (Nat.le_succ ell) (x.map rho))
        (liftTypeCoordinate (Nat.le_succ ell) (y.map rho))
    rw [hCoordinate x, hCoordinate y]

/-- Retained old source indices inside the old target predecessor,
using the ACTUAL strict level map. -/
noncomputable def kptShapeOldRetainedIndex
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n : Nat) :
    Fin n → Fin (kptShapeLevelMap family F n) :=
  fun i =>
    ⟨kptShapeLevelMap family F i.val,
      (kptShapeLevelMap_strictMono family F) i.isLt⟩

/-- The genuine enlarged retained index is precisely the
one-coordinate extension of the old index. -/
theorem kptShapeRetainedIndices_compatible
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n : Nat) (i : Fin n) :
    kptShapeLastRetainedIndex family F n i.castSucc =
      (kptShapeOldRetainedIndex family F n i).castSucc := by
  apply Fin.ext
  rfl

/-- A target successor's complete pulled-back old type is the
literal retained-coordinate pullback of its target predecessor. -/
theorem kptShapeReindex_restrict_last
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n : Nat)
    (Q : PartialTypeWithE
      (kptShapeLevelMap family F n + 1) db du dd) :
    (Q.reindexOrdinary
        (kptShapeLastRetainedIndex family F n)).restrict
          (Nat.le_succ n) =
      (Q.restrict (Nat.le_succ (kptShapeLevelMap family F n))).
        reindexOrdinary (kptShapeOldRetainedIndex family F n) := by
  exact Q.reindexOrdinary_restrict_last
    (kptShapeOldRetainedIndex family F n)
    (kptShapeLastRetainedIndex family F n)
    (kptShapeRetainedIndices_compatible family F n)

end SuccessorTree.V10

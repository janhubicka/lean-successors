import SuccessorTree.V10.LevelRemovalRawPrefix
import SuccessorTree.V10.LevelRemovalBoundaryRestoration
import Mathlib.Tactic

/-!
# The last-coordinate deletion is literally the old predecessor

The intrinsic M2 first factor deletes the missing target coordinate.
At the FIRST affected source level that coordinate is the final
ordinary socle point of every image F(x).

Consequently deleting that coordinate removes only the top ordinary
column and is literally the complete L+ initial restriction: it does
not alter the remaining directed relations, singleton data or E bits.

This is the B1 predecessor identity needed for the eventual boundary
prescription D(x) -> F(x). It is a pure record theorem, needing no
corrected B3, M2 factorization or new finite-age hypothesis.
-/

namespace SuccessorTree.V10

/-- The coordinate map omitting the last ordinary vertex of a
nonempty socle is exactly the usual inclusion of the smaller socle.
The distinguished type vertex is unchanged. -/
theorem deleteLastTypeCoordinate_eq_lift
    (m : Nat) (x : Option (Fin m)) :
    deleteTypeCoordinate m (m + 1) (Nat.lt_succ_self m) x =
      liftTypeCoordinate (Nat.le_succ m) x := by
  cases x with
  | none => rfl
  | some i =>
      apply congrArg some
      apply Fin.ext
      change deleteAt m i.val = i.val
      exact deleteAt_below m i.val i.isLt

/-- Deleting the LAST ordinary coordinate agrees with complete
induced restriction of the full L+ record (not merely its L reduct). -/
theorem PartialTypeWithE.deleteOrdinary_last_eq_restrict
    {m db du dd : Nat}
    (T : PartialTypeWithE (m + 1) db du dd) :
    T.deleteOrdinary m (Nat.lt_succ_self m) =
      T.restrict (Nat.le_succ m) := by
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      change T.lReduct.binary
          (deleteTypeCoordinate m (m + 1) (Nat.lt_succ_self m) a)
          (deleteTypeCoordinate m (m + 1) (Nat.lt_succ_self m) b) r =
        T.lReduct.binary
          (liftTypeCoordinate (Nat.le_succ m) a)
          (liftTypeCoordinate (Nat.le_succ m) b) r
      rw [deleteLastTypeCoordinate_eq_lift m a,
        deleteLastTypeCoordinate_eq_lift m b]
    · intro a r
      change T.lReduct.unary
          (deleteTypeCoordinate m (m + 1) (Nat.lt_succ_self m) a) r =
        T.lReduct.unary (liftTypeCoordinate (Nat.le_succ m) a) r
      rw [deleteLastTypeCoordinate_eq_lift m a]
    · intro a r
      change T.lReduct.diagonal
          (deleteTypeCoordinate m (m + 1) (Nat.lt_succ_self m) a) r =
        T.lReduct.diagonal (liftTypeCoordinate (Nat.le_succ m) a) r
      rw [deleteLastTypeCoordinate_eq_lift m a]
  · intro a b
    change T.eRelation
        (deleteTypeCoordinate m (m + 1) (Nat.lt_succ_self m) a)
        (deleteTypeCoordinate m (m + 1) (Nat.lt_succ_self m) b) =
      T.eRelation
        (liftTypeCoordinate (Nat.le_succ m) a)
        (liftTypeCoordinate (Nat.le_succ m) b)
    rw [deleteLastTypeCoordinate_eq_lift m a,
      deleteLastTypeCoordinate_eq_lift m b]

/-- At any positive raw Kpt level, deleting the final ordinary
coordinate gives exactly the canonical full predecessor at the
preceding level. The equality includes ALL L+ atoms. -/
theorem rawPartialTypeDeleteAt_last_eq_ancestor
    {db du dd : Nat}
    (N : RawPartialTypeNode db du dd)
    (hPos : 0 < N.1) :
    rawPartialTypeDeleteAt N (N.1 - 1) (by omega) =
      rawPartialTypeAncestor N (N.1 - 1) (Nat.sub_le N.1 1) := by
  rcases N with ⟨cut,T⟩
  cases cut with
  | zero => omega
  | succ m =>
      change
        (⟨m,T.deleteOrdinary m (Nat.lt_succ_self m)⟩ :
          RawPartialTypeNode db du dd) =
        (⟨m,T.restrict (Nat.le_succ m)⟩ :
          RawPartialTypeNode db du dd)
      exact congrArg (Sigma.mk m)
        (T.deleteOrdinary_last_eq_restrict)

/-- At the first affected SOURCE level, every image F(x) has the
same ordinary cut as F(a₀). Therefore the fixed deleted coordinate
m=lev(F(a₀))-1 is literally its final ordinary coordinate, and the
intrinsic deleted image D(x) equals the exact complete predecessor
of F(x) at level m. This is the desired B1 property on the actual
boundary restoration graph, with no finite B3 age hypothesis. -/
theorem uniformGapDeletedShapeMap_boundary_raw_ancestor
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : AdmissibleKptNode family)
    (hx : LevelTree.lev x = LevelTree.lev a₀) :
    (uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x).1 =
      rawPartialTypeAncestor (F x).1 (LevelTree.lev (F a₀) - 1)
        (by
          have hlevel := F.level_eq_of_level_eq hx
          change (F x).1.1 = (F a₀).1.1 at hlevel
          omega) := by
  change (uniformGapDeletedKpt family F q₀ a₀ hprev hgap x).1 = _
  obtain ⟨hm,hRaw⟩ :=
    uniformGapDeletedKpt_above_raw family F q₀ a₀
      hprev hgap x (Nat.le_of_eq hx.symm)
  rw [hRaw]
  have hlevel := F.level_eq_of_level_eq hx
  change (F x).1.1 = (F a₀).1.1 at hlevel
  have hM : LevelTree.lev (F a₀) - 1 = (F x).1.1 - 1 := by
    change (F a₀).1.1 - 1 = (F x).1.1 - 1
    omega
  rw [hM]
  have hPositive : 0 < (F x).1.1 := by
    have ha : 0 < (F a₀).1.1 := by omega
    omega
  exact rawPartialTypeDeleteAt_last_eq_ancestor (F x).1 hPositive

/-- The intrinsic boundary deletion is below F(x) as an actual
admissible Kpt predecessor, not merely as a compatible L-reduct. -/
theorem uniformGapDeletedShapeMap_boundary_le_image
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : AdmissibleKptNode family)
    (hx : LevelTree.lev x = LevelTree.lev a₀) :
    uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x ≤ F x := by
  change (uniformGapDeletedShapeMap family F q₀ a₀
    hprev hgap x).1 ≤ (F x).1
  rw [uniformGapDeletedShapeMap_boundary_raw_ancestor
    family F q₀ a₀ hprev hgap x hx]
  exact rawPartialTypeAncestor_le (F x).1
    (LevelTree.lev (F a₀) - 1)
    (by
      have hlevel := F.level_eq_of_level_eq hx
      change (F x).1.1 = (F a₀).1.1 at hlevel
      omega)

end SuccessorTree.V10

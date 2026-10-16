import SuccessorTree.V10.KptE1ImageParameterCases

/-!
# Complete Kpt parameter transport at the true target predecessor

The earlier shape-level parameter lemma works with a target indexed
by the numerical image of the source level.  The canonical successor,
however, is indexed by the actual node `F a`.  This module removes
that dependent-index mismatch directly, using a reusable finite
coordinate-transport lemma.  It preserves every positive and absent
L/E atom, including both directed binary orientations.

No new E1 assumption and no alternative reindexing API is introduced.
-/

namespace SuccessorTree.V10

/-- Taking the last ordinary parameter commutes with two complete
ordinary-coordinate reindexings when their actual new-coordinate
and earlier-coordinate maps agree. -/
theorem PartialTypeWithE.reindexOrdinary_lastOrdinaryParameter
    {n ell f g db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (rho : Fin (n + 1) → Fin (ell + 1))
    (eta : Fin f → Fin g)
    (hf : f ≤ n) (hg : g ≤ ell)
    (hLast : rho (Fin.last n) = Fin.last ell)
    (hEarly : ∀ i : Fin f,
      (lastOrdinaryCoordinate n f hf (some i)).map rho =
        lastOrdinaryCoordinate ell g hg (some (eta i))) :
    (Q.reindexOrdinary rho).lastOrdinaryParameter f hf =
      (Q.lastOrdinaryParameter g hg).reindexOrdinary eta := by
  have hCoordinate (x : Option (Fin f)) :
      (lastOrdinaryCoordinate n f hf x).map rho =
        lastOrdinaryCoordinate ell g hg (x.map eta) := by
    cases x with
    | none =>
        change some (rho (Fin.last n)) = some (Fin.last ell)
        exact congrArg some hLast
    | some i => exact hEarly i
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y r
      change Q.lReduct.binary
          ((lastOrdinaryCoordinate n f hf x).map rho)
          ((lastOrdinaryCoordinate n f hf y).map rho) r =
        Q.lReduct.binary
          (lastOrdinaryCoordinate ell g hg (x.map eta))
          (lastOrdinaryCoordinate ell g hg (y.map eta)) r
      rw [hCoordinate x, hCoordinate y]
    · intro x r
      change Q.lReduct.unary
          ((lastOrdinaryCoordinate n f hf x).map rho) r =
        Q.lReduct.unary
          (lastOrdinaryCoordinate ell g hg (x.map eta)) r
      rw [hCoordinate x]
    · intro x r
      change Q.lReduct.diagonal
          ((lastOrdinaryCoordinate n f hf x).map rho) r =
        Q.lReduct.diagonal
          (lastOrdinaryCoordinate ell g hg (x.map eta)) r
      rw [hCoordinate x]
  · intro x y
    change Q.eRelation
        ((lastOrdinaryCoordinate n f hf x).map rho)
        ((lastOrdinaryCoordinate n f hf y).map rho) =
      Q.eRelation
        (lastOrdinaryCoordinate ell g hg (x.map eta))
        (lastOrdinaryCoordinate ell g hg (y.map eta))
    rw [hCoordinate x, hCoordinate y]

/-- Genuine node-indexed parameter transport.  This is the exact
target height needed by the canonical Kpt successor, and avoids
postulating equality of arbitrary independently indexed types. -/
theorem kptShapeReindex_parameter_atNode
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (a : AdmissibleKptNode family)
    (f : Nat) (hf : f ≤ LevelTree.lev a)
    (Q : PartialTypeWithE ((F a).1.1 + 1) db du dd)
    (hg : kptShapeLevelMap family F f ≤ (F a).1.1) :
    (Q.reindexOrdinary
      (kptShapeLastIndexAtNode family F a)).lastOrdinaryParameter f hf =
      (Q.lastOrdinaryParameter (kptShapeLevelMap family F f) hg).reindexOrdinary (kptShapeOldRetainedIndex family F f) := by
  exact Q.reindexOrdinary_lastOrdinaryParameter
    (kptShapeLastIndexAtNode family F a)
    (kptShapeOldRetainedIndex family F f)
    hf hg (kptShapeLastIndexAtNode_last family F a) (by
      intro i
      apply congrArg some
      apply Fin.ext
      rfl)

/-- From the *actual* target parameter F(x) at its canonical
image cut, recover the literal L+ source parameter x after pulling
back the target one-step type. -/
theorem kptShapeReindex_parameter_recovers_atNode
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (a x : AdmissibleKptNode family)
    (hx : LevelTree.lev x ≤ LevelTree.lev a)
    (Q : PartialTypeWithE ((F a).1.1 + 1) db du dd)
    (hg : kptShapeLevelMap family F (LevelTree.lev x) ≤ (F a).1.1)
    (hTargetParameter :
      (F x).1 =
        (⟨kptShapeLevelMap family F (LevelTree.lev x),
          Q.lastOrdinaryParameter
            (kptShapeLevelMap family F (LevelTree.lev x)) hg⟩ :
          RawPartialTypeNode db du dd)) :
    (Q.reindexOrdinary
      (kptShapeLastIndexAtNode family F a)).lastOrdinaryParameter
        (LevelTree.lev x) hx = x.1.2 := by
  calc
    (Q.reindexOrdinary
      (kptShapeLastIndexAtNode family F a)).lastOrdinaryParameter
        (LevelTree.lev x) hx =
      (Q.lastOrdinaryParameter
        (kptShapeLevelMap family F (LevelTree.lev x)) hg).reindexOrdinary
            (kptShapeOldRetainedIndex family F (LevelTree.lev x)) :=
      kptShapeReindex_parameter_atNode family F a
        (LevelTree.lev x) hx Q hg
    _ = shapeMapRetainedRecord family F x := by
      change
        (Q.lastOrdinaryParameter
          (kptShapeLevelMap family F (LevelTree.lev x)) hg).reindexOrdinary
            (kptShapeOldRetainedIndex family F (LevelTree.lev x)) =
        (F x).1.2.reindexOrdinary (retainedSocleIndex family F x)
      exact (rawPartialType_reindex_eq_of_sigma
        (F x).1
        (Q.lastOrdinaryParameter
          (kptShapeLevelMap family F (LevelTree.lev x)) hg)
        hTargetParameter
        (retainedSocleIndex family F x)
        (kptShapeOldRetainedIndex family F (LevelTree.lev x))
        (by
          intro i
          apply Fin.ext
          rfl)).symm
    _ = x.1.2 := shapeMap_recovers_complete_record family F x

end SuccessorTree.V10

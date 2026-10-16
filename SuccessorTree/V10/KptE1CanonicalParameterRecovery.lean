import SuccessorTree.V10.KptE1CanonicalSourceStep

/-!
# Recover the actual source singleton parameter from its image

A source shape map preserves the *entire* L+ record on retained
coordinates, not merely the levels or the induced positive relations.

The target of a genuine canonical successor determines the image of
each nonempty source parameter: F(x) is the canonical shortened type
of the newest ordinary target vertex at its E cut. Reindexing that
shortened target record back to the source coordinates therefore gives
the literal original source parameter x.

The proof reuses the existing `reindexOrdinary` and
`shapeMap_recovers_complete_record`; no new representation or
abstract E1 assumption is introduced.
-/

namespace SuccessorTree.V10

/-- If the image of a genuine source Kpt node is the target's
canonical last-ordinary-vertex parameter at its actual shape level,
then the canonical parameter of the *retained* successor is
literally the original source node's complete L+ record.

The statement includes all absent directed L bits, unary/diagonal
bits and auxiliary E atoms. -/
theorem kptShapeReindex_parameter_recovers_source
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n : Nat) (x : AdmissibleKptNode family)
    (hx : x.1.1 ≤ n)
    (Q : PartialTypeWithE
      (kptShapeLevelMap family F n + 1) db du dd)
    (hTargetParameter :
      (F x).1 =
        (⟨kptShapeLevelMap family F x.1.1,
          Q.lastOrdinaryParameter
            (kptShapeLevelMap family F x.1.1)
            ((kptShapeLevelMap_strictMono family F).monotone hx)⟩ :
          RawPartialTypeNode db du dd)) :
    (Q.reindexOrdinary
      (kptShapeLastRetainedIndex family F n)).lastOrdinaryParameter x.1.1 hx = x.1.2 := by
  calc
    (Q.reindexOrdinary
      (kptShapeLastRetainedIndex family F n)).lastOrdinaryParameter x.1.1 hx =
      (Q.lastOrdinaryParameter
        (kptShapeLevelMap family F x.1.1)
        ((kptShapeLevelMap_strictMono family F).monotone hx)).reindexOrdinary
            (kptShapeOldRetainedIndex family F x.1.1) :=
      kptShapeReindex_parameter_commutes
        family F n x.1.1 hx Q
    _ = shapeMapRetainedRecord family F x := by
      unfold shapeMapRetainedRecord
      rw [hTargetParameter]
      rfl
    _ = x.1.2 :=
      shapeMap_recovers_complete_record family F x

end SuccessorTree.V10

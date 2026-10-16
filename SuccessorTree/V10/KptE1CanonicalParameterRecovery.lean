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

/-- Transport a reindexed complete L+ record across the equality
of two dependent raw Sigma nodes.  The explicit Fin.cast coordinate
identity keeps both the record and its indexing map well-typed; a
direct `rw` on the Sigma equality would not. -/
theorem rawPartialType_reindex_eq_of_sigma
    {n m db du dd : Nat}
    (S : RawPartialTypeNode db du dd)
    (T : PartialTypeWithE m db du dd)
    (hRaw : S = (⟨m, T⟩ : RawPartialTypeNode db du dd))
    (rho : Fin n → Fin S.1)
    (eta : Fin n → Fin m)
    (hCoord : ∀ i : Fin n,
      Fin.cast (congrArg Sigma.fst hRaw) (rho i) = eta i) :
    S.2.reindexOrdinary rho = T.reindexOrdinary eta := by
  cases hRaw
  have hMap : rho = eta := by
    funext i
    simpa using hCoord i
  subst eta
  rfl


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
      change
        (Q.lastOrdinaryParameter
          (kptShapeLevelMap family F x.1.1)
          ((kptShapeLevelMap_strictMono family F).monotone hx)).reindexOrdinary
            (kptShapeOldRetainedIndex family F x.1.1) =
        (F x).1.2.reindexOrdinary (retainedSocleIndex family F x)
      exact (rawPartialType_reindex_eq_of_sigma
        (F x).1
        (Q.lastOrdinaryParameter
          (kptShapeLevelMap family F x.1.1)
          ((kptShapeLevelMap_strictMono family F).monotone hx))
        hTargetParameter
        (retainedSocleIndex family F x)
        (kptShapeOldRetainedIndex family F x.1.1)
        (by
          intro i
          apply Fin.ext
          rfl)).symm
    _ = x.1.2 :=
      shapeMap_recovers_complete_record family F x

end SuccessorTree.V10

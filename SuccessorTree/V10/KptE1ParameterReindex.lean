import SuccessorTree.V10.KptE1ReindexPrefix

/-!
# Canonical Kpt parameter commutes with genuine shape-level pullback

The final source-successor reconstruction needs its *actual* parameter,
not an arbitrary shortened type.  For a Kpt shape map with strict level
map λ, taking the shortened type of the last ordinary vertex at the
source cut f commutes with retaining the actual target λ-coordinates.

The equality is of complete L+ types: directed binary atoms, negative
facts, unary and diagonal records, and the auxiliary E matrix.  In
particular there is no appeal to OneLevelPullback or a fabricated
E-expansion of an L-only age witness.
-/

namespace SuccessorTree.V10

/-- Extracting the last-ordinary parameter after retaining the
source levels is exactly the retained target canonical parameter.
The target cut is the genuine shape-level image of f. -/
theorem kptShapeReindex_parameter_commutes
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n f : Nat) (hf : f ≤ n)
    (Q : PartialTypeWithE
      (kptShapeLevelMap family F n + 1) db du dd) :
    (Q.reindexOrdinary (kptShapeLastRetainedIndex family F n)).
      lastOrdinaryParameter f hf =
    (Q.lastOrdinaryParameter (kptShapeLevelMap family F f)
        ((kptShapeLevelMap_strictMono family F).monotone hf)).
      reindexOrdinary (kptShapeOldRetainedIndex family F f) := by
  let rho := kptShapeLastRetainedIndex family F n
  let eta := kptShapeOldRetainedIndex family F f
  let hfImage : kptShapeLevelMap family F f ≤
      kptShapeLevelMap family F n :=
    (kptShapeLevelMap_strictMono family F).monotone hf
  have hCoordinate (x : Option (Fin f)) :
      (lastOrdinaryCoordinate n f hf x).map rho =
        lastOrdinaryCoordinate
          (kptShapeLevelMap family F n)
          (kptShapeLevelMap family F f)
          hfImage (x.map eta) := by
    cases x with
    | none =>
        change some (kptShapeLastRetainedIndex family F n (Fin.last n)) =
          some (Fin.last (kptShapeLevelMap family F n))
        exact congrArg some (kptShapeLastRetainedIndex_last family F n)
    | some i =>
        apply congrArg some
        apply Fin.ext
        rfl
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y r
      change Q.lReduct.binary
          ((lastOrdinaryCoordinate n f hf x).map rho)
          ((lastOrdinaryCoordinate n f hf y).map rho) r =
        Q.lReduct.binary
          (lastOrdinaryCoordinate
            (kptShapeLevelMap family F n)
            (kptShapeLevelMap family F f) hfImage (x.map eta))
          (lastOrdinaryCoordinate
            (kptShapeLevelMap family F n)
            (kptShapeLevelMap family F f) hfImage (y.map eta)) r
      rw [hCoordinate x, hCoordinate y]
    · intro x r
      change Q.lReduct.unary
          ((lastOrdinaryCoordinate n f hf x).map rho) r =
        Q.lReduct.unary
          (lastOrdinaryCoordinate
            (kptShapeLevelMap family F n)
            (kptShapeLevelMap family F f) hfImage (x.map eta)) r
      rw [hCoordinate x]
    · intro x r
      change Q.lReduct.diagonal
          ((lastOrdinaryCoordinate n f hf x).map rho) r =
        Q.lReduct.diagonal
          (lastOrdinaryCoordinate
            (kptShapeLevelMap family F n)
            (kptShapeLevelMap family F f) hfImage (x.map eta)) r
      rw [hCoordinate x]
  · intro x y
    change Q.eRelation
        ((lastOrdinaryCoordinate n f hf x).map rho)
        ((lastOrdinaryCoordinate n f hf y).map rho) =
      Q.eRelation
        (lastOrdinaryCoordinate
          (kptShapeLevelMap family F n)
          (kptShapeLevelMap family F f) hfImage (x.map eta))
        (lastOrdinaryCoordinate
          (kptShapeLevelMap family F n)
          (kptShapeLevelMap family F f) hfImage (y.map eta))
    rw [hCoordinate x, hCoordinate y]

end SuccessorTree.V10

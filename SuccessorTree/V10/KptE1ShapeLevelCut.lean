import SuccessorTree.V10.KptE1ReindexedNewColumn
import SuccessorTree.V10.LevelRemovalSkipsOnly
import Mathlib.Tactic

/-!
# The exact new-column E cut is reflected by a genuine Kpt shape level map

For a concrete Kpt ShapeMap F, the common level map lambda is proved
STRICTLY INCREASING, not merely monotone. Given a source predecessor
level n, retain all source ordinary coordinates 0,...,n in a target
complete successor Q of length lambda(n)+1 by sending i to lambda(i).
The last source ordinary maps to the last target ordinary literally.

The strict level-map theorem gives the crucial E-cut equality

    lambda(i) < lambda(f)  iff  i < f.

Combined with the separately checked last-column transport lemma,
this proves that a target canonical last E column of cut lambda(f)
pulls back to a source canonical last column of cut f, with reverse
E absence and both directions of the no-new-binary-tuples rule.

This removes the *arithmetical* E1 cut-preimage hypothesis for a
genuine Kpt shape map. The remaining proof must identify the target
cut lambda(f) from the canonical empty/singleton image-parameter,
recover the earlier source record, establish the forbidden-free
admissibility source, and invoke the source successor graph.
-/

namespace SuccessorTree.V10

/-- Retain the source ordinary coordinates INCLUDING the newly
introduced last ordinary vertex. Its target position is the literal
shape level map of its source position. -/
noncomputable def kptShapeLastRetainedIndex
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n : Nat) :
    Fin (n + 1) →
      Fin (kptShapeLevelMap family F n + 1) :=
  fun i =>
    ⟨kptShapeLevelMap family F i.val, by
      have hi : i.val ≤ n := by omega
      have hle := (kptShapeLevelMap_strictMono family F).monotone hi
      omega⟩

/-- The full retained ordinary index is genuinely increasing,
including the newly introduced successor coordinate. -/
theorem kptShapeLastRetainedIndex_strictMono
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n : Nat) :
    StrictMono (kptShapeLastRetainedIndex family F n) := by
  intro i j hij
  change kptShapeLevelMap family F i.val <
    kptShapeLevelMap family F j.val
  exact (kptShapeLevelMap_strictMono family F) hij

/-- The terminal source ordinary vertex maps to the terminal
target ordinary vertex, not to an arbitrary later coordinate. -/
theorem kptShapeLastRetainedIndex_last
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n : Nat) :
    kptShapeLastRetainedIndex family F n (Fin.last n) =
      Fin.last (kptShapeLevelMap family F n) := by
  apply Fin.ext
  rfl

/-- Every genuine Kpt shape-map level cut pulls back to precisely
the corresponding initial source segment. No E1 assumption occurs. -/
theorem kptShapeLastRetainedIndex_cut_iff
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n f : Nat) (i : Fin n) :
    (kptShapeLastRetainedIndex family F n i.castSucc).val <
      kptShapeLevelMap family F f ↔ i.val < f := by
  change kptShapeLevelMap family F i.val <
    kptShapeLevelMap family F f ↔ i.val < f
  constructor
  · intro h
    by_contra hn
    have hle : f ≤ i.val := Nat.le_of_not_gt hn
    have hmon :=
      (kptShapeLevelMap_strictMono family F).monotone hle
    omega
  · intro hlt
    exact (kptShapeLevelMap_strictMono family F) hlt

/-- A target canonical Kpt new ordinary column with cut equal to the
image of f yields a genuine canonical source new column at cut f
under the ACTUAL source/target level indexing. This is the specific
finite record step required when pulling back a defined Kpt successor
along a one-level-skipping member of the real Kpt monoid. -/
theorem kptShapeLastRetainedIndex_validNewColumn
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n f : Nat)
    (Q : PartialTypeWithE
      (kptShapeLevelMap family F n + 1) db du dd)
    (hValid : ValidNewOrdinaryColumn Q
      (kptShapeLevelMap family F f)) :
    ValidNewOrdinaryColumn
      (Q.reindexOrdinary
        (kptShapeLastRetainedIndex family F n)) f := by
  exact Q.reindexOrdinary_validNewColumn
    (kptShapeLastRetainedIndex family F n)
    (kptShapeLastRetainedIndex_strictMono family F n)
    (kptShapeLastRetainedIndex_last family F n)
    (kptShapeLevelMap family F f) hValid f
    (kptShapeLastRetainedIndex_cut_iff family F n f)

end SuccessorTree.V10

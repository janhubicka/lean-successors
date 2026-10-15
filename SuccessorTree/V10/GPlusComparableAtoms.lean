import SuccessorTree.V10.GPlusShapeImagePrefix
import Mathlib.Tactic

/-!
# Observation 6.42: exact binary and E atoms of comparable G+ vertices

Suppose A is a genuine proper-prefix code of B. Definition 6.40 reads
both directed binary atoms, and the auxiliary E atoms, from the two
last coordinates |A|-1 and |B|-1 of the single larger finite code B.

Its genuine ShapeMap image has last coordinates precisely
lambda(|A|-1) and lambda(|B|-1). The already verified full finite-code
reconstruction at the retained numerical coordinates of B therefore
supplies literal equalities of these two binary and E atoms, including
false values.

Proper-prefix reflection guarantees that originally unrelated G+
branches remain unrelated, so they gain no new off-diagonal L or E
tuples. This is a full induced comparison of both ordered directions,
not just a positive relational homomorphism.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

namespace FinitePartialCode

/-- Exact finite-code equality transports a directed binary atom,
including false data, with the dependent source length cast. -/
theorem binary_eq_of_eq
    {C D : FinitePartialCode db du dd}
    (h : C = D) (i j : Fin D.size) (t : Fin db) :
    C.binary (Fin.cast (congrArg FinitePartialCode.size h).symm i)
      (Fin.cast (congrArg FinitePartialCode.size h).symm j) t =
    D.binary i j t := by
  cases h
  rfl

theorem eRelation_eq_of_eq
    {C D : FinitePartialCode db du dd}
    (h : C = D) (i j : Fin D.size) :
    C.eRelation (Fin.cast (congrArg FinitePartialCode.size h).symm i)
      (Fin.cast (congrArg FinitePartialCode.size h).symm j) =
    D.eRelation i j := by
  cases h
  rfl

end FinitePartialCode

/-- Full code recovery evaluated at ANY two actual original vertices
recovers both oriented binary bits, not only at the last vertices. -/
theorem shapeImage_retained_binary
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (B : FiniteGPlusVertex family)
    (i j : Fin B.val.size) (t : Fin db) :
    (gPlusShapeImage F B).val.binary
      (Fin.cast (gPlusShapeImage_size F B).symm
        (shapeImageRetainedIndex F B i))
      (Fin.cast (gPlusShapeImage_size F B).symm
        (shapeImageRetainedIndex F B j)) t =
    B.val.binary i j t := by
  have hRec := shapeImageRetainedCode_eq F B
  have hAtom := FinitePartialCode.binary_eq_of_eq hRec i j t
  change (gPlusShapeImage F B).val.binary
      (Fin.cast (gPlusShapeImage_size F B).symm
        (shapeImageRetainedIndex F B i))
      (Fin.cast (gPlusShapeImage_size F B).symm
        (shapeImageRetainedIndex F B j)) t =
    B.val.binary i j t at hAtom
  exact hAtom

theorem shapeImage_retained_E
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (B : FiniteGPlusVertex family)
    (i j : Fin B.val.size) :
    (gPlusShapeImage F B).val.eRelation
      (Fin.cast (gPlusShapeImage_size F B).symm
        (shapeImageRetainedIndex F B i))
      (Fin.cast (gPlusShapeImage_size F B).symm
        (shapeImageRetainedIndex F B j)) =
    B.val.eRelation i j := by
  have hRec := shapeImageRetainedCode_eq F B
  have hAtom := FinitePartialCode.eRelation_eq_of_eq hRec i j
  change (gPlusShapeImage F B).val.eRelation
      (Fin.cast (gPlusShapeImage_size F B).symm
        (shapeImageRetainedIndex F B i))
      (Fin.cast (gPlusShapeImage_size F B).symm
        (shapeImageRetainedIndex F B j)) =
    B.val.eRelation i j at hAtom
  exact hAtom

/-- In a comparable pair, the first retained last coordinate in the
larger image code is exactly the last coordinate of the smaller image
code interpreted inside the larger image code. -/
theorem shapeImage_retainedLower_eq_lowerLast
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : FiniteGPlusVertex family)
    (hAB : A.IsProperPrefix B) :
    Fin.cast (gPlusShapeImage_size F B).symm
      (shapeImageRetainedIndex F B (A.lowerLastIn B hAB)) =
    (gPlusShapeImage F A).lowerLastIn (gPlusShapeImage F B)
      ((gPlusShapeImage_properPrefix_iff F A B).2 hAB) := by
  apply Fin.ext
  change kptShapeLevelMap family F (A.val.size - 1) =
    (gPlusShapeImage F A).val.size - 1
  rw [gPlusShapeImage_size F A]
  unfold gPlusShapeImageCut
  omega

/-- The retained last coordinate of the larger source code agrees
with the last coordinate of its image code. -/
theorem shapeImage_retainedUpper_eq_last
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (B : FiniteGPlusVertex family) :
    Fin.cast (gPlusShapeImage_size F B).symm
      (shapeImageRetainedIndex F B B.last) =
    (gPlusShapeImage F B).last := by
  apply Fin.ext
  change kptShapeLevelMap family F (B.val.size - 1) =
    (gPlusShapeImage F B).val.size - 1
  rw [gPlusShapeImage_size F B]
  unfold gPlusShapeImageCut
  omega

/-- Both binary orientations are read from the same larger code, and
the forward ordered-pair atom is preserved exactly. -/
theorem gPlusShapeImage_binary_forward
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : FiniteGPlusVertex family)
    (hAB : A.IsProperPrefix B) (t : Fin db) :
    finiteGPlusBinary (gPlusShapeImage F A) (gPlusShapeImage F B) t =
      finiteGPlusBinary A B t := by
  have hImg := (gPlusShapeImage_properPrefix_iff F A B).2 hAB
  rw [finiteGPlusBinary_forward _ _ t hImg,
    finiteGPlusBinary_forward _ _ t hAB]
  have hAtom :=
    shapeImage_retained_binary F B (A.lowerLastIn B hAB) B.last t
  rw [shapeImage_retainedLower_eq_lowerLast F A B hAB,
      shapeImage_retainedUpper_eq_last F B] at hAtom
  exact hAtom

/-- The reversed directed binary atom is distinct and is preserved,
including its absence. -/
theorem gPlusShapeImage_binary_reverse
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : FiniteGPlusVertex family)
    (hAB : A.IsProperPrefix B) (t : Fin db) :
    finiteGPlusBinary (gPlusShapeImage F B) (gPlusShapeImage F A) t =
      finiteGPlusBinary B A t := by
  have hImg := (gPlusShapeImage_properPrefix_iff F A B).2 hAB
  rw [finiteGPlusBinary_reverse _ _ t hImg,
    finiteGPlusBinary_reverse _ _ t hAB]
  have hAtom :=
    shapeImage_retained_binary F B B.last (A.lowerLastIn B hAB) t
  rw [shapeImage_retainedLower_eq_lowerLast F A B hAB,
      shapeImage_retainedUpper_eq_last F B] at hAtom
  exact hAtom

/-- The reverse orientation of the auxiliary E relation is also
the corresponding E table entry of the same larger finite code. -/
theorem finiteGPlusE_reverse
    (A B : FiniteGPlusVertex family) (hAB : A.IsProperPrefix B) :
    finiteGPlusE B A =
      B.val.eRelation B.last (A.lowerLastIn B hAB) := by
  have hNot : ¬ B.IsProperPrefix A :=
    FiniteGPlusVertex.properPrefix_asymm hAB
  simp [finiteGPlusE, hNot, hAB, FiniteGPlusVertex.lowerLastIn]

theorem gPlusShapeImage_E_forward
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : FiniteGPlusVertex family) (hAB : A.IsProperPrefix B) :
    finiteGPlusE (gPlusShapeImage F A) (gPlusShapeImage F B) =
      finiteGPlusE A B := by
  have hImg := (gPlusShapeImage_properPrefix_iff F A B).2 hAB
  rw [finiteGPlusE_forward _ _ hImg,
    finiteGPlusE_forward _ _ hAB]
  have hAtom :=
    shapeImage_retained_E F B (A.lowerLastIn B hAB) B.last
  rw [shapeImage_retainedLower_eq_lowerLast F A B hAB,
      shapeImage_retainedUpper_eq_last F B] at hAtom
  exact hAtom

theorem gPlusShapeImage_E_reverse
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : FiniteGPlusVertex family) (hAB : A.IsProperPrefix B) :
    finiteGPlusE (gPlusShapeImage F B) (gPlusShapeImage F A) =
      finiteGPlusE B A := by
  have hImg := (gPlusShapeImage_properPrefix_iff F A B).2 hAB
  rw [finiteGPlusE_reverse _ _ hImg, finiteGPlusE_reverse _ _ hAB]
  have hAtom :=
    shapeImage_retained_E F B B.last (A.lowerLastIn B hAB)
  rw [shapeImage_retainedLower_eq_lowerLast F A B hAB,
      shapeImage_retainedUpper_eq_last F B] at hAtom
  exact hAtom

/-- On arbitrary ordered pairs, both directed off-diagonal binary
values are induced exactly: positive, negative, comparable, equal and
incomparable cases are all covered. -/
theorem gPlusShapeImage_preserves_binary
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : FiniteGPlusVertex family) (t : Fin db) :
    finiteGPlusBinary (gPlusShapeImage F A) (gPlusShapeImage F B) t =
      finiteGPlusBinary A B t := by
  by_cases hAB : A.IsProperPrefix B
  · exact gPlusShapeImage_binary_forward F A B hAB t
  by_cases hBA : B.IsProperPrefix A
  · exact gPlusShapeImage_binary_reverse F B A hBA t
  have hNotAB : ¬ (gPlusShapeImage F A).IsProperPrefix
      (gPlusShapeImage F B) := by
    intro h
    exact hAB ((gPlusShapeImage_properPrefix_iff F A B).1 h)
  have hNotBA : ¬ (gPlusShapeImage F B).IsProperPrefix
      (gPlusShapeImage F A) := by
    intro h
    exact hBA ((gPlusShapeImage_properPrefix_iff F B A).1 h)
  rw [finiteGPlusBinary_incomparable _ _ t hNotAB hNotBA,
    finiteGPlusBinary_incomparable _ _ t hAB hBA]

/-- The auxiliary E relation on ALL ordered pairs is induced exactly.
No new E facts are attached to incomparable or identical vertices. -/
theorem gPlusShapeImage_preserves_E
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : FiniteGPlusVertex family) :
    finiteGPlusE (gPlusShapeImage F A) (gPlusShapeImage F B) =
      finiteGPlusE A B := by
  by_cases hAB : A.IsProperPrefix B
  · exact gPlusShapeImage_E_forward F A B hAB
  by_cases hBA : B.IsProperPrefix A
  · exact gPlusShapeImage_E_reverse F B A hBA
  have hNotAB : ¬ (gPlusShapeImage F A).IsProperPrefix
      (gPlusShapeImage F B) := by
    intro h
    exact hAB ((gPlusShapeImage_properPrefix_iff F A B).1 h)
  have hNotBA : ¬ (gPlusShapeImage F B).IsProperPrefix
      (gPlusShapeImage F A) := by
    intro h
    exact hBA ((gPlusShapeImage_properPrefix_iff F B A).1 h)
  rw [finiteGPlusE_incomparable _ _ hNotAB hNotBA,
    finiteGPlusE_incomparable _ _ hAB hBA]

end SuccessorTree.V10

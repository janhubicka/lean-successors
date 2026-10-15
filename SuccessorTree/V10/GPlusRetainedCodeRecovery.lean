import SuccessorTree.V10.GPlusRetainedCoordinates
import Mathlib.Tactic

/-!
# Observation 6.42: recover the entire ordinary source finite code

The genuine admissible Kpt ShapeMap recovery theorem already proves
that the complete image partial type, reindexed by the common strictly
increasing level map, equals the source partial type. This file
restricts that verified theorem to ORDINARY vertices and packages it
as equality of finite partial L+ codes, including all directed positive
and negative binary atoms, unary and diagonal atoms, and auxiliary E.

The second theorem proves that cutting the image at ANY level after
all retained original coordinates does not lose any of the recovered
table. This includes the manuscript's cut lambda(n-1)+1.

No new ShapeMap axioms, representation hypotheses or age assumptions
are introduced. Transport from an arbitrary Kpt node to the canonical
G+ vertex remains a separate subsequent bridge.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- Full ordinary finite-code recovery on the retained coordinates
of ANY actual admissible Kpt source node. -/
theorem shapeMap_recovers_ordinaryCode
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (U : AdmissibleKptNode family) :
    (RawPartialTypeNode.ordinaryCode (F U).1).reindex U.1.1
      (retainedSocleIndex family F U) =
    RawPartialTypeNode.ordinaryCode U.1 := by
  have hRec := shapeMap_recovers_complete_record family F U
  have hBinary :
      (fun i j t =>
        (F U).1.2.lReduct.binary
          (some (retainedSocleIndex family F U i))
          (some (retainedSocleIndex family F U j)) t) =
      (fun i j t => U.1.2.lReduct.binary (some i) (some j) t) := by
    funext i j t
    exact congrArg
      (fun Q : PartialTypeWithE U.1.1 db du dd =>
        Q.lReduct.binary (some i) (some j) t) hRec
  have hUnary :
      (fun i t =>
        (F U).1.2.lReduct.unary
          (some (retainedSocleIndex family F U i)) t) =
      (fun i t => U.1.2.lReduct.unary (some i) t) := by
    funext i t
    exact congrArg
      (fun Q : PartialTypeWithE U.1.1 db du dd =>
        Q.lReduct.unary (some i) t) hRec
  have hDiagonal :
      (fun i t =>
        (F U).1.2.lReduct.diagonal
          (some (retainedSocleIndex family F U i)) t) =
      (fun i t => U.1.2.lReduct.diagonal (some i) t) := by
    funext i t
    exact congrArg
      (fun Q : PartialTypeWithE U.1.1 db du dd =>
        Q.lReduct.diagonal (some i) t) hRec
  have hE :
      (fun i j =>
        (F U).1.2.eRelation
          (some (retainedSocleIndex family F U i))
          (some (retainedSocleIndex family F U j))) =
      (fun i j => U.1.2.eRelation (some i) (some j)) := by
    funext i j
    exact congrArg
      (fun Q : PartialTypeWithE U.1.1 db du dd =>
        Q.eRelation (some i) (some j)) hRec
  change
    FinitePartialCode.mk U.1.1
      (fun i j t =>
        (F U).1.2.lReduct.binary
          (some (retainedSocleIndex family F U i))
          (some (retainedSocleIndex family F U j)) t)
      (fun i t =>
        (F U).1.2.lReduct.unary
          (some (retainedSocleIndex family F U i)) t)
      (fun i t =>
        (F U).1.2.lReduct.diagonal
          (some (retainedSocleIndex family F U i)) t)
      (fun i j =>
        (F U).1.2.eRelation
          (some (retainedSocleIndex family F U i))
          (some (retainedSocleIndex family F U j))) =
    FinitePartialCode.mk U.1.1
      (fun i j t => U.1.2.lReduct.binary (some i) (some j) t)
      (fun i t => U.1.2.lReduct.unary (some i) t)
      (fun i t => U.1.2.lReduct.diagonal (some i) t)
      (fun i j => U.1.2.eRelation (some i) (some j))
  rw [hBinary, hUnary, hDiagonal, hE]

/-- Even if F adds unretained image coordinates, an initial image
cut containing every retained source coordinate has EXACTLY the same
complete induced source code after reindexing. -/
theorem shapeMap_recovers_ordinaryCode_of_imagePrefix
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (U : AdmissibleKptNode family)
    (d : Nat)
    (hd : d ≤ (F U).1.1)
    (hRet : ∀ i : Fin U.1.1,
      kptShapeLevelMap family F i.val < d) :
    ((RawPartialTypeNode.ordinaryCode (F U).1).restrict d hd).reindex
        U.1.1
        (fun i : Fin U.1.1 =>
          (⟨kptShapeLevelMap family F i.val, hRet i⟩ : Fin d)) =
      RawPartialTypeNode.ordinaryCode U.1 := by
  calc
    ((RawPartialTypeNode.ordinaryCode (F U).1).restrict d hd).reindex
        U.1.1
        (fun i : Fin U.1.1 =>
          (⟨kptShapeLevelMap family F i.val, hRet i⟩ : Fin d)) =
      (RawPartialTypeNode.ordinaryCode (F U).1).reindex
        U.1.1 (retainedSocleIndex family F U) := rfl
    _ = RawPartialTypeNode.ordinaryCode U.1 :=
      shapeMap_recovers_ordinaryCode F U

end SuccessorTree.V10

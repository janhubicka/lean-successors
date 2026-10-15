import SuccessorTree.V10.GPlusRetainedCodeRecovery
import Mathlib.Tactic

/-!
# Observation 6.42: recover any genuine G+ source code from its image

The preceding module verifies complete finite-code recovery for a genuine
Kpt source type and its image, even after an image-prefix cut. This
module specializes that result to the actual image gPlusShapeImage F A
of every valid finite G+ vertex A.

The only nontrivial bookkeeping is dependent finite lengths:
  - the canonical cap has level exactly size(A), propositionally;
  - the image G+ vertex is the restriction of F(cap(A)) to the actual
    manuscript cut lambda(size(A)-1)+1;
  - the retained-coordinate map has the same numerical addresses as
    the verified full-record recovery map.

Two general finite-code congruence lemmas isolate this bookkeeping.
The main theorem then states that pulling the actual image finite
code back along the retained numerical addresses gives EXACTLY A.
Both directions and absences of all L+ relations, including E, are
covered. No representation interface or additional ShapeMap axiom is
introduced.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

namespace FinitePartialCode

/-- Pullbacks from a prefix coincide with pullbacks from the full
finite code whenever the corresponding indices have equal numerical
values. This handles all four finite tables, not just positive facts. -/
theorem reindex_of_prefix
    {C D : FinitePartialCode db du dd}
    (d : Nat) (hd : d ≤ C.size)
    (hD : D = C.restrict d hd)
    (n : Nat)
    (rhoD : Fin n → Fin D.size)
    (rhoC : Fin n → Fin C.size)
    (hRho : ∀ i, (rhoD i).val = (rhoC i).val) :
    D.reindex n rhoD = C.reindex n rhoC := by
  subst D
  have hLift (i : Fin n) :
      (⟨(rhoD i).val, lt_of_lt_of_le (rhoD i).isLt hd⟩ :
        Fin C.size) = rhoC i := Fin.ext (hRho i)
  have hBinary :
      (fun i j t => (C.restrict d hd).binary (rhoD i) (rhoD j) t) =
      (fun i j t => C.binary (rhoC i) (rhoC j) t) := by
    funext i j t
    change C.binary
      ⟨(rhoD i).val, lt_of_lt_of_le (rhoD i).isLt hd⟩
      ⟨(rhoD j).val, lt_of_lt_of_le (rhoD j).isLt hd⟩ t =
      C.binary (rhoC i) (rhoC j) t
    rw [hLift i, hLift j]
  have hUnary :
      (fun i t => (C.restrict d hd).unary (rhoD i) t) =
      (fun i t => C.unary (rhoC i) t) := by
    funext i t
    change C.unary
      ⟨(rhoD i).val, lt_of_lt_of_le (rhoD i).isLt hd⟩ t =
      C.unary (rhoC i) t
    rw [hLift i]
  have hDiagonal :
      (fun i t => (C.restrict d hd).diagonal (rhoD i) t) =
      (fun i t => C.diagonal (rhoC i) t) := by
    funext i t
    change C.diagonal
      ⟨(rhoD i).val, lt_of_lt_of_le (rhoD i).isLt hd⟩ t =
      C.diagonal (rhoC i) t
    rw [hLift i]
  have hE :
      (fun i j => (C.restrict d hd).eRelation (rhoD i) (rhoD j)) =
      (fun i j => C.eRelation (rhoC i) (rhoC j)) := by
    funext i j
    change C.eRelation
      ⟨(rhoD i).val, lt_of_lt_of_le (rhoD i).isLt hd⟩
      ⟨(rhoD j).val, lt_of_lt_of_le (rhoD j).isLt hd⟩ =
      C.eRelation (rhoC i) (rhoC j)
    rw [hLift i, hLift j]
  change
    FinitePartialCode.mk n
      (fun i j t => (C.restrict d hd).binary (rhoD i) (rhoD j) t)
      (fun i t => (C.restrict d hd).unary (rhoD i) t)
      (fun i t => (C.restrict d hd).diagonal (rhoD i) t)
      (fun i j => (C.restrict d hd).eRelation (rhoD i) (rhoD j)) =
    FinitePartialCode.mk n
      (fun i j t => C.binary (rhoC i) (rhoC j) t)
      (fun i t => C.unary (rhoC i) t)
      (fun i t => C.diagonal (rhoC i) t)
      (fun i j => C.eRelation (rhoC i) (rhoC j))
  rw [hBinary, hUnary, hDiagonal, hE]

/-- Changing the source length of a finite-code pullback along a
proved equality merely casts the input coordinates. -/
theorem reindex_change_size
    (C : FinitePartialCode db du dd)
    {n m : Nat} (h : n = m)
    (rho : Fin n → Fin C.size) :
    C.reindex m (fun i => rho (Fin.cast h.symm i)) =
      C.reindex n rho := by
  subst m
  rfl

end FinitePartialCode

/-- Recover the ACTUAL original G+ vertex code from its image under
any genuine Kpt ShapeMap, at the manuscript's shorter image cut. -/
theorem shapeImageRetainedCode_eq
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) :
    shapeImageRetainedCode F A = A.val := by
  let U := A.canonicalCap
  let D := (gPlusShapeImage F A).val
  let C := RawPartialTypeNode.ordinaryCode (F U).1
  let d := gPlusShapeImageCut F A
  have hd : d ≤ C.size :=
    gPlusShapeImageCut_le_capImage F A
  have hD : D = C.restrict d hd :=
    gPlusShapeImage_code_of_fullCap F A
  let rhoD : Fin A.val.size → Fin D.size :=
    fun i => Fin.cast (gPlusShapeImage_size F A).symm
      (shapeImageRetainedIndex F A i)
  have hLen : U.1.1 = A.val.size := A.canonicalCap_level
  let rhoC : Fin A.val.size → Fin C.size :=
    fun i => retainedSocleIndex family F U
      (Fin.cast hLen.symm i)
  have hRho : ∀ i : Fin A.val.size,
      (rhoD i).val = (rhoC i).val := by
    intro i
    rfl
  have hPull :
      D.reindex A.val.size rhoD =
        C.reindex A.val.size rhoC :=
    FinitePartialCode.reindex_of_prefix d hd hD
      A.val.size rhoD rhoC hRho
  have hChange :
      C.reindex A.val.size rhoC =
        C.reindex U.1.1 (retainedSocleIndex family F U) :=
    FinitePartialCode.reindex_change_size C hLen
      (retainedSocleIndex family F U)
  have hRecover :
      C.reindex U.1.1 (retainedSocleIndex family F U) =
        RawPartialTypeNode.ordinaryCode U.1 :=
    shapeMap_recovers_ordinaryCode F U
  have hCap :
      RawPartialTypeNode.ordinaryCode U.1 = A.val :=
    A.canonicalCap_ordinaryCode
  calc
    shapeImageRetainedCode F A = D.reindex A.val.size rhoD := rfl
    _ = C.reindex A.val.size rhoC := hPull
    _ = C.reindex U.1.1 (retainedSocleIndex family F U) := hChange
    _ = RawPartialTypeNode.ordinaryCode U.1 := hRecover
    _ = A.val := hCap

end SuccessorTree.V10

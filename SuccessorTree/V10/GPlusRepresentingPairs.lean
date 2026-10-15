import SuccessorTree.V10.GPlusOrdinaryCompatibility
import Mathlib.Tactic

/-!
# Observation 6.42: the actual representing pair v(S,T)

For two genuine admissible Kpt nodes S<T, the paper's vertex v(S,T)
is the complete ordinary L+ code of the prefix of T at level(S)+1.
Here that prefix is an actual admissible Kpt ancestor, and we convert
it to a genuine forbidden-free finite G+ vertex using the checked
intrinsic ordinary-code construction.

The construction behaves correctly under an arbitrary genuine Kpt
ShapeMap: (S,T) maps to (F(S),F(T)), whose cut is
lambda(level(S))+1. There is no hypothesis that a shape map already
acts on G+, and no invented representation interface.

A valid G+ vertex A also supplies an ACTUAL representing pair: take
the neutral cap over A and its ancestor at size(A)-1.  The equality
v(S_A,T_A)=A is the next separate ordinary-cap-record lemma, not
assumed here.  This distinction is important for the converse in
Observation 6.42 and eventual envelope coverage.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- The exact source data for the manuscript's v(S+,T+), including
the strict Kpt prefix rather than an abstract pair of level numbers. -/
structure GPlusRepresentingPair
    (family : List (NormalizedForbidden db du dd)) where
  lower : AdmissibleKptNode family
  upper : AdmissibleKptNode family
  lower_lt_upper : lower < upper

namespace GPlusRepresentingPair

/-- The numerical cut producing v(S,T) from the larger partial type. -/
noncomputable def cut (P : GPlusRepresentingPair family) : Nat :=
  LevelTree.lev P.lower + 1

theorem cut_pos (P : GPlusRepresentingPair family) :
    0 < P.cut := by
  unfold cut
  omega

/-- Strict Kpt ancestry guarantees the one-step-higher cut is available. -/
theorem cut_le_upper (P : GPlusRepresentingPair family) :
    P.cut ≤ LevelTree.lev P.upper := by
  have hlt := LevelTree.lt_level_lt P.lower_lt_upper
  unfold cut
  omega

/-- The actual admissible Kpt prefix whose ordinary code is v(S,T). -/
noncomputable def representedNode (P : GPlusRepresentingPair family) :
    AdmissibleKptNode family :=
  admissibleKptAncestor P.upper P.cut P.cut_le_upper

/-- The manuscript's vertex v(S,T), as an actual finite valid G+ code. -/
noncomputable def vertex (P : GPlusRepresentingPair family) :
    FiniteGPlusVertex family :=
  AdmissibleKptNode.toGPlus P.representedNode
    (by
      change 0 < P.cut
      exact P.cut_pos)

@[simp] theorem representedNode_level (P : GPlusRepresentingPair family) :
    LevelTree.lev P.representedNode = P.cut := by
  rfl

@[simp] theorem vertex_size (P : GPlusRepresentingPair family) :
    P.vertex.val.size = P.cut := by
  change P.representedNode.1.1 = P.cut
  rfl

/-- The vertex's entire induced finite L+ record is the ordinary
record of T at the exact cut, not of an arbitrary witness. -/
theorem vertex_code (P : GPlusRepresentingPair family) :
    P.vertex.val = RawPartialTypeNode.ordinaryCode P.representedNode.1 := by
  exact AdmissibleKptNode.toGPlus_code P.representedNode
    (by change 0 < P.cut; exact P.cut_pos)

/-- A genuine ShapeMap sends a strict representing pair to another
strict pair. This requires only the checked weak-successor theorem
implying preservation of strict Kpt order. -/
def image
    (P : GPlusRepresentingPair family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family)) :
    GPlusRepresentingPair family where
  lower := F P.lower
  upper := F P.upper
  lower_lt_upper := F.map_lt_of_lt P.lower_lt_upper

@[simp] theorem image_cut
    (P : GPlusRepresentingPair family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family)) :
    (P.image F).cut =
      kptShapeLevelMap family F (LevelTree.lev P.lower)+1 := by
  change LevelTree.lev (F P.lower)+1 =
    kptShapeLevelMap family F (LevelTree.lev P.lower)+1
  rw [kptShapeLevelMap_eq family F P.lower]

@[simp] theorem image_vertex_size
    (P : GPlusRepresentingPair family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family)) :
    (P.image F).vertex.val.size =
      kptShapeLevelMap family F (LevelTree.lev P.lower)+1 := by
  rw [GPlusRepresentingPair.vertex_size (P.image F), P.image_cut F]

/-- Every valid finite G+ vertex has a genuine candidate representing
pair: the neutral cap above A and its immediate shorter ancestor.
The equality of their ordinary code with A is the next lemma. -/
noncomputable def canonical
    (A : FiniteGPlusVertex family) : GPlusRepresentingPair family := by
  let U := A.canonicalCap
  have hPos := finiteGPlusVertex_size_pos A
  have hLe : A.val.size-1 ≤ LevelTree.lev U := by
    rw [show LevelTree.lev U = A.val.size from A.canonicalCap_level]
    omega
  let S := admissibleKptAncestor U (A.val.size-1) hLe
  have hSU : S ≤ U := admissibleKptAncestor_le U _ hLe
  have hLevelS : LevelTree.lev S = A.val.size-1 := rfl
  have hLevelU : LevelTree.lev U = A.val.size :=
    A.canonicalCap_level
  have hNe : S ≠ U := by
    intro hEq
    have h := congrArg LevelTree.lev hEq
    rw [hLevelS,hLevelU] at h
    omega
  exact ⟨S,U,lt_of_le_of_ne hSU hNe⟩

/-- The canonical representing pair has the correct one-point cut. -/
theorem canonical_cut
    (A : FiniteGPlusVertex family) :
    (canonical A).cut = A.val.size := by
  change A.val.size-1+1 = A.val.size
  have hPos := finiteGPlusVertex_size_pos A
  omega

end GPlusRepresentingPair

end SuccessorTree.V10

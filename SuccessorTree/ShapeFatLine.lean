import SuccessorTree.ShapeFirstSplit
import Mathlib.Tactic

/-!
# Algebraic two-block lines in a fat block sequence

The line attached to adjacent cuts c_i<c_{i+1} is defined algebraically by

  q o u_i^+ o p,

where p is the local identity/one-level letter at c_i and q is a one-moving
tail coordinate at c_{i+1}.  This is the right-hand side of the manuscript's
fat-line formula, used here without any geometric pullback claim.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Evaluate one algebraic two-block line member. -/
noncomputable def FatBlockSeq.lineApply
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat)
    (q : AM H (U.cut (i + 1)) 1)
    (p : LineInput (OneLevelLetter H (U.cut i))) :
    AM H (U.cut i) 1 := by
  let P : MMap H := localInputMMap H (U.cut i) p
  let F : MMap H :=
    MMap.comp H (q.representative H)
      (MMap.comp H (U.blockMap H i) P)
  have hcut : U.cut i < U.cut (i + 1) :=
    U.cut_strict (Nat.lt_succ_self i)
  have hfixQ :
      (q.representative H).FixesBelow H (U.cut (i + 1)) :=
    q.representative_fixesBelow H
  have hfixBlock :
      (U.blockMap H i).FixesBelow H (U.cut i) :=
    U.blockMap_fixesBelow H i
  have hfixP :
      P.FixesBelow H (U.cut i) :=
    H.localInputMMap_fixesBelow (U.cut i) p
  exact F.toAM H (U.cut i) 1
    (MMap.comp_fixesBelow H (q.representative H)
      (MMap.comp H (U.blockMap H i) P) (U.cut i)
      (by
        intro x hx
        exact hfixQ x (lt_trans hx hcut))
      (MMap.comp_fixesBelow H (U.blockMap H i) P (U.cut i)
        hfixBlock hfixP))

/-- The distinguished base point of an algebraic line is the first block:
the tail q fixes everything below the next cut. -/
theorem FatBlockSeq.lineApply_base
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat)
    (q : AM H (U.cut (i + 1)) 1) :
    U.lineApply H i q LineInput.base = (U.block i).1 := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hqfix :=
    q.representative_fixesBelow H
  have hblockTop := (U.block i).1.representative_top H
  have hblockVal := congrArg Subtype.val hblockTop
  change
    ((U.block i).1.representative H).restrictLe H (U.cut i) =
      (U.block i).1.1 at hblockVal
  have hxBlock := congrFun hblockVal x
  have hblockLev :
      LevelTree.lev (U.blockMap H i x.1) < U.cut (i + 1) := by
    calc
      LevelTree.lev (U.blockMap H i x.1) =
          H.levelMap (U.blockMap H i).map (LevelTree.lev x.1) :=
        (H.levelMap_eq (U.blockMap H i).map (a := x.1)).symm
      _ ≤ H.levelMap (U.blockMap H i).map (U.cut i) :=
        (H.levelMap_strictMono (U.blockMap H i).map).monotone x.2
      _ = U.cut (i + 1) - 1 := U.blockMap_level_cut H i
      _ < U.cut (i + 1) := by
        have hcut := U.cut_strict (Nat.lt_succ_self i)
        omega
  change
    q.representative H (U.blockMap H i x.1) = (U.block i).1.1 x
  rw [hqfix (U.blockMap H i x.1) hblockLev]
  rw [FatBlockSeq.blockMap]
  rw [H.canonicalExtension_agrees
    ((U.block i).1.representative H) (U.cut i) x.1 x.2]
  exact hxBlock

/-- The total suffix map, packaged as a shape subspace at the suffix cut. -/
noncomputable def FatBlockSeq.tailSubspace
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) :
    ShapeSubspace H (U.cut i) :=
  ⟨(U.tail H i).limit H, (U.tail H i).limit_fixesBelow H⟩

/-- Evaluate a source one-moving word in the suffix limit. -/
noncomputable def FatBlockSeq.evalAt
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat)
    (r : AM H (U.cut i) 1) :
    AM H (U.cut i) 1 :=
  H.shapeAct (U.cut i) (U.tailSubspace H i) r

/-- The empty/identity coordinate evaluates to the first fat block. -/
theorem FatBlockSeq.evalAt_id
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) :
    U.evalAt H i (AM.id1 H (U.cut i)) = (U.block i).1 := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hidTop := (AM.id1 H (U.cut i)).representative_top H
  have hidVal := congrArg Subtype.val hidTop
  change
    ((AM.id1 H (U.cut i)).representative H).restrictLe H (U.cut i) =
      (MMap.id H).restrictLe H (U.cut i) at hidVal
  have hxId := congrFun hidVal x
  have htail :
      (U.tail H i).limit H x.1 = U.blockMap H i x.1 := by
    by_cases hxlt : LevelTree.lev x.1 < U.cut i
    · rw [(U.tail H i).limit_fixesBelow H x.1 hxlt,
        U.blockMap_fixesBelow H i x.1 hxlt]
    · have hxlev : LevelTree.lev x.1 = U.cut i := by omega
      rw [(U.tail H i).tail_limit_eq_cumulative H 0 x.1
        (by simpa [hxlev])]
      change U.blockMap H i x.1 = U.blockMap H i x.1
      rfl
  have hblockTop := (U.block i).1.representative_top H
  have hblockVal := congrArg Subtype.val hblockTop
  change
    ((U.block i).1.representative H).restrictLe H (U.cut i) =
      (U.block i).1.1 at hblockVal
  have hxBlock := congrFun hblockVal x
  change
    (U.tail H i).limit H
        ((AM.id1 H (U.cut i)).representative H x.1) =
      (U.block i).1.1 x
  rw [hxId]
  rw [htail]
  rw [FatBlockSeq.blockMap]
  rw [H.canonicalExtension_agrees
    ((U.block i).1.representative H) (U.cut i) x.1 x.2]
  exact hxBlock

end SMTree
end SuccessorTree

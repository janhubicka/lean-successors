import SuccessorTree.ShapePreserving
import Mathlib.Tactic

/-!
# Shape maps reflect the prefix order

The existing ShapeMap interface supplies level preservation, strict
level order and genuine weak successors, which together imply
monotonicity. Injectivity and the LevelTree unique-ancestor property
also force order REFLECTION: if F(a) is a prefix of F(b), then a was
already a prefix of b.

This elementary argument is independent of M1--M3 and of any
application-specific finite age. It is useful for restricting maps to
their images and for canonical partial inverse constructions.
-/

namespace SuccessorTree.ShapeMap

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

/-- Every shape-preserving map is an order embedding on its image.
It is impossible to create a new comparability between old nodes.
No M2 or pruning axiom is used. -/
theorem reflects_le (F : ShapeMap S) {a b : T}
    (hab : F a ≤ F b) : a ≤ b := by
  have hLevels : LevelTree.lev a ≤ LevelTree.lev b := by
    by_contra hn
    have hBA : LevelTree.lev b < LevelTree.lev a := by omega
    have hFBA := F.level_lt_of_level_lt hBA
    have hFAB := LevelTree.level_le_of_le hab
    omega
  let c := LevelTree.ancestor b (LevelTree.lev a) hLevels
  have hcb : c ≤ b :=
    LevelTree.ancestor_le b (LevelTree.lev a) hLevels
  have hFcb : F c ≤ F b := F.map_le_of_le hcb
  have hcl : LevelTree.lev c = LevelTree.lev a :=
    LevelTree.level_ancestor b (LevelTree.lev a) hLevels
  have hFlevels : LevelTree.lev (F c) = LevelTree.lev (F a) :=
    F.level_eq_of_level_eq hcl
  have hEq : F a = F c := by
    rcases LevelTree.comparable_below hab hFcb with hac | hca
    · exact LevelTree.same_level_of_le hac hFlevels.symm
    · exact (LevelTree.same_level_of_le hca hFlevels).symm
  have hac : a = c := F.injective' hEq
  simpa only [hac] using hcb

end SuccessorTree.ShapeMap

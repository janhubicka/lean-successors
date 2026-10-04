import SuccessorTree.FatTree.FiniteReduction

/-!
# Finitization of the fat-tree order

This file starts the A.2 layer for the fat-tree Ramsey space.  The manuscript
defines x ≤fin y by finite fat-tree reduction together with equality of the
terminal cuts.  We isolate exactly that relation here before proving the
finiteness and approximation clauses of A.2.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FiniteFatTree

variable (H : SMTree S)

/-- The manuscript's finitary order on finite fat trees: reduction with the
same terminal ambient cut. -/
def LeFin (X Y : FiniteFatTree H) : Prop :=
  Reduces H X Y ∧ X.terminalCut = Y.terminalCut

/-- The finitary fat-tree order is reflexive. -/
theorem leFin_refl (X : FiniteFatTree H) : LeFin H X X := by
  exact ⟨reduces_refl H X, rfl⟩

/-- The finitary fat-tree order is transitive. -/
theorem leFin_trans {X Y Z : FiniteFatTree H}
    (hXY : LeFin H X Y) (hYZ : LeFin H Y Z) :
    LeFin H X Z := by
  exact ⟨reduces_trans H hXY.1 hYZ.1, hXY.2.trans hYZ.2⟩

/-- Forgetting the terminal-cut equality leaves an ordinary finite
fat-subtree reduction. -/
theorem reduces_of_leFin {X Y : FiniteFatTree H}
    (h : LeFin H X Y) : Reduces H X Y :=
  h.1

/-- A finitary reduction has exactly the same terminal ambient cut. -/
theorem terminalCut_eq_of_leFin {X Y : FiniteFatTree H}
    (h : LeFin H X Y) : X.terminalCut = Y.terminalCut :=
  h.2

end FiniteFatTree

end SMTree
end SuccessorTree

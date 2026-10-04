import SuccessorTree.FatTree.FiniteReduction
import Mathlib.Data.Fintype.Sigma

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

/-- Finite code for a one-row approximation whose last image level is
strictly below a fixed ambient cut. -/
noncomputable def boundedRowCode (n d : Nat)
    (a : {a : AM H n 1 // a.rowEndLevel H < d}) :
    InitialNode T n → InitialNode T d := by
  intro x
  let F : MMap H := a.1.representative H
  have htop := a.1.representative_top H
  have hval := congrArg Subtype.val htop
  change F.restrictLe H n = a.1.1.1 at hval
  have hx : a.1.1.1 x = F x.1 := by
    exact (congrFun hval x).symm
  refine ⟨a.1.1.1 x, ?_⟩
  have hlev :
      LevelTree.lev (F x.1) ≤ H.levelMap F.map n := by
    calc
      LevelTree.lev (F x.1) =
          H.levelMap F.map (LevelTree.lev x.1) :=
        (H.levelMap_eq F.map (a := x.1)).symm
      _ ≤ H.levelMap F.map n :=
        (H.levelMap_strictMono F.map).monotone x.2
  have hend : H.levelMap F.map n = a.1.rowEndLevel H := rfl
  apply Nat.le_of_lt
  calc
    LevelTree.lev (a.1.1.1 x) = LevelTree.lev (F x.1) := by rw [hx]
    _ ≤ H.levelMap F.map n := hlev
    _ = a.1.rowEndLevel H := hend
    _ < d := a.2

@[simp] theorem boundedRowCode_val (n d : Nat)
    (a : {a : AM H n 1 // a.rowEndLevel H < d})
    (x : InitialNode T n) :
    (boundedRowCode H n d a x).1 = a.1.1.1 x := by
  rfl

/-- The bounded row code is injective: a realized finite row is determined
by its values on the finite source initial segment. -/
theorem boundedRowCode_injective (n d : Nat) :
    Function.Injective (boundedRowCode H n d) := by
  classical
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hx := congrFun hab x
  have hxv := congrArg Subtype.val hx
  simpa only [boundedRowCode_val] using hxv

/-- For fixed source cut and ambient terminal bound there are only finitely
many possible one-row approximations. -/
theorem boundedRows_finite (n d : Nat) :
    Set.Finite {a : AM H n 1 | a.rowEndLevel H < d} := by
  classical
  rw [← Set.finite_coe_iff]
  exact Finite.of_injective
    (boundedRowCode H n d)
    (boundedRowCode_injective H n d)

/-- The subtype of rows with fixed source cut and bounded last image
level is a concrete finite type. -/
noncomputable instance boundedRowFiberFintype (n d : Nat) :
    Fintype {a : AM H n 1 // a.rowEndLevel H < d} :=
  Set.Finite.fintype (boundedRows_finite H n d)

/-- A row below terminal cut `d`, tagged by its source cut.  Source cuts are
strictly below `d` because every row advances to a strictly larger next
cut. -/
def BoundedRow (d : Nat) :=
  Σ n : Fin d, {a : AM H n.1 1 // a.rowEndLevel H < d}

noncomputable instance boundedRowFintype (d : Nat) :
    Fintype (BoundedRow H d) := by
  letI fibers :
      ∀ n : Fin d, Fintype {a : AM H n.1 1 // a.rowEndLevel H < d} :=
    fun n => boundedRowFiberFintype H n.1 d
  infer_instance

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

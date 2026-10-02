import SuccessorTree.ShapeLargeLine
import SuccessorTree.HalesJewett.Forcing
import Mathlib.Tactic

/-!
# The substitution action of M^n on AM^n_1

For the direct fusion proof, finite one-level shape approximations play the
role of finite words and total M-maps fixing the frozen prefix play the role
of infinite subspaces.  Left composition is the substitution action.
-/

namespace SuccessorTree
namespace SMTree

open SuccessorTree.HalesJewett

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Total M-maps fixing all source levels strictly below n. -/
abbrev ShapeSubspace (H : SMTree S) (n : Nat) :=
  {F : MMap H // F.FixesBelow H n}

namespace ShapeSubspace

def id (H : SMTree S) (n : Nat) : ShapeSubspace H n :=
  ⟨MMap.id H, MMap.id_fixesBelow H n⟩

def comp (H : SMTree S) {n : Nat}
    (F G : ShapeSubspace H n) : ShapeSubspace H n :=
  ⟨MMap.comp H F.1 G.1,
    MMap.comp_fixesBelow H F.1 G.1 n F.2 G.2⟩

/-- A tail subspace fixing below m is also a subspace at every earlier cut n. -/
def weaken (H : SMTree S) {n m : Nat} (hnm : n ≤ m)
    (F : ShapeSubspace H m) : ShapeSubspace H n :=
  ⟨F.1, by
    intro x hx
    exact F.2 x (lt_of_lt_of_le hx hnm)⟩

end ShapeSubspace

/-- Left substitution of a total shape subspace into a one-level finite word. -/
noncomputable def shapeAct
    (H : SMTree S) (n : Nat)
    (F : ShapeSubspace H n) (g : AM H n 1) : AM H n 1 :=
  (MMap.comp H F.1 (g.representative H)).toAM H n 1
    (MMap.comp_fixesBelow H F.1 (g.representative H) n
      F.2 (g.representative_fixesBelow H))

@[simp] theorem shapeAct_val
    (H : SMTree S) (n : Nat)
    (F : ShapeSubspace H n) (g : AM H n 1) :
    (H.shapeAct n F g).1 =
      ramseyApprox H (n + 1)
        (MMap.comp H F.1 (g.representative H)) := rfl

/-- The representative chosen after substitution agrees, on the finite source
segment, with the literal composition used to define the substitution. -/
theorem shapeAct_representative_agrees
    (H : SMTree S) (n : Nat)
    (F : ShapeSubspace H n) (g : AM H n 1)
    (x : T) (hx : LevelTree.lev x ≤ n) :
    (H.shapeAct n F g).representative H x =
      F.1 (g.representative H x) := by
  have htop := AM.representative_top H (H.shapeAct n F g)
  have hval := congrArg Subtype.val htop
  change
    ((H.shapeAct n F g).representative H).restrictLe H n =
      (MMap.comp H F.1 (g.representative H)).restrictLe H n at hval
  exact congrFun hval ⟨x, hx⟩

theorem shapeAct_id
    (H : SMTree S) (n : Nat) (g : AM H n 1) :
    H.shapeAct n (ShapeSubspace.id H n) g = g := by
  apply Subtype.ext
  rw [shapeAct_val]
  have htop := g.representative_top H
  apply Subtype.ext
  have hval := congrArg Subtype.val htop
  change
    (g.representative H).restrictLe H n = g.1.1 at hval
  simpa using hval

theorem shapeAct_comp
    (H : SMTree S) (n : Nat)
    (F G : ShapeSubspace H n) (g : AM H n 1) :
    H.shapeAct n (ShapeSubspace.comp H F G) g =
      H.shapeAct n F (H.shapeAct n G g) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change
    F.1 (G.1 (g.representative H x.1)) =
      F.1 ((H.shapeAct n G g).representative H x.1)
  rw [H.shapeAct_representative_agrees n G g x.1 x.2]

/-- Concrete substitution action used by the forcing/fusion proof. -/
noncomputable def shapeSubspaceAction
    (H : SMTree S) (n : Nat) :
    HalesJewett.SubspaceAction (AM H n 1) (ShapeSubspace H n) where
  act := H.shapeAct n
  id := ShapeSubspace.id H n
  comp := ShapeSubspace.comp H
  act_id := H.shapeAct_id n
  act_comp := H.shapeAct_comp n

/-- Terminal target level of a one-level finite shape word. -/
noncomputable def AM.topLevel
    (H : SMTree S) {n : Nat} (g : AM H n 1) : Nat :=
  H.levelMap (g.representative H).map n

theorem AM.level_le_topLevel
    (H : SMTree S) {n : Nat} (g : AM H n 1)
    (x : T) (hx : LevelTree.lev x ≤ n) :
    LevelTree.lev (g.representative H x) ≤ g.topLevel H := by
  calc
    LevelTree.lev (g.representative H x) =
        H.levelMap (g.representative H).map (LevelTree.lev x) :=
      (H.levelMap_eq (g.representative H).map (a := x)).symm
    _ ≤ H.levelMap (g.representative H).map n :=
      (H.levelMap_strictMono (g.representative H).map).monotone hx
    _ = g.topLevel H := rfl

/-- A tail refinement whose cut lies strictly above a finite word cannot
change that word. This is the shape analogue of Shift preserving short words. -/
theorem shapeAct_weaken_eq_self_of_top_lt
    (H : SMTree S)
    {n m : Nat} (hnm : n ≤ m)
    (U : ShapeSubspace H m)
    (g : AM H n 1)
    (hg : g.topLevel H < m) :
    H.shapeAct n (ShapeSubspace.weaken H hnm U) g = g := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hUx :
      U.1 (g.representative H x.1) =
        g.representative H x.1 := by
    apply U.2
    exact lt_of_le_of_lt
      (g.level_le_topLevel H x.1 x.2) hg
  change U.1 (g.representative H x.1) = g.1.1 x
  rw [hUx]
  have htop := g.representative_top H
  have hval := congrArg Subtype.val htop
  change (g.representative H).restrictLe H n = g.1.1 at hval
  exact congrFun hval x

end SMTree
end SuccessorTree

import SuccessorTree.ShapeLargeLine
import SuccessorTree.HalesJewett.Forcing
import Mathlib.Tactic
import Mathlib.Data.Fintype.Pi

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
  apply Subtype.ext
  funext x
  have htop := g.representative_top H
  have hval := congrArg Subtype.val htop
  change
    (g.representative H).restrictLe H n = g.1.1 at hval
  have hx := congrFun hval x
  change (g.representative H).restrictLe H n x = g.1.1 x
  exact hx

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


/-- The identity one-level finite word. -/
def AM.id1 (H : SMTree S) (n : Nat) : AM H n 1 :=
  (MMap.id H).toAM H n 1 (MMap.id_fixesBelow H n)

theorem AM.id1_topLevel (H : SMTree S) (n : Nat) :
    (AM.id1 H n).topLevel H = n := by
  obtain ⟨x, hx⟩ := H.level_nonempty n
  calc
    (AM.id1 H n).topLevel H =
        LevelTree.lev ((AM.id1 H n).representative H x) := by
      simpa [AM.topLevel, hx] using
        H.levelMap_eq ((AM.id1 H n).representative H).map (a := x)
    _ = LevelTree.lev x := by
      have htop := AM.representative_top H (AM.id1 H n)
      have hval := congrArg Subtype.val htop
      change
        ((AM.id1 H n).representative H).restrictLe H n =
          (MMap.id H).restrictLe H n at hval
      have hx' := congrFun hval ⟨x, by simpa [hx]⟩
      exact congrArg LevelTree.lev hx'
    _ = n := hx

private theorem shapeAction_list_map_eq_self
    (p : List T) (F : T → T)
    (h : ∀ x ∈ p, F x = x) :
    p.map F = p := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
      have hx : F x = x := h x (by simp)
      have hxs : ∀ y ∈ xs, F y = y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons]
      rw [hx, ih hxs]

/-- There is only one one-level word whose terminal image level has not moved
past the source level: the identity restriction. -/
theorem AM.eq_id1_of_topLevel_le
    (H : SMTree S) {n : Nat} (g : AM H n 1)
    (hg : g.topLevel H ≤ n) :
    g = AM.id1 H n := by
  have hge : n ≤ g.topLevel H :=
    H.levelMap_id_le (g.representative H).map n
  have htop : g.topLevel H = n := le_antisymm hg hge
  have hfix :
      ∀ x : T, LevelTree.lev x ≤ n →
        g.representative H x = x := by
    intro x hx
    by_cases hlt : LevelTree.lev x < n
    · exact g.representative_fixesBelow H x hlt
    · have hxlev : LevelTree.lev x = n := by omega
      cases n with
      | zero =>
          have hle : x ≤ g.representative H x :=
            (g.representative H).map.root_le' (by simpa [hxlev])
          have hsame :
              LevelTree.lev x =
                LevelTree.lev (g.representative H x) := by
            calc
              LevelTree.lev x = 0 := hxlev
              _ = g.topLevel H := htop.symm
              _ = H.levelMap (g.representative H).map 0 := rfl
              _ = LevelTree.lev (g.representative H x) := by
                simpa [hxlev] using
                  H.levelMap_eq (g.representative H).map (a := x)
          exact (LevelTree.same_level_of_le hle hsame).symm
      | succ p =>
          let y := LevelTree.ancestor x p (by omega)
          have hylev : LevelTree.lev y = p :=
            LevelTree.level_ancestor x p (by omega)
          have hyx : y ≤ x :=
            LevelTree.ancestor_le x p (by omega)
          have hcov : y ⋖ x := by
            apply LevelTree.covBy_of_le_level_succ hyx
            omega
          obtain ⟨params, ch, hs⟩ := S.s3 hcov
          have hyfix : g.representative H y = y :=
            g.representative_fixesBelow H y (by omega)
          have hpfix :
              params.map (g.representative H) = params := by
            apply shapeAction_list_map_eq_self
            intro z hz
            exact g.representative_fixesBelow H z
              (lt_trans (S.parameter_level_lt hs hz) (by omega))
          obtain ⟨d, hd, hdx⟩ :=
            (g.representative H).map.weak_succ' hs
          have hd' : S.succ y params ch = some d := by
            simpa [hyfix, hpfix] using hd
          have hdx0 : d = x := by
            apply Option.some.inj
            calc
              some d = S.succ y params ch := hd'.symm
              _ = some x := hs
          subst d
          have hrepLev :
              LevelTree.lev (g.representative H x) = p + 1 := by
            calc
              LevelTree.lev (g.representative H x) =
                  H.levelMap (g.representative H).map (p + 1) := by
                simpa [hxlev] using
                  (H.levelMap_eq (g.representative H).map (a := x)).symm
              _ = g.topLevel H := rfl
              _ = p + 1 := by simpa using htop
          have hsame :
              LevelTree.lev x =
                LevelTree.lev (g.representative H x) := by
            exact hxlev.trans hrepLev.symm
          exact (LevelTree.same_level_of_le hdx hsame).symm
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have htopg := g.representative_top H
  have hvalg := congrArg Subtype.val htopg
  change (g.representative H).restrictLe H n = g.1.1 at hvalg
  have hxg := congrFun hvalg x
  change g.1.1 x = x.1
  rw [← hxg]
  exact hfix x.1 x.2

/-- Nodes lying strictly below a target cut. -/
abbrev BelowNode (T : Type u) [PartialOrder T] [LevelTree T] (m : Nat) :=
  {x : T // LevelTree.lev x < m}

noncomputable instance belowNodeFintype
    (T : Type u) [PartialOrder T] [LevelTree T] (m : Nat) :
    Fintype (BelowNode T m) := by
  have hfin : Set.Finite {x : T | LevelTree.lev x < m} :=
    (levelLe_finite (T := T) m).subset (by
      intro x hx
      exact Nat.le_of_lt hx)
  exact hfin.fintype

/-- One-level shape words whose terminal target level lies below m. -/
abbrev AMBelow (H : SMTree S) (n m : Nat) :=
  {g : AM H n 1 // g.topLevel H < m}

noncomputable def amBelowCode
    (H : SMTree S) (n m : Nat) :
    AMBelow H n m → (InitialNode T n → BelowNode T m) :=
  fun g x => ⟨g.1.representative H x.1,
    lt_of_le_of_lt
      (g.1.level_le_topLevel H x.1 x.2) g.2⟩

theorem amBelowCode_injective
    (H : SMTree S) (n m : Nat) :
    Function.Injective (H.amBelowCode n m) := by
  intro g h hcode
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hxcode :=
    congrArg Subtype.val (congrFun hcode x)
  have hgtop := g.1.representative_top H
  have hhtop := h.1.representative_top H
  have hgval := congrArg Subtype.val hgtop
  have hhval := congrArg Subtype.val hhtop
  change (g.1.representative H).restrictLe H n = g.1.1.1 at hgval
  change (h.1.representative H).restrictLe H n = h.1.1.1 at hhval
  calc
    g.1.1.1 x = g.1.representative H x.1 :=
      (congrFun hgval x).symm
    _ = h.1.representative H x.1 := hxcode
    _ = h.1.1.1 x := congrFun hhval x

noncomputable instance amBelowFintype
    (H : SMTree S) (n m : Nat) :
    Fintype (AMBelow H n m) := by
  classical
  letI : Fintype (InitialNode T n) := initialNodeFintype T n
  letI : Fintype (BelowNode T m) := belowNodeFintype T m
  letI : DecidableEq (InitialNode T n) := Classical.decEq _
  letI : Fintype (InitialNode T n → BelowNode T m) := inferInstance
  exact Fintype.ofInjective
    (H.amBelowCode n m)
    (H.amBelowCode_injective n m)


end SMTree
end SuccessorTree

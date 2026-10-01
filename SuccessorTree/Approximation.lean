import SuccessorTree.Canonical
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Finite approximations to M-maps

An approximation is stored extensionally on a finite bounded part of the tree;
existence of a full realizing map in M is a proposition.  This avoids
artificially distinguishing different full extensions of the same paper
approximation.
-/

namespace SuccessorTree

variable {T : Type u} [PartialOrder T] [LevelTree T]

/-- Nodes through level m. -/
def BoundedNode (T : Type u) [PartialOrder T] [LevelTree T] (m : Nat) :=
  {a : T // LevelTree.lev a ≤ m}

namespace BoundedNode

theorem set_finite :
    ∀ m : Nat, Set.Finite {a : T | LevelTree.lev a ≤ m} := by
  intro m
  induction m with
  | zero =>
      apply (LevelTree.level_finite 0).subset
      intro a ha
      change LevelTree.lev a ≤ 0 at ha
      have hzero : LevelTree.lev a = 0 := by omega
      exact hzero
  | succ m ih =>
      apply (ih.union (LevelTree.level_finite (m + 1))).subset
      intro a ha
      change LevelTree.lev a ≤ m + 1 at ha
      by_cases hle : LevelTree.lev a ≤ m
      · exact Or.inl hle
      · have heq : LevelTree.lev a = m + 1 := by omega
        exact Or.inr heq

noncomputable instance fintype (m : Nat) : Fintype (BoundedNode T m) :=
  (set_finite (T := T) m).fintype

end BoundedNode

namespace ShapeMap

variable {Label : Type v} {S : STree T Label}

/-- Paper notation M_n: the full map fixes every source level below n. -/
def FixesBelow (F : ShapeMap S) (n : Nat) : Prop :=
  ∀ a : T, LevelTree.lev a < n → F a = a

theorem id_fixesBelow (n : Nat) :
    (ShapeMap.id S).FixesBelow n := by
  intro a ha
  rfl

theorem FixesBelow.comp {F G : ShapeMap S} {n : Nat}
    (hF : F.FixesBelow n) (hG : G.FixesBelow n) :
    (F.comp G).FixesBelow n := by
  intro a ha
  simp [hF a ha, hG a ha]

end ShapeMap

namespace SMTree

variable {Label : Type v} {S : STree T Label}
variable (H : SMTree S)

/-- A function on T(<=top) which is the restriction of some member of M_n. -/
def RealizesApprox (n top : Nat) (f : BoundedNode T top → T) : Prop :=
  ∃ F : ShapeMap S,
    F ∈ H.M ∧
    F.FixesBelow n ∧
    ∀ x : BoundedNode T top, F x.1 = f x

/-- Paper finite approximations with n frozen source levels and source domain
through level top.  For k=1 use top=n; for k=2 use top=n+1. -/
def Approx (n top : Nat) :=
  {f : BoundedNode T top → T // H.RealizesApprox n top f}

namespace Approx

instance : CoeFun (H.Approx n top) (fun _ => BoundedNode T top → T) :=
  ⟨fun g => g.1⟩

@[ext] theorem ext {g h : H.Approx n top}
    (heq : ∀ x, g x = h x) : g = h := by
  apply Subtype.ext
  funext x
  exact heq x

noncomputable def realizer (g : H.Approx n top) : ShapeMap S :=
  Classical.choose g.2

theorem realizer_mem (g : H.Approx n top) :
    Approx.realizer H g ∈ H.M :=
  (Classical.choose_spec g.2).1

theorem realizer_fixesBelow (g : H.Approx n top) :
    (Approx.realizer H g).FixesBelow n :=
  (Classical.choose_spec g.2).2.1

theorem realizer_apply (g : H.Approx n top) (x : BoundedNode T top) :
    Approx.realizer H g x.1 = g x :=
  (Classical.choose_spec g.2).2.2 x

noncomputable def ofShapeMap
    (F : ShapeMap S) (hmem : F ∈ H.M) (hfix : F.FixesBelow n) :
    H.Approx n top :=
  ⟨fun x => F x.1, ⟨F, hmem, hfix, fun _ => rfl⟩⟩

@[simp] theorem ofShapeMap_apply
    (F : ShapeMap S) (hmem : F ∈ H.M) (hfix : F.FixesBelow n)
    (x : BoundedNode T top) :
    Approx.ofShapeMap H F hmem hfix x = F x.1 := rfl

/-- Restrict an approximation to a smaller bounded source. -/
noncomputable def restrict
    (g : H.Approx n top) (small : Nat) (hsmall : small ≤ top) :
    H.Approx n small :=
  ⟨fun x => g ⟨x.1, x.2.trans hsmall⟩,
    ⟨Approx.realizer H g,
      Approx.realizer_mem H g,
      Approx.realizer_fixesBelow H g, by
        intro x
        exact Approx.realizer_apply H g ⟨x.1, x.2.trans hsmall⟩⟩⟩

end Approx

/-- A one-step letter in the paper's finite Hales--Jewett alphabet. -/
def RealizesLetter (n : Nat)
    (f : BoundedNode T n → BoundedNode T (n + 1)) : Prop :=
  ∃ F : ShapeMap S,
    F ∈ H.M ∧
    F.FixesBelow n ∧
    H.levelMap F n = n + 1 ∧
    ∀ x : BoundedNode T n, F x.1 = (f x).1

def Letter (n : Nat) :=
  {f : BoundedNode T n → BoundedNode T (n + 1) // H.RealizesLetter n f}

namespace Letter

instance : CoeFun (H.Letter n)
    (fun _ => BoundedNode T n → BoundedNode T (n + 1)) :=
  ⟨fun e => e.1⟩

noncomputable instance fintype : Fintype (H.Letter n) := by
  classical
  letI : Fintype (BoundedNode T n) := BoundedNode.fintype n
  letI : Fintype (BoundedNode T (n + 1)) := BoundedNode.fintype (n + 1)
  exact Fintype.ofFinite _

noncomputable def realizer (e : H.Letter n) : ShapeMap S :=
  Classical.choose e.2

theorem realizer_mem (e : H.Letter n) :
    Letter.realizer H e ∈ H.M :=
  (Classical.choose_spec e.2).1

theorem realizer_fixesBelow (e : H.Letter n) :
    (Letter.realizer H e).FixesBelow n :=
  (Classical.choose_spec e.2).2.1

theorem realizer_levelMap (e : H.Letter n) :
    H.levelMap (Letter.realizer H e) n = n + 1 :=
  (Classical.choose_spec e.2).2.2.1

theorem realizer_apply (e : H.Letter n) (x : BoundedNode T n) :
    Letter.realizer H e x.1 = (e x).1 :=
  (Classical.choose_spec e.2).2.2.2 x

/-- Forget the output bound and view a letter as a one-level approximation. -/
noncomputable def toApprox (e : H.Letter n) : H.Approx n n :=
  ⟨fun x => (e x).1,
    ⟨Letter.realizer H e,
      Letter.realizer_mem H e,
      Letter.realizer_fixesBelow H e,
      fun x => Letter.realizer_apply H e x⟩⟩

@[simp] theorem toApprox_apply (e : H.Letter n) (x : BoundedNode T n) :
    Letter.toApprox H e x = (e x).1 := rfl

end Letter

/-- Identity one-level approximation. -/
noncomputable def idApprox (n : Nat) : H.Approx n n :=
  Approx.ofShapeMap H (ShapeMap.id S) H.id_mem
    (ShapeMap.id_fixesBelow n)

end SMTree

end SuccessorTree

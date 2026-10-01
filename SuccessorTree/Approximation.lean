import SuccessorTree.Monoid
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Finite admissible approximations

The paper writes AM for finite restrictions of members of the monoid M.
This file gives those objects an extensional Lean representation.

An approximation with source cut n and target cut m is an actual map on the
finite initial segment T(<=n), with values in T(<=m), whose top source level
lands exactly on m and which extends to a member of M.  The global extension
is a proof of admissibility, not part of the extensional data; consequently
the fixed-cut approximation types are finite.
-/

namespace SuccessorTree

open LevelTree

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Nodes on the first n+1 levels of the tree. -/
def InitialSegment (T : Type u) [PartialOrder T] [LevelTree T] (n : Nat) :=
  {a : T // LevelTree.lev a <= n}

namespace InitialSegment

theorem carrier_finite :
    forall n : Nat, Set.Finite {a : T | LevelTree.lev a <= n} := by
  intro n
  induction n with
  | zero =>
      apply (LevelTree.level_finite 0).subset
      intro a ha
      simpa using ha
  | succ n ih =>
      have hset :
          {a : T | LevelTree.lev a <= n + 1} =
            {a : T | LevelTree.lev a <= n} union
              {a : T | LevelTree.lev a = n + 1} := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_union]
        omega
      rw [hset]
      exact ih.union (LevelTree.level_finite (n + 1))

noncomputable instance fintype (n : Nat) : Fintype (InitialSegment T n) :=
  Set.Finite.fintype (carrier_finite (T := T) n)

@[simp] theorem coe_level_le (a : InitialSegment T n) :
    LevelTree.lev a.1 <= n :=
  a.2

/-- Inclusion of a smaller initial segment into a larger one. -/
def castLE {n m : Nat} (h : n <= m) :
    InitialSegment T n -> InitialSegment T m :=
  fun a => ⟨a.1, a.2.trans h⟩

@[simp] theorem castLE_val {n m : Nat} (h : n <= m)
    (a : InitialSegment T n) :
    (castLE h a).1 = a.1 := rfl

end InitialSegment

/-- Extensional agreement of two global maps through a source level. -/
def ShapeMap.AgreesThrough (F G : ShapeMap S) (n : Nat) : Prop :=
  forall a : T, LevelTree.lev a <= n -> F a = G a

namespace ShapeMap

theorem agreesThrough_refl (F : ShapeMap S) (n : Nat) :
    F.AgreesThrough F n := by
  intro a ha
  rfl

theorem agreesThrough_symm {F G : ShapeMap S} {n : Nat}
    (h : F.AgreesThrough G n) :
    G.AgreesThrough F n := by
  intro a ha
  exact (h a ha).symm

theorem agreesThrough_trans {F G K : ShapeMap S} {n : Nat}
    (hFG : F.AgreesThrough G n) (hGK : G.AgreesThrough K n) :
    F.AgreesThrough K n := by
  intro a ha
  exact (hFG a ha).trans (hGK a ha)

theorem agreesThrough_mono {F G : ShapeMap S} {n m : Nat}
    (h : F.AgreesThrough G n) (hmn : m <= n) :
    F.AgreesThrough G m := by
  intro a ha
  exact h a (ha.trans hmn)

end ShapeMap

/-- A finite admissible map from T(<=src) whose top source level lands
exactly on target level dst. -/
structure Approximation (H : SMTree S) (src dst : Nat) where
  toFun : InitialSegment T src -> InitialSegment T dst
  top_level :
    forall a : InitialSegment T src,
      LevelTree.lev a.1 = src ->
        LevelTree.lev (toFun a).1 = dst
  extendible :
    exists F : ShapeMap S,
      F ∈ H.M /\
      forall a : InitialSegment T src, F a.1 = (toFun a).1

namespace Approximation

variable {H : SMTree S}

instance : CoeFun (Approximation H src dst)
    (fun _ => InitialSegment T src -> InitialSegment T dst) :=
  ⟨Approximation.toFun⟩

@[ext] theorem ext {A B : Approximation H src dst}
    (h : forall a, (A a).1 = (B a).1) :
    A = B := by
  cases A with
  | mk f hf he =>
      cases B with
      | mk g hg ge =>
          have hfg : f = g := by
            funext a
            exact Subtype.ext (h a)
          subst g
          rfl

theorem toFun_injective :
    Function.Injective
      (fun A : Approximation H src dst => A.toFun) := by
  intro A B h
  apply Approximation.ext
  intro a
  exact congrArg Subtype.val (congrFun h a)

noncomputable instance fintype :
    Fintype (Approximation H src dst) :=
  Fintype.ofInjective
    (fun A : Approximation H src dst => A.toFun)
    toFun_injective

/-- Choose a global monoid member witnessing admissibility.  Its tail is
irrelevant to the extensional approximation. -/
noncomputable def someExtension (A : Approximation H src dst) :
    ShapeMap S :=
  Classical.choose A.extendible

theorem someExtension_mem (A : Approximation H src dst) :
    A.someExtension ∈ H.M :=
  (Classical.choose_spec A.extendible).1

theorem someExtension_apply (A : Approximation H src dst)
    (a : InitialSegment T src) :
    A.someExtension a.1 = (A a).1 :=
  (Classical.choose_spec A.extendible).2 a

theorem someExtension_agrees (A : Approximation H src dst) :
    forall a : T, LevelTree.lev a <= src ->
      A.someExtension a =
        (A ⟨a, by assumption⟩).1 := by
  intro a ha
  exact A.someExtension_apply ⟨a, ha⟩

/-- Restriction of a monoid member to a finite source cut. -/
noncomputable def ofMember
    (F : ShapeMap S) (hF : F ∈ H.M) (src : Nat) :
    Approximation H src (H.levelMap F src) where
  toFun := fun a =>
    ⟨F a.1, by
      calc
        LevelTree.lev (F a.1) =
            H.levelMap F (LevelTree.lev a.1) :=
          (H.levelMap_eq F (a := a.1)).symm
        _ <= H.levelMap F src :=
          (H.levelMap_strictMono F).monotone a.2⟩
  top_level := by
    intro a ha
    calc
      LevelTree.lev (F a.1) =
          H.levelMap F (LevelTree.lev a.1) :=
        (H.levelMap_eq F (a := a.1)).symm
      _ = H.levelMap F src := by rw [ha]
  extendible := ⟨F, hF, by intro a; rfl⟩

@[simp] theorem ofMember_apply
    (F : ShapeMap S) (hF : F ∈ H.M) (src : Nat)
    (a : InitialSegment T src) :
    ((ofMember F hF src) a).1 = F a.1 := rfl

/-- Identity finite approximation. -/
def id (H : SMTree S) (n : Nat) : Approximation H n n where
  toFun := fun a => ⟨a.1, a.2⟩
  top_level := by
    intro a ha
    exact ha
  extendible := by
    refine ⟨ShapeMap.id S, H.id_mem, ?_⟩
    intro a
    rfl

@[simp] theorem id_apply (H : SMTree S) (n : Nat)
    (a : InitialSegment T n) :
    ((id H n) a).1 = a.1 := rfl

/-- Composition of finite approximations.  The extensional map is ordinary
composition; admissibility follows by composing chosen monoid extensions. -/
noncomputable def comp
    (B : Approximation H mid dst)
    (A : Approximation H src mid) :
    Approximation H src dst where
  toFun := fun a => B (A a)
  top_level := by
    intro a ha
    apply B.top_level
    exact A.top_level a ha
  extendible := by
    let FA := A.someExtension
    let FB := B.someExtension
    refine ⟨FB.comp FA,
      H.comp_mem B.someExtension_mem A.someExtension_mem, ?_⟩
    intro a
    change FB (FA a.1) = (B (A a)).1
    rw [show FA a.1 = (A a).1 by
      exact A.someExtension_apply a]
    exact B.someExtension_apply (A a)

@[simp] theorem comp_apply
    (B : Approximation H mid dst)
    (A : Approximation H src mid)
    (a : InitialSegment T src) :
    ((B.comp A) a).1 = (B (A a)).1 := rfl

/-- An approximation fixes every node strictly below the distinguished source
level.  This is the superscript n condition in AM^n_k. -/
def FixesBelow (A : Approximation H src dst) (n : Nat) : Prop :=
  forall a : InitialSegment T src,
    LevelTree.lev a.1 < n -> (A a).1 = a.1

theorem id_fixesBelow (H : SMTree S) (n : Nat) :
    (id H n).FixesBelow n := by
  intro a ha
  rfl

/-- The finite alphabet Gamma = AM^n_1(n+1) used in the first pigeonhole
lemma: admissible one-step maps, identity below level n. -/
def OneStep (H : SMTree S) (n : Nat) :=
  {A : Approximation H n (n + 1) // A.FixesBelow n}

noncomputable instance oneStepFintype :
    Fintype (OneStep H n) :=
  Fintype.ofFinite _

theorem OneStep.fixesBelow (e : OneStep H n) :
    e.1.FixesBelow n :=
  e.2

/-- A one-step letter viewed as its underlying finite approximation. -/
def OneStep.toApprox (e : OneStep H n) :
    Approximation H n (n + 1) :=
  e.1

@[simp] theorem OneStep.toApprox_apply (e : OneStep H n)
    (a : InitialSegment T n) :
    ((e.toApprox) a).1 = (e.1 a).1 := rfl

end Approximation

end SuccessorTree

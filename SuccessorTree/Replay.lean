import SuccessorTree.Canonical
import SuccessorTree.Pigeonhole
import Mathlib.Tactic

/-!
# Replay construction for the one-dimensional pigeonhole lemma

This file follows Section 3.1 of the successor-tree paper.  It first
formalizes the recursively defined finite maps g_w.
-/

namespace SuccessorTree

open LevelTree

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable {H : SMTree S}

namespace SMTree

/-- Level maps respect composition. -/
theorem levelMap_comp (H : SMTree S) (F G : ShapeMap S) (n : Nat) :
    H.levelMap (F.comp G) n =
      H.levelMap F (H.levelMap G n) := by
  obtain ⟨a, ha⟩ := H.level_nonempty n
  have hG :
      LevelTree.lev (G a) = H.levelMap G n := by
    simpa [ha] using (H.levelMap_eq G (a := a)).symm
  calc
    H.levelMap (F.comp G) n =
        LevelTree.lev (F (G a)) := by
      simpa [ha] using H.levelMap_eq (F.comp G) (a := a)
    _ = H.levelMap F (LevelTree.lev (G a)) :=
      (H.levelMap_eq F (a := G a)).symm
    _ = H.levelMap F (H.levelMap G n) := by rw [hG]

end SMTree

namespace Approximation

/-- Restrict a specified monoid member to a specified target cut, when its
level map is known at the source cut. -/
noncomputable def ofMemberAt
    (F : ShapeMap S) (hF : F ∈ H.M)
    (src dst : Nat)
    (hlevel : H.levelMap F src = dst) :
    Approximation H src dst where
  toFun := fun a =>
    ⟨F a.1, by
      calc
        LevelTree.lev (F a.1) =
            H.levelMap F (LevelTree.lev a.1) :=
          (H.levelMap_eq F (a := a.1)).symm
        _ ≤ H.levelMap F src :=
          (H.levelMap_strictMono F).monotone a.2
        _ = dst := hlevel⟩
  top_level := by
    intro a ha
    calc
      LevelTree.lev (F a.1) =
          H.levelMap F (LevelTree.lev a.1) :=
        (H.levelMap_eq F (a := a.1)).symm
      _ = H.levelMap F src := by rw [ha]
      _ = dst := hlevel
  extendible := ⟨F, hF, by intro a; rfl⟩

@[simp] theorem ofMemberAt_apply
    (F : ShapeMap S) (hF : F ∈ H.M)
    (src dst : Nat)
    (hlevel : H.levelMap F src = dst)
    (a : InitialSegment T src) :
    ((ofMemberAt F hF src dst hlevel) a).1 = F a.1 := rfl

/-- A canonical extension advances exactly one target level at the next source
level. -/
theorem canonicalExtension_nextLevel
    (A : Approximation H src dst) :
    H.levelMap A.canonicalExtension (src + 1) = dst + 1 := by
  have hbase :
      dst ≤ H.levelMap A.canonicalExtension src := by
    rw [A.canonicalExtension_topLevel]
  have hs :=
    H.levelMap_succ_of_tailFull
      A.canonicalExtension dst src
      A.canonicalExtension_tailFull hbase
  rw [A.canonicalExtension_topLevel] at hs
  exact hs

/-- If the finite approximation is identity below fixed, so is its canonical
extension. -/
theorem canonicalExtension_eq_id_below
    (A : Approximation H src dst)
    (hfix : A.FixesBelow fixed)
    (hfixed : fixed ≤ src)
    {a : T} (ha : LevelTree.lev a < fixed) :
    A.canonicalExtension a = a := by
  have hasrc : LevelTree.lev a ≤ src :=
    (Nat.le_of_lt ha).trans hfixed
  let x : InitialSegment T src := ⟨a, hasrc⟩
  calc
    A.canonicalExtension a = (A x).1 :=
      A.canonicalExtension_apply x
    _ = a := hfix x ha

/-- One moving level with arbitrary target cut: the extensional version of
AM^n_1. -/
structure MovingOne (H : SMTree S) (n : Nat) where
  dst : Nat
  approx : Approximation H n dst
  fixesBelow : approx.FixesBelow n

namespace MovingOne

/-- The empty word gives the identity approximation. -/
def identity (H : SMTree S) (n : Nat) : MovingOne H n where
  dst := n
  approx := Approximation.id H n
  fixesBelow := Approximation.id_fixesBelow H n

/-- A one-step Hales--Jewett alphabet letter as a general one-moving-level
approximation. -/
def ofLetter (e : OneStep H n) : MovingOne H n where
  dst := n + 1
  approx := e.toApprox
  fixesBelow := e.fixesBelow

/-- Append one alphabet letter to a word state. -/
noncomputable def step
    (X : MovingOne H n) (e : OneStep H n) :
    MovingOne H n := by
  let F := X.approx.canonicalExtension
  have hF : F ∈ H.M := X.approx.canonicalExtension_mem
  have hnext :
      H.levelMap F (n + 1) = X.dst + 1 :=
    X.approx.canonicalExtension_nextLevel
  let B : Approximation H (n + 1) (X.dst + 1) :=
    Approximation.ofMemberAt F hF (n + 1) (X.dst + 1) hnext
  let C : Approximation H n (X.dst + 1) :=
    B.comp e.toApprox
  refine ⟨X.dst + 1, C, ?_⟩
  intro a ha
  change (B (e.toApprox a)).1 = a.1
  change F (e.toApprox a).1 = a.1
  have he : (e.toApprox a).1 = a.1 :=
    e.fixesBelow a ha
  rw [he]
  exact X.approx.canonicalExtension_eq_id_below
    X.fixesBelow le_rfl ha

@[simp] theorem step_dst
    (X : MovingOne H n) (e : OneStep H n) :
    (X.step e).dst = X.dst + 1 := by
  rfl

/-- Run a word from an existing one-moving-level state. -/
noncomputable def run
    (X : MovingOne H n) : List (OneStep H n) → MovingOne H n
  | [] => X
  | e :: w => run (X.step e) w

@[simp] theorem run_nil (X : MovingOne H n) :
    X.run [] = X := rfl

@[simp] theorem run_cons
    (X : MovingOne H n) (e : OneStep H n) (w : List (OneStep H n)) :
    X.run (e :: w) = (X.step e).run w := rfl

theorem run_append
    (X : MovingOne H n)
    (u v : List (OneStep H n)) :
    X.run (u ++ v) = (X.run u).run v := by
  induction u generalizing X with
  | nil => rfl
  | cons e u ih =>
      simp only [List.cons_append, run_cons]
      exact ih (X.step e)

theorem run_dst
    (X : MovingOne H n) :
    ∀ w : List (OneStep H n),
      (X.run w).dst = X.dst + w.length := by
  intro w
  induction w generalizing X with
  | nil => simp
  | cons e w ih =>
      rw [run_cons, ih]
      simp
      omega

/-- The paper's recursively defined g_w. -/
noncomputable def wordApprox
    (H : SMTree S) (n : Nat)
    (w : List (OneStep H n)) : MovingOne H n :=
  (identity H n).run w

@[simp] theorem wordApprox_dst
    (H : SMTree S) (n : Nat)
    (w : List (OneStep H n)) :
    (wordApprox H n w).dst = n + w.length := by
  unfold wordApprox
  rw [run_dst]
  rfl

theorem wordApprox_append
    (H : SMTree S) (n : Nat)
    (u v : List (OneStep H n)) :
    wordApprox H n (u ++ v) =
      (wordApprox H n u).run v := by
  exact run_append (identity H n) u v

theorem wordApprox_snoc
    (H : SMTree S) (n : Nat)
    (u : List (OneStep H n)) (e : OneStep H n) :
    wordApprox H n (u ++ [e]) =
      (wordApprox H n u).step e := by
  rw [wordApprox_append]
  rfl

end MovingOne

end Approximation

end SuccessorTree

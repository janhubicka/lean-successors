import SuccessorTree.FatTree.Amalgamation
import SuccessorTree.ShapeAction
import SuccessorTree.FatTree.Sequencing
import RamseySpace.Basic

/-!
# The abstract approximation system of fat trees

This file packages the literal fat-tree sequencing lemmas as Todorčević's
typed `ApproximationSystem`.  A level-`n` approximation is a finite fat
tree whose height is exactly `n`.

Closedness and A.2--A.4 are deliberately kept in later files.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- Finite fat trees of exactly height `n`. -/
def ExactApprox (n : Nat) :=
  {x : FiniteFatTree H // x.height = n}

/-- The nth typed approximation of an infinite fat tree. -/
def exactApprox (n : Nat) (U : FatTree H) : ExactApprox H n :=
  ⟨U.initialSegment H n, rfl⟩

/-- The unique typed approximation of height zero. -/
def emptyExactApprox : ExactApprox H 0 :=
  ⟨FatTree.empty H, rfl⟩

/-- The identity infinite fat tree.  Its cut is the identity on
levels and every row is the identity one-level finite word. -/
noncomputable def identityFatTree : FatTree H where
  cut := fun i => i
  cut_zero := rfl
  row := fun i => AM.id1 H i
  row_cut := by
    intro i
    have h :
        (AM.id1 H i).rowEndLevel H = i := by
      simpa [AM.rowEndLevel, AM.topLevel] using
        AM.id1_topLevel H i
    omega

@[simp] theorem identityFatTree_cut (i : Nat) :
    (identityFatTree H).cut i = i := rfl

/-- Complete a finite fat tree by attaching the identity tail at its terminal
cut. -/
noncomputable def completeFinite (x : FiniteFatTree H) : FatTree H :=
  splice H x (identityFatTree H) x.terminalCut (by rfl)

/-- The prescribed finite tree is literally the corresponding initial
segment of its completion. -/
theorem completeFinite_initialSegment (x : FiniteFatTree H) :
    (completeFinite H x).initialSegment H x.height = x := by
  exact splice_initialSegment H x (identityFatTree H)
    x.terminalCut (by rfl)

/-- Complete an exact-height approximation. -/
noncomputable def completeExact {n : Nat} (x : ExactApprox H n) :
    FatTree H :=
  completeFinite H x.1

theorem exactApprox_completeExact {n : Nat} (x : ExactApprox H n) :
    exactApprox H n (completeExact H x) = x := by
  rcases x with ⟨x, hx⟩
  cases hx
  apply Subtype.ext
  exact completeFinite_initialSegment H x

/-- Literal A1(1) in typed approximation form. -/
theorem exactApprox_zero (U : FatTree H) :
    exactApprox H 0 U = emptyExactApprox H := by
  apply Subtype.ext
  exact a1_one H U

/-- Separation in the typed approximation language. -/
theorem exactApprox_separated {U V : FatTree H}
    (h : ∀ n : Nat, exactApprox H n U = exactApprox H n V) :
    U = V := by
  apply ext_of_initialSegments_eq H
  intro n
  exact congrArg Subtype.val (h n)

/-- Coherence in the typed approximation language. -/
theorem exactApprox_coherent
    {U V : FatTree H} {n : Nat}
    (h : exactApprox H n U = exactApprox H n V)
    (m : Nat) (hm : m < n) :
    exactApprox H m U = exactApprox H m V := by
  apply Subtype.ext
  have hn :
      U.initialSegment H n = V.initialSegment H n :=
    congrArg Subtype.val h
  exact (a1_three H hn).2 m hm

/-- The A1 data for infinite fat trees.  Surjectivity of `approx` is filled
in after the completion lemma below; keeping it as a theorem makes the
construction boundary explicit. -/
def approximationSystemOfCompletion
    (complete : ∀ {n : Nat}, ExactApprox H n → FatTree H)
    (hcomplete :
      ∀ {n : Nat} (x : ExactApprox H n),
        exactApprox H n (complete x) = x) :
    RamseySpace.ApproximationSystem where
  Point := FatTree H
  Approx := ExactApprox H
  le := FatTree.Reduces H
  le_refl := FatTree.reduces_refl H
  le_trans := fun hXY hYZ => FatTree.reduces_trans H hXY hYZ
  approx := exactApprox H
  approx_surjective := by
    intro n x
    exact ⟨complete x, hcomplete x⟩
  empty := emptyExactApprox H
  approx_zero := exactApprox_zero H
  separated := by
    intro U V h
    exact exactApprox_separated H h
  coherent := by
    intro U V n h m hm
    exact exactApprox_coherent H h m hm


/-- The concrete Todorčević A1 approximation system of fat trees. -/
noncomputable def approximationSystem :
    RamseySpace.ApproximationSystem :=
  approximationSystemOfCompletion H
    (fun x => completeExact H x)
    (fun x => exactApprox_completeExact H x)

end FatTree

end SMTree
end SuccessorTree

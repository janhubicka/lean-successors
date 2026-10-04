import SuccessorTree.FatTree.Basic

/-!
# Todorcevic A1 for fat trees

This file proves the sequencing axioms for the finite initial segments of an
infinite fat tree.  It is deliberately independent of reduction, amalgamation,
and the optional embedding-space EA assumption.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FiniteFatTree

variable (H : SMTree S)

/-- Equality of finite fat trees transports a row at the corresponding
source index. -/
theorem row_heq_of_eq {U V : FiniteFatTree H}
    (h : U = V) (i : Fin V.height) :
    HEq
      (U.row
        (Fin.cast
          (congrArg (fun Z : FiniteFatTree H => Z.height) h).symm i))
      (V.row i) := by
  cases h
  rfl

/-- Taking a finite initial segment commutes with equality of the ambient
finite fat trees. -/
theorem initialSegment_congr {U V : FiniteFatTree H}
    (hUV : U = V) (k : Nat)
    (hU : k ≤ U.height) (hV : k ≤ V.height) :
    U.initialSegment H k hU = V.initialSegment H k hV := by
  cases hUV
  rfl

end FiniteFatTree

namespace FatTree

variable (H : SMTree S)

/-- Pointwise equality of cuts and rows determines an infinite fat tree. -/
theorem ext_pointwise {U V : FatTree H}
    (hcut : ∀ i : Nat, U.cut i = V.cut i)
    (hrow : ∀ i : Nat, HEq (U.row i) (V.row i)) :
    U = V := by
  cases U with
  | mk uc uz ur urc =>
      cases V with
      | mk vc vz vr vrc =>
          dsimp at hcut hrow
          have hc : uc = vc := funext hcut
          subst vc
          have hr : ur = vr := by
            funext i
            exact eq_of_heq (hrow i)
          subst vr
          rfl

/-- The unique empty finite fat tree. -/
def empty : FiniteFatTree H where
  height := 0
  cut := fun _ => 0
  cut_zero := rfl
  row := fun i => Fin.elim0 i
  row_cut := fun i => Fin.elim0 i

/-- A1(1): every zeroth approximation is the empty finite fat tree. -/
theorem a1_one (U : FatTree H) :
    U.initialSegment H 0 = empty H := by
  refine FiniteFatTree.ext_pointwise H
    (U := U.initialSegment H 0) (V := empty H) rfl ?_ ?_
  · intro i
    have hi1 : i.1 < 1 := by
      simpa only [FatTree.initialSegment] using i.2
    have hi : i.1 = 0 := by omega
    change U.cut i.1 = 0
    rw [hi, U.cut_zero]
  · intro i
    exact Fin.elim0 i

/-- Taking the first `k` rows of the first `n` rows gives the first
`k` rows of the original infinite tree. -/
theorem initialSegment_initialSegment
    (U : FatTree H) (n k : Nat) (hk : k ≤ n) :
    (U.initialSegment H n).initialSegment H k hk =
      U.initialSegment H k := by
  refine FiniteFatTree.ext_pointwise H
    (U := (U.initialSegment H n).initialSegment H k hk)
    (V := U.initialSegment H k) rfl ?_ ?_
  · intro i
    rfl
  · intro i
    exact HEq.rfl

/-- Equality of all finite approximations determines the infinite fat tree. -/
theorem ext_of_initialSegments_eq {U V : FatTree H}
    (h : ∀ n : Nat,
      U.initialSegment H n = V.initialSegment H n) :
    U = V := by
  apply ext_pointwise H
  · intro i
    have ht := congrArg FiniteFatTree.terminalCut (h i)
    simpa using ht
  · intro i
    let j : Fin ((V.initialSegment H (i + 1)).height) :=
      ⟨i, by
        change i < i + 1
        exact Nat.lt_succ_self i⟩
    have hr :=
      FiniteFatTree.row_heq_of_eq H (h (i + 1)) j
    change HEq (U.row i) (V.row i) at hr
    exact hr

/-- A1(2): unequal infinite fat trees are separated by a finite
approximation. -/
theorem a1_two {U V : FatTree H} (hne : U ≠ V) :
    ∃ n : Nat,
      U.initialSegment H n ≠ V.initialSegment H n := by
  classical
  by_contra hno
  apply hne
  apply ext_of_initialSegments_eq H
  intro n
  by_contra hn
  exact hno ⟨n, hn⟩

/-- Equality of finite approximations forces equality of their lengths. -/
theorem initialSegment_height_eq
    {U V : FatTree H} {n m : Nat}
    (h : U.initialSegment H n = V.initialSegment H m) :
    n = m := by
  have hh := congrArg FiniteFatTree.height h
  change n = m at hh
  exact hh

/-- A1(3): equal finite approximations have the same length and all previous
approximations agree. -/
theorem a1_three
    {U V : FatTree H} {n m : Nat}
    (h : U.initialSegment H n = V.initialSegment H m) :
    n = m ∧
      ∀ k : Nat, k < n →
        U.initialSegment H k = V.initialSegment H k := by
  have hnm : n = m :=
    initialSegment_height_eq H h
  subst m
  refine ⟨rfl, ?_⟩
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt hk
  calc
    U.initialSegment H k =
        (U.initialSegment H n).initialSegment H k hkn :=
      (U.initialSegment_initialSegment H n k hkn).symm
    _ = (V.initialSegment H n).initialSegment H k hkn :=
      FiniteFatTree.initialSegment_congr H h k hkn hkn
    _ = V.initialSegment H k :=
      V.initialSegment_initialSegment H n k hkn

end FatTree

end SMTree
end SuccessorTree

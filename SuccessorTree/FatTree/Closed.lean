import SuccessorTree.FatTree.ApproximationSystem
import RamseySpace.Closed

/-!
# Metric closedness of the fat-tree approximation space

A coherent approximation code is realized by taking the ith row from any
realizer of the code through level i+1.  Prefix realizability guarantees that
these choices agree on overlaps.

This file is independent of A4 and of the optional embedding-space EA axiom.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

private theorem realized_prefix_eq
    (c : (approximationSystem H).ApproximationCode)
    (hpref :
      ∀ N, (approximationSystem H).PrefixRealizable c N)
    (N M k : Nat) (hkN : k ≤ N) (hkM : k ≤ M) :
    (Classical.choose (hpref N)).initialSegment H k =
      (Classical.choose (hpref M)).initialSegment H k := by
  have hN :=
    Classical.choose_spec (hpref N) k hkN
  have hM :=
    Classical.choose_spec (hpref M) k hkM
  exact congrArg Subtype.val (hN.trans hM.symm)

/-- The approximation image of infinite fat trees is closed in the
first-difference/product topology. -/
theorem isMetricallyClosed :
    (approximationSystem H).IsMetricallyClosed := by
  classical
  intro c hpref
  let X : Nat → FatTree H :=
    fun N => Classical.choose (hpref N)
  have hX :
      ∀ N n : Nat, n ≤ N →
        exactApprox H n (X N) = c n := by
    intro N n hn
    exact Classical.choose_spec (hpref N) n hn

  let cut : Nat → Nat := fun i => (X (i + 1)).cut i
  let row : (i : Nat) → AM H (cut i) 1 :=
    fun i => (X (i + 1)).row i

  have hcut_overlap (i : Nat) :
      (X (i + 1)).cut (i + 1) =
        (X (i + 2)).cut (i + 1) := by
    have hseg :=
      realized_prefix_eq H c hpref
        (i + 1) (i + 2) (i + 1) (by omega) (by omega)
    have ht :=
      congrArg FiniteFatTree.terminalCut hseg
    rw [FatTree.initialSegment_terminalCut,
        FatTree.initialSegment_terminalCut] at ht
    exact ht

  let U : FatTree H := {
    cut := cut
    cut_zero := by
      dsimp [cut]
      exact (X 1).cut_zero
    row := row
    row_cut := by
      intro i
      dsimp [row, cut]
      calc
        ((X (i + 1)).row i).rowEndLevel H + 1 =
            (X (i + 1)).cut (i + 1) :=
          (X (i + 1)).row_cut i
        _ = (X (i + 2)).cut (i + 1) :=
          hcut_overlap i
  }

  refine ⟨U, ?_⟩
  intro n
  apply Subtype.ext
  have hreal : (X n).initialSegment H n = (c n).1 := by
    exact congrArg Subtype.val (hX n n le_rfl)
  calc
    U.initialSegment H n = (X n).initialSegment H n := by
      apply FiniteFatTree.ext_pointwise H
        (U := U.initialSegment H n)
        (V := (X n).initialSegment H n)
        rfl
      · intro i
        have hiN : i.1 ≤ n := by
          change i.1 < n + 1 at i.2
          omega
        change (X (i.1 + 1)).cut i.1 = (X n).cut i.1
        have hseg :=
          realized_prefix_eq H c hpref
            (i.1 + 1) n i.1 (by omega) hiN
        have ht :=
          congrArg FiniteFatTree.terminalCut hseg
        rw [FatTree.initialSegment_terminalCut,
            FatTree.initialSegment_terminalCut] at ht
        exact ht
      · intro i
        have hiN : i.1 + 1 ≤ n := by
          change i.1 < n at i.2
          omega
        change HEq ((X (i.1 + 1)).row i.1) ((X n).row i.1)
        have hseg :=
          realized_prefix_eq H c hpref
            (i.1 + 1) n (i.1 + 1) le_rfl hiN
        let j : Fin ((X n).initialSegment H (i.1 + 1) |>.height) :=
          ⟨i.1, by
            change i.1 < i.1 + 1
            omega⟩
        have hr :=
          FiniteFatTree.row_heq_of_eq H hseg j
        change
          HEq ((X (i.1 + 1)).row i.1) ((X n).row i.1) at hr
        exact hr
    _ = (c n).1 := hreal

end FatTree
end SMTree
end SuccessorTree

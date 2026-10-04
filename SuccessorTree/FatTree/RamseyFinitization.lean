import SuccessorTree.FatTree.ApproximationSystem
import RamseySpace.Finitization

/-!
# Typed A2 finitization for fat trees

This packages the already verified concrete finite fat-tree order as the
`RamseySpace.Finitization` attached to the typed exact approximations.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

private noncomputable def S0 := approximationSystem H

/-- Forget the level tag of a typed finite approximation.  The level is
recoverable from the height of the underlying finite fat tree. -/
noncomputable def finiteApproxTree :
    (S0 H).FiniteApprox → FiniteFatTree H
  | ⟨_, a⟩ => a.1

theorem finiteApproxTree_injective :
    Function.Injective (finiteApproxTree H) := by
  intro a b hab
  rcases a with ⟨n, ⟨A, hA⟩⟩
  rcases b with ⟨m, ⟨B, hB⟩⟩
  dsimp [finiteApproxTree] at hab
  have hnm : n = m := by
    calc
      n = A.height := hA.symm
      _ = B.height := congrArg FiniteFatTree.height hab
      _ = m := hB
  cases hnm
  cases hab
  rfl

/-- Typed A2 order: forget the level tags and use the concrete finite
fat-tree order. -/
def typedLeFin
    (a b : (S0 H).FiniteApprox) : Prop :=
  FiniteFatTree.LeFin H (finiteApproxTree H a) (finiteApproxTree H b)

/-- A typed initial approximation is literally the corresponding finite
initial segment of the larger underlying finite fat tree. -/
theorem tree_eq_initialSegment_of_isInitial
    {n m : Nat}
    {a : (S0 H).Approx n} {b : (S0 H).Approx m}
    (hab : (S0 H).IsInitial a b) :
    ∃ hnm : n ≤ m,
      a.1 = b.1.initialSegment H n
        (by exact hnm.trans_eq b.2.symm) := by
  change n ≤ m ∧
    ∃ X : FatTree H,
      exactApprox H n X = a ∧ exactApprox H m X = b at hab
  rcases hab with ⟨hnm, X, hXa, hXb⟩
  refine ⟨hnm, ?_⟩
  have ha :
      X.initialSegment H n = a.1 :=
    congrArg Subtype.val hXa
  have hb :
      X.initialSegment H m = b.1 :=
    congrArg Subtype.val hXb
  have hprefix :
      (X.initialSegment H m).initialSegment H n hnm =
        X.initialSegment H n :=
    X.initialSegment_initialSegment H m n hnm
  calc
    a.1 = X.initialSegment H n := ha.symm
    _ = (X.initialSegment H m).initialSegment H n hnm :=
      hprefix.symm
    _ = b.1.initialSegment H n
        (by exact hnm.trans_eq b.2.symm) := by
      exact FiniteFatTree.initialSegment_congr H hb n
        (by
          change n ≤ m
          exact hnm)
        (hnm.trans_eq b.2.symm)

/-- The concrete A2 theorems packaged in Todorčević's typed interface. -/
noncomputable def finitization :
    RamseySpace.Finitization (S0 H) where
  leFin := typedLeFin H
  leFin_refl := by
    intro a
    exact FiniteFatTree.leFin_refl H (finiteApproxTree H a)
  leFin_trans := by
    intro a b c hab hbc
    exact FiniteFatTree.leFin_trans H hab hbc
  lowerFinite := by
    intro b
    classical
    rw [← Set.finite_coe_iff]
    let target :=
      {x : FiniteFatTree H //
        FiniteFatTree.LeFin H x (finiteApproxTree H b)}
    letI : Finite target := by
      rw [show target =
        {x : FiniteFatTree H //
          x ∈ {x : FiniteFatTree H |
            FiniteFatTree.LeFin H x (finiteApproxTree H b)}} by rfl]
      exact (FiniteFatTree.leFin_lower_finite H
        (finiteApproxTree H b)).to_subtype
    let f :
        {a : (S0 H).FiniteApprox // typedLeFin H a b} → target :=
      fun a => ⟨finiteApproxTree H a.1, a.2⟩
    exact Finite.of_injective f (by
      intro a b hab
      apply Subtype.ext
      apply finiteApproxTree_injective H
      exact congrArg Subtype.val hab)
  realizesOrder := by
    intro X Y
    change FatTree.Reduces H X Y ↔
      ∀ n, ∃ m,
        FiniteFatTree.LeFin H
          (X.initialSegment H n)
          (Y.initialSegment H m)
    exact FiniteFatTree.reduces_iff_initialSegment_leFin H X Y
  prefix_leFin := by
    intro n m k a b c hab hbc
    rcases tree_eq_initialSegment_of_isInitial H hab with
      ⟨hnm, ha⟩
    have hbc' :
        FiniteFatTree.LeFin H b.1 c.1 := hbc
    rcases FiniteFatTree.leFin_prefix H hbc' n
        (by simpa [b.2] using hnm) with
      ⟨j, hj, hfin⟩
    have hjk : j ≤ k := hj.trans_eq c.2
    let dTree : FiniteFatTree H :=
      c.1.initialSegment H j hj
    let d : (S0 H).Approx j :=
      ⟨dTree, rfl⟩
    refine ⟨j, d, ?_, ?_⟩
    · refine ⟨hjk, completeExact H c, ?_, exactApprox_completeExact H c⟩
      · apply Subtype.ext
        have hc :
            (completeExact H c).initialSegment H k = c.1 := by
          exact congrArg Subtype.val (exactApprox_completeExact H c)
        have hseg :
            (completeExact H c).initialSegment H j =
              c.1.initialSegment H j hj := by
          have hprefix :=
            (completeExact H c).initialSegment_initialSegment H k j hjk
          calc
            (completeExact H c).initialSegment H j =
                ((completeExact H c).initialSegment H k).initialSegment H j
                  hjk := hprefix.symm
            _ = c.1.initialSegment H j hj := by
              exact FiniteFatTree.initialSegment_congr H hc j _ _
        exact hseg
    · change FiniteFatTree.LeFin H a.1 dTree
      rw [ha]
      exact hfin

end FatTree
end SMTree
end SuccessorTree

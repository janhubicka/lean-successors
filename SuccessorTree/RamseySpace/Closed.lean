import SuccessorTree.ShapeFusion
import RamseySpace.Closed

/-!
# Metric closedness of the shape-preserving map space

Points are M-maps, ordered by right composition, with the finite
approximations already defined in `RamseySpace.Basic`.  A coherent product
code has arbitrarily long realizations.  Choose one realization at each
length.  Consecutive realizations agree on the source levels already fixed,
so M1 gives their pointwise fusion limit.  That limit realizes the whole
code.

This is the closedness paragraph in the optional embedding-Ellentuck proof.
No A3/EA or pigeonhole theorem is used.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- A chosen realization of the first `i+2` coordinates of a metrically
closed code candidate.  The one-level offset makes stage `i` determine
the whole source segment through level `i`. -/
noncomputable def shapeClosedStage
    (H : SMTree S)
    (c : (ramseyApproximationSystem H).ApproximationCode)
    (hpref : ∀ N, (ramseyApproximationSystem H).PrefixRealizable c N)
    (i : Nat) : MMap H :=
  Classical.choose (hpref (i + 1))

theorem shapeClosedStage_spec
    (H : SMTree S)
    (c : (ramseyApproximationSystem H).ApproximationCode)
    (hpref : ∀ N, (ramseyApproximationSystem H).PrefixRealizable c N)
    (i n : Nat) (hn : n ≤ i + 1) :
    ramseyApprox H n (shapeClosedStage H c hpref i) = c n :=
  (Classical.choose_spec (hpref (i + 1))) n hn

/-- Consecutive chosen realizations agree on every node whose source level
has already been exposed. -/
theorem shapeClosedStage_stable
    (H : SMTree S)
    (c : (ramseyApproximationSystem H).ApproximationCode)
    (hpref : ∀ N, (ramseyApproximationSystem H).PrefixRealizable c N) :
    MMap.FusionStable H (shapeClosedStage H c hpref) := by
  intro i x hx
  have hleft :=
    shapeClosedStage_spec H c hpref i (i + 1) le_rfl
  have hright :=
    shapeClosedStage_spec H c hpref (i + 1) (i + 1) (by omega)
  have happ :
      ramseyApprox H (i + 1) (shapeClosedStage H c hpref i) =
        ramseyApprox H (i + 1) (shapeClosedStage H c hpref (i + 1)) :=
    hleft.trans hright.symm
  have hval := congrArg Subtype.val happ
  change
    (shapeClosedStage H c hpref i).restrictLe H i =
      (shapeClosedStage H c hpref (i + 1)).restrictLe H i at hval
  exact congrFun hval ⟨x, hx⟩

/-- The M1 limit of the chosen finite realizations realizes every coordinate
of the coherent approximation code. -/
theorem shapeClosed_limit_realizes
    (H : SMTree S)
    (c : (ramseyApproximationSystem H).ApproximationCode)
    (hpref : ∀ N, (ramseyApproximationSystem H).PrefixRealizable c N) :
    let L := MMap.fusionLimit H (shapeClosedStage H c hpref)
      (shapeClosedStage_stable H c hpref)
    ∀ n, ramseyApprox H n L = c n := by
  intro L n
  cases n with
  | zero =>
      have h0 := shapeClosedStage_spec H c hpref 0 0 (by omega)
      exact h0
  | succ n =>
      have hstage :=
        shapeClosedStage_spec H c hpref n (n + 1) le_rfl
      have hlimit :
          ramseyApprox H (n + 1) L =
            ramseyApprox H (n + 1) (shapeClosedStage H c hpref n) := by
        apply Subtype.ext
        funext x
        change L x.1 = shapeClosedStage H c hpref n x.1
        exact MMap.fusionLimit_eq_stage H
          (shapeClosedStage H c hpref)
          (shapeClosedStage_stable H c hpref) x.2
      exact hlimit.trans hstage

/-- The shape-preserving M-map approximation space is metrically closed. -/
theorem shapeIsMetricallyClosed
    (H : SMTree S) :
    (ramseyApproximationSystem H).IsMetricallyClosed := by
  intro c hpref
  let L := MMap.fusionLimit H (shapeClosedStage H c hpref)
    (shapeClosedStage_stable H c hpref)
  refine ⟨L, ?_⟩
  exact shapeClosed_limit_realizes H c hpref

end SMTree
end SuccessorTree

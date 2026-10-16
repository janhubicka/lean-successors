import SuccessorTree.RamseySpace.Nonempty
import RamseySpace.ClosedTopology

/-!
# Closedness and fusion of the direct monoid approximation space

The points are the actual distinguished monoid maps `MMap H`; finite
approximations are their restrictions to the initial tree levels.
The manuscript's topological shape-map Ellentuck theorem requires
the corresponding approximation image to be closed.

This closedness follows from **M1 fusion alone**. Whenever a full
sequence of approximations has every finite prefix realized, choose
successively longer realizing monoid maps. They agree on each frozen
level, hence their pointwise fusion limit is again in the monoid.

Together with the previously verified A.1 and A.2 finitization, this
also yields fusion completeness. Neither A.3(2) amalgamation nor
A.4 pigeonhole is asserted here. Those remain separate obligations
for Theorem 1.11; fat-tree Ellentuck does not discharge them by itself.
-/

namespace SuccessorTree.SMTree

universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

/-- The approximation image of the actual M-map space is closed under
coherent limits of finite restrictions. This is the finite-prefix
criterion for the book's Tychonoff closedness hypothesis. -/
theorem ramseyApproximation_isMetricallyClosed
    (H : SMTree S) :
    (ramseyApproximationSystem H).IsMetricallyClosed := by
  classical
  let R := ramseyApproximationSystem H
  intro c hpref
  let F : Nat → MMap H :=
    fun i => Classical.choose (hpref (i + 2))
  have hF : ∀ i n, n ≤ i + 2 → R.approx n (F i) = c n := by
    intro i n hn
    exact (Classical.choose_spec (hpref (i + 2))) n hn
  have hstable : ShapeMap.FusionStable (fun i => (F i).map) := by
    intro i x hx
    let m : Nat := LevelTree.lev x
    have hEq : R.approx (m + 1) (F i) =
        R.approx (m + 1) (F (i + 1)) :=
      (hF i (m + 1) (by omega)).trans
        (hF (i + 1) (m + 1) (by omega)).symm
    have hMap := congrArg Subtype.val hEq
    change (F i).restrictLe H m =
      (F (i + 1)).restrictLe H m at hMap
    exact congrFun hMap ⟨x, le_rfl⟩
  let Lmap : ShapeMap S :=
    ShapeMap.fusionLimit (fun i => (F i).map) hstable
  have hLmem : Lmap ∈ H.M :=
    H.fusion_mem (fun i => (F i).map) (fun i => (F i).mem) hstable
  let L : MMap H := ⟨Lmap, hLmem⟩
  refine ⟨L, ?_⟩
  intro n
  cases n with
  | zero =>
      cases c 0
      rfl
  | succ n =>
      have hStage :
          R.approx (n + 1) L = R.approx (n + 1) (F n) := by
        apply Subtype.ext
        change L.restrictLe H n = (F n).restrictLe H n
        funext a
        change L a.1 = (F n) a.1
        exact ShapeMap.fusionLimit_eq_stage
          (fun i => (F i).map) hstable a.2
      exact hStage.trans (hF n (n + 1) (by omega))

/-- Literal Tychonoff closedness of the approximation image in
`AR^ℕ` with the book's discrete topology. -/
theorem ramseyApproximation_isTychonoffClosed
    (H : SMTree S) :
    (ramseyApproximationSystem H).IsTychonoffClosed :=
  ((ramseyApproximationSystem H).isTychonoffClosed_iff_isClosedApproximationImage).2
      (H.ramseyApproximation_isMetricallyClosed)

/-- The direct M-map approximation space has fusion limits already
at the A.1/A.2 stage, without assuming A.3 or A.4. -/
theorem ramseyApproximation_fusionComplete
    (H : SMTree S) :
    RamseySpace.FusionComplete (ramseyApproximationSystem H) :=
  (H.ramseyFinitization).fusionComplete_of_isMetricallyClosed
    (H.ramseyApproximation_isMetricallyClosed)

end SuccessorTree.SMTree

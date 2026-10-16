import SuccessorTree.ShapeLocalPigeonhole

/-!
# Direct M-space A.4 at positive depth

The existing `shapeLocalPigeonhole` does more than a particular
Hales–Jewett line: it homogenizes the **entire** one-step
front for an arbitrary realized finite prefix of strictly positive
depth. This turns it into Todorčević A.4 for the *actual*
M-map approximation space (not only for fat trees).

The depth-zero case is deliberately excluded; the latter is
possible only for the empty source approximation and requires a
separate one-dimensional reduction at source level zero.
-/

namespace SuccessorTree.SMTree

universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

/-- Todorčević A.4 in the direct M-space for every positive-depth
finite approximation, with arbitrary two-colouring of its full
one-step approximation front. -/
theorem directPigeonhole_positiveDepth
    (H : SMTree S) {n d : Nat}
    (a : RamseyApprox H n) (B : MMap H)
    (hd : (ramseyFinitization H).HasDepth a B d)
    (hpos : 0 < d)
    (O : Set (RamseyApprox H (n + 1))) :
    ∃ A : MMap H,
      A ∈ (ramseyApproximationSystem H).levelNeighborhood d B ∧
      ((ramseyApproximationSystem H).oneStepApproximations a A ⊆ O ∨
       Disjoint ((ramseyApproximationSystem H).oneStepApproximations a A) O) := by
  classical
  let colour : StepColouring H Bool := fun m b =>
    if h : m = n then
      decide (Eq.mp
        (congrArg (fun k : Nat => RamseyApprox H (k + 1)) h) b ∈ O)
    else false
  have hcolour (b : RamseyApprox H (n + 1)) :
      colour n b = decide (b ∈ O) := by
    rfl
  obtain ⟨A, hAB, c, hc⟩ :=
    H.shapeLocalPigeonhole colour ⟨n, a⟩ B d hpos hd
  refine ⟨A, hAB, ?_⟩
  cases c with
  | false =>
      right
      apply Set.disjoint_left.mpr
      intro b hb hOb
      have h := hc b hb
      rw [hcolour b] at h
      simp [hOb] at h
  | true =>
      left
      intro b hb
      by_contra hNot
      have h := hc b hb
      rw [hcolour b] at h
      simp [hNot] at h

end SuccessorTree.SMTree

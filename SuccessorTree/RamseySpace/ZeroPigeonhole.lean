import SuccessorTree.RamseySpace.PositivePigeonhole
import SuccessorTree.ShapeFiniteProduct
import Mathlib.Tactic

/-!
# The direct M-map Ramsey space satisfies Todorčević A.4

The positive-depth case is `directPigeonhole_positiveDepth`,
already established by the existing arbitrary-prefix local
pigeonhole theorem.

The only other case is depth zero, which (by A.2's index bound)
has the unique empty approximation as its stem. There the
one-dimensional shape-Ramsey theorem at source level zero
homogenizes the complete front after right composition with
the ambient map.

This is an **actual A.4 theorem for M maps**, not just for fat
trees. It does not add the A.3(2) amalgamation hypothesis still
needed for the full shape-map Ellentuck theorem.
-/

namespace SuccessorTree.SMTree

universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

/-- A.4 for the depth-zero/empty finite-approximation case. -/
theorem directPigeonhole_zeroDepth
    (H : SMTree S) (a : RamseyApprox H 0) (B : MMap H)
    (O : Set (RamseyApprox H 1)) :
    ∃ A : MMap H,
      A ∈ (ramseyApproximationSystem H).levelNeighborhood 0 B ∧
      ((ramseyApproximationSystem H).oneStepApproximations a A ⊆ O ∨
       Disjoint ((ramseyApproximationSystem H).oneStepApproximations a A) O) := by
  classical
  let χ : AM H 0 1 → Bool := fun g =>
    decide (ramseyApprox H 1
      (MMap.comp H B (g.representative H)) ∈ O)
  obtain ⟨W, hW⟩ := H.shapeOneDimensionalRamsey 0 χ
  let A : MMap H := MMap.comp H B W.1
  have hAB :
      A ∈ (ramseyApproximationSystem H).levelNeighborhood 0 B := by
    constructor
    · exact ⟨W.1, fun _ => rfl⟩
    · rfl
  let q0 : AM H 0 1 := AM.id1 H 0
  let c : Bool := χ (H.shapeAct 0 W q0)
  have hAll :
      ∀ b, b ∈ (ramseyApproximationSystem H).oneStepApproximations a A →
        decide (b ∈ O) = c := by
    intro b hb
    rcases hb with ⟨X, hXA, hXb⟩
    rcases hXA.1 with ⟨K, hK⟩
    have hFix : K.FixesBelow H 0 := by
      intro x hx
      omega
    let q : AM H 0 1 := K.toAM H 0 1 hFix
    have hqact (x : T) (hx : LevelTree.lev x ≤ 0) :
        (H.shapeAct 0 W q).representative H x = W.1 (K x) := by
      rw [H.shapeAct_representative_agrees 0 W q x hx]
      exact congrArg W.1
        (MMap.toAM_representative_agrees H K 0 1 hFix x (by omega))
    have hEq :
        b = ramseyApprox H 1
          (MMap.comp H B ((H.shapeAct 0 W q).representative H)) := by
      rw [← hXb]
      apply Subtype.ext
      funext x
      change X x.1 =
        B ((H.shapeAct 0 W q).representative H x.1)
      rw [hK x.1]
      change B (W.1 (K x.1)) =
        B ((H.shapeAct 0 W q).representative H x.1)
      rw [hqact x.1 x.2]
    calc
      decide (b ∈ O) = χ (H.shapeAct 0 W q) := by
        dsimp [χ]
        rw [hEq]
      _ = χ (H.shapeAct 0 W q0) := hW q q0
      _ = c := rfl
  refine ⟨A, hAB, ?_⟩
  cases hc : c with
  | false =>
      right
      apply Set.disjoint_left.mpr
      intro b hb hOb
      have h := hAll b hb
      simp [hOb, hc] at h
  | true =>
      left
      intro b hb
      by_contra hNot
      have h := hAll b hb
      simp [hNot, hc] at h

/-- **Full A.4 for the direct M-map approximation system**, including
both the empty stem (depth zero) and arbitrary nonempty stems.
The result has no hidden A.3(2) premise, and uses only the
original M1–M3 successor-tree axioms. -/
theorem directPigeonhole
    (H : SMTree S) {n d : Nat}
    (a : RamseyApprox H n) (B : MMap H)
    (hd : (ramseyFinitization H).HasDepth a B d)
    (O : Set (RamseyApprox H (n + 1))) :
    ∃ A : MMap H,
      A ∈ (ramseyApproximationSystem H).levelNeighborhood d B ∧
      ((ramseyApproximationSystem H).oneStepApproximations a A ⊆ O ∨
       Disjoint ((ramseyApproximationSystem H).oneStepApproximations a A) O) := by
  by_cases hzero : d = 0
  · have hn : n = 0 := by
      have hle := H.ramseyLeFin_level_le hd.1
      omega
    subst n
    subst d
    exact H.directPigeonhole_zeroDepth a B O
  · exact H.directPigeonhole_positiveDepth a B hd
      (Nat.pos_of_ne_zero hzero) O

end SuccessorTree.SMTree

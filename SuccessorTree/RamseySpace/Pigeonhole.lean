import SuccessorTree.RamseySpace.Nonempty
import SuccessorTree.ShapeLocalPigeonhole
import SuccessorTree.ShapeFiniteRamsey

/-!
# Todorčević A4 for shape-preserving maps

The positive-depth case is exactly the already formalized local one-step
pigeonhole theorem.  The only missing case is the empty approximation, whose
depth is zero.  There we apply the relative one-moving-level Ramsey theorem
directly below the prescribed outer map.

No Ellentuck amalgamation hypothesis is used here.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Every M-map is a shape subspace at cut zero. -/
def shapeSubspaceZero (H : SMTree S) (B : MMap H) :
    ShapeSubspace H 0 :=
  ⟨B, by
    intro x hx
    omega⟩

/-- A reduction can be recovered as literal right composition with its
witness. -/
theorem mmap_eq_comp_of_ramseyReduction
    (H : SMTree S) {A B : MMap H}
    (hAB : RamseyReduction H A B) :
    ∃ K : MMap H, A = MMap.comp H B K := by
  rcases hAB with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  apply MMap.ext_apply
  intro x
  exact hK x

/-- The A4 conclusion at the empty approximation. -/
theorem shapePigeonhole_zero
    (H : SMTree S)
    (a : RamseyApprox H 0)
    (B : MMap H)
    (O : Set (RamseyApprox H 1)) :
    ∃ A : MMap H,
      A ∈ (ramseyApproximationSystem H).levelNeighborhood 0 B ∧
      ((ramseyApproximationSystem H).oneStepApproximations a A ⊆ O ∨
        Disjoint
          ((ramseyApproximationSystem H).oneStepApproximations a A) O) := by
  classical
  let colour : RamseyApprox H 1 → Bool := fun b => decide (b ∈ O)
  obtain ⟨W, hWB, hhom⟩ :=
    H.shapeRamsey_one_relative 0 (shapeSubspaceZero H B) colour
  have hWB0 :
      W.1 ∈ (ramseyApproximationSystem H).levelNeighborhood 0 B := by
    exact ⟨hWB, rfl⟩
  refine ⟨W.1, hWB0, ?_⟩
  let base : RamseyApprox H 1 := ramseyApprox H 1 W.1
  by_cases hbase : base ∈ O
  · left
    intro b hb
    rcases hb with ⟨X, hXaW, hXb⟩
    obtain ⟨K, hXeq⟩ := mmap_eq_comp_of_ramseyReduction H hXaW.1
    let K0 : ShapeSubspace H 0 := shapeSubspaceZero H K
    let I0 : ShapeSubspace H 0 := ShapeSubspace.id H 0
    have hconst := hhom K0 I0
    have hright :
        ramseyApprox H 1 (MMap.comp H W.1 I0.1) = base := by
      apply Subtype.ext
      funext x
      rfl
    have hleft :
        ramseyApprox H 1 (MMap.comp H W.1 K0.1) = b := by
      rw [← hXb, hXeq]
    have hbool : colour b = colour base := by
      rw [← hleft, ← hright]
      exact hconst
    have htrue : colour base = true := by
      simp only [colour, decide_eq_true_eq]
      exact hbase
    have : colour b = true := hbool.trans htrue
    simpa only [colour, decide_eq_true_eq] using this
  · right
    rw [Set.disjoint_left]
    intro b hb hbO
    rcases hb with ⟨X, hXaW, hXb⟩
    obtain ⟨K, hXeq⟩ := mmap_eq_comp_of_ramseyReduction H hXaW.1
    let K0 : ShapeSubspace H 0 := shapeSubspaceZero H K
    let I0 : ShapeSubspace H 0 := ShapeSubspace.id H 0
    have hconst := hhom K0 I0
    have hright :
        ramseyApprox H 1 (MMap.comp H W.1 I0.1) = base := by
      apply Subtype.ext
      funext x
      rfl
    have hleft :
        ramseyApprox H 1 (MMap.comp H W.1 K0.1) = b := by
      rw [← hXb, hXeq]
    have hbool : colour b = colour base := by
      rw [← hleft, ← hright]
      exact hconst
    have htrue : colour b = true := by
      simp only [colour, decide_eq_true_eq]
      exact hbO
    have hfalse : colour base = false := by
      simp only [colour, decide_eq_false_iff_not]
      exact hbase
    exact Bool.noConfusion (htrue.symm.trans (hbool.trans hfalse))

/-- Membership colouring at one prescribed approximation level, extended
arbitrarily to the other levels required by the front-fusion interface. -/
noncomputable def shapeA4Colour
    (H : SMTree S) (n : Nat) (O : Set (RamseyApprox H (n + 1))) :
    StepColouring H Bool :=
  fun m b =>
    if h : m = n then
      decide ((h ▸ b) ∈ O)
    else
      false

@[simp] theorem shapeA4Colour_at
    (H : SMTree S) (n : Nat) (O : Set (RamseyApprox H (n + 1)))
    (b : RamseyApprox H (n + 1)) :
    shapeA4Colour H n O n b = decide (b ∈ O) := by
  simp [shapeA4Colour]

/-- Todorčević A4 for the shape-preserving-map approximation space. -/
theorem shapePigeonhole
    (H : SMTree S)
    {n : Nat} (a : RamseyApprox H n)
    (B : MMap H) {d : Nat}
    (hd : (ramseyFinitization H).HasDepth a B d)
    (O : Set (RamseyApprox H (n + 1))) :
    ∃ A : MMap H,
      A ∈ (ramseyApproximationSystem H).levelNeighborhood d B ∧
      ((ramseyApproximationSystem H).oneStepApproximations a A ⊆ O ∨
        Disjoint
          ((ramseyApproximationSystem H).oneStepApproximations a A) O) := by
  classical
  cases n with
  | zero =>
      have hd0 : d = 0 := by
        by_contra hne
        have hpos : 0 < d := Nat.pos_of_ne_zero hne
        have hnot := hd.2 0 hpos
        exact hnot trivial
      subst d
      exact shapePigeonhole_zero H a B O
  | succ n =>
      have hdpos : 0 < d := by
        by_contra hnot
        have hd0 : d = 0 := Nat.eq_zero_of_not_pos hnot
        subst d
        have hfin :
            RamseyLeFin H
              ⟨n + 1, a⟩
              ((ramseyApproximationSystem H).finiteApprox 0 B) :=
          hd.1
        exact hfin
      let colour := shapeA4Colour H (n + 1) O
      obtain ⟨A, hAB, c, hc⟩ :=
        H.shapeLocalPigeonhole colour
          (⟨n + 1, a⟩ :
            (ramseyApproximationSystem H).FiniteApprox)
          B d hdpos hd
      refine ⟨A, hAB, ?_⟩
      cases hcval : c with
      | false =>
          right
          rw [Set.disjoint_left]
          intro b hb hbO
          have h := hc b hb
          have hcolour : colour (n + 1) b = true := by
            change decide (b ∈ O) = true
            exact of_decide_eq_true rfl hbO
          rw [hcval] at h
          exact Bool.noConfusion (hcolour.symm.trans h)
      | true =>
          left
          intro b hb
          have h := hc b hb
          rw [hcval] at h
          change decide (b ∈ O) = true at h
          exact of_decide_eq_true h

end SMTree
end SuccessorTree

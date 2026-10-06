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

/-- The tagged target set used to turn one prescribed approximation level
into a component of a step-colouring.  Using the sigma type avoids dependent
casts in the colouring itself. -/
def taggedOneStepTarget
    (H : SMTree S) (n : Nat)
    (O : Set ((ramseyApproximationSystem H).Approx (n + 1))) :
    Set (ramseyApproximationSystem H).FiniteApprox :=
  {q | ∃ b ∈ O, q = ⟨n + 1, b⟩}

/-- At the target level, membership in the tagged set is exactly membership
in the original colour class. -/
theorem mem_taggedOneStepTarget_iff
    (H : SMTree S) (n : Nat)
    (O : Set ((ramseyApproximationSystem H).Approx (n + 1)))
    (b : (ramseyApproximationSystem H).Approx (n + 1)) :
    (⟨n + 1, b⟩ : (ramseyApproximationSystem H).FiniteApprox) ∈
        taggedOneStepTarget H n O ↔
      b ∈ O := by
  constructor
  · rintro ⟨c, hc, hcb⟩
    cases hcb
    exact hc
  · intro hb
    exact ⟨b, hb, rfl⟩

/-- Membership colouring at one prescribed approximation level, extended
arbitrarily to all levels through the tagged sigma type. -/
noncomputable def shapeA4Colour
    (H : SMTree S) (n : Nat)
    (O : Set ((ramseyApproximationSystem H).Approx (n + 1))) :
    StepColouring H Bool := by
  classical
  intro m b
  exact if
    (⟨m + 1, b⟩ : (ramseyApproximationSystem H).FiniteApprox) ∈
      taggedOneStepTarget H n O
    then true else false

theorem shapeA4Colour_true_iff
    (H : SMTree S) (n : Nat)
    (O : Set ((ramseyApproximationSystem H).Approx (n + 1)))
    (b : (ramseyApproximationSystem H).Approx (n + 1)) :
    shapeA4Colour H n O n b = true ↔ b ∈ O := by
  classical
  simp only [shapeA4Colour, if_eq_true_eq]
  exact mem_taggedOneStepTarget_iff H n O b

/-- The A4 conclusion at the empty approximation. -/
theorem shapePigeonhole_zero
    (H : SMTree S)
    (a : (ramseyApproximationSystem H).Approx 0)
    (B : MMap H)
    (O : Set ((ramseyApproximationSystem H).Approx 1)) :
    ∃ A : MMap H,
      A ∈ (ramseyApproximationSystem H).levelNeighborhood 0 B ∧
      ((ramseyApproximationSystem H).oneStepApproximations (n := 0) a A ⊆ O ∨
        Disjoint
          ((ramseyApproximationSystem H).oneStepApproximations (n := 0) a A) O) := by
  classical
  let colour : RamseyApprox H 1 → Bool :=
    fun b => if b ∈ O then true else false
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
    change RamseyApprox H 1 at b
    rcases hb with ⟨X, hXaW, hXb⟩
    change ramseyApprox H 1 X = b at hXb
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
      have heq := congrArg (ramseyApprox H 1) hXeq
      exact heq.symm.trans hXb
    have hbool : colour b = colour base := by
      rw [← hleft, ← hright]
      exact hconst
    have hbaseColour : colour base = true := by
      simp [colour, hbase]
    have hbColour : colour b = true := hbool.trans hbaseColour
    by_contra hnot
    have : colour b = false := by simp [colour, hnot]
    exact Bool.noConfusion (hbColour.symm.trans this)
  · right
    rw [Set.disjoint_left]
    intro b hb hbO
    change RamseyApprox H 1 at b
    rcases hb with ⟨X, hXaW, hXb⟩
    change ramseyApprox H 1 X = b at hXb
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
      have heq := congrArg (ramseyApprox H 1) hXeq
      exact heq.symm.trans hXb
    have hbool : colour b = colour base := by
      rw [← hleft, ← hright]
      exact hconst
    have hbColour : colour b = true := by simp [colour, hbO]
    have hbaseColour : colour base = false := by simp [colour, hbase]
    exact Bool.noConfusion (hbColour.symm.trans (hbool.trans hbaseColour))

/-- Todorčević A4 for the shape-preserving-map approximation space. -/
theorem shapePigeonhole
    (H : SMTree S)
    {n : Nat} (a : (ramseyApproximationSystem H).Approx n)
    (B : MMap H) {d : Nat}
    (hd : (ramseyFinitization H).HasDepth a B d)
    (O : Set ((ramseyApproximationSystem H).Approx (n + 1))) :
    ∃ A : MMap H,
      A ∈ (ramseyApproximationSystem H).levelNeighborhood d B ∧
      ((ramseyApproximationSystem H).oneStepApproximations (n := n) a A ⊆ O ∨
        Disjoint
          ((ramseyApproximationSystem H).oneStepApproximations (n := n) a A) O) := by
  classical
  cases n with
  | zero =>
      have hd0 : d = 0 := by
        by_contra hne
        have hpos : 0 < d := Nat.pos_of_ne_zero hne
        have hnot := hd.2 0 hpos
        apply hnot
        trivial
      subst d
      exact shapePigeonhole_zero H a B O
  | succ n =>
      have hdpos : 0 < d := by
        by_contra hnot
        have hd0 : d = 0 := Nat.eq_zero_of_not_pos hnot
        subst d
        have hfin := hd.1
        change False at hfin
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
          rw [hcval] at h
          have htrue :
              shapeA4Colour H (n + 1) O (n + 1) b = true :=
            (shapeA4Colour_true_iff H (n + 1) O b).2 hbO
          exact Bool.noConfusion (htrue.symm.trans h)
      | true =>
          left
          intro b hb
          have h := hc b hb
          rw [hcval] at h
          exact (shapeA4Colour_true_iff H (n + 1) O b).1 h

end SMTree
end SuccessorTree

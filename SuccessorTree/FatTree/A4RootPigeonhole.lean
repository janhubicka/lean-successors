import SuccessorTree.FatTree.A4TypedBridge
import SuccessorTree.FatTree.A4Root

/-!
# The root-fixed case of the fat-tree A4 pigeonhole theorem

When there is no letter skipping level zero, every row with source cut zero
is the identity. The typed one-step front then has at most one member and
is homogeneous without any thinning. This completes only the degenerate
root-fixed branch; it does not assume or prove the general A4 conclusion.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- Equality of all available rows implies that the geometric one-step front
is a subsingleton. No choice of a canonical composition is imposed. -/
theorem oneStep_subsingleton_of_rows_equal
    {n : Nat} (a : (approximationSystem H).Approx n) (U : FatTree H)
    (hrows : ∀ g k : AM H a.1.terminalCut 1, g = k) :
    ((approximationSystem H).oneStepApproximations a U).Subsingleton := by
  intro b hb b' hb'
  obtain ⟨g, _, hbg⟩ := oneStep_exists_appendedRow H a U hb
  obtain ⟨k, _, hbk⟩ := oneStep_exists_appendedRow H a U hb'
  apply Subtype.ext
  rw [hbg, hbk, hrows g k]

/-- At a root-fixed source cut, the whole geometric one-step front has at
most one element. This covers the empty-front case as well. -/
theorem oneStep_subsingleton_at_fixedRoot
    {n : Nat} (a : (approximationSystem H).Approx n) (U : FatTree H)
    (hcut : a.1.terminalCut = 0)
    (hno : ¬ Nonempty (OneLevelLetter H 0)) :
    ((approximationSystem H).oneStepApproximations a U).Subsingleton := by
  apply oneStep_subsingleton_of_rows_equal H a U
  rw [hcut]
  intro g k
  exact (H.rootRow_eq_id1_of_no_rootLetter hno g).trans
    (H.rootRow_eq_id1_of_no_rootLetter hno k).symm

/-- A subsingleton one-step front is homogeneous for every set of one-step
approximations. -/
theorem oneStep_homogeneous_of_subsingleton
    {n : Nat} (a : (approximationSystem H).Approx n) (U : FatTree H)
    (hsub : ((approximationSystem H).oneStepApproximations a U).Subsingleton)
    (O : Set ((approximationSystem H).Approx (n + 1))) :
    (approximationSystem H).oneStepApproximations a U ⊆ O ∨
      (approximationSystem H).oneStepApproximations a U ⊆ Oᶜ := by
  classical
  by_cases hit : ∃ b, b ∈ (approximationSystem H).oneStepApproximations a U ∧ b ∈ O
  · obtain ⟨b, hb, hbO⟩ := hit
    left
    intro b' hb'
    have heq : b' = b := hsub hb' hb
    simpa only [heq] using hbO
  · right
    intro b hb hbO
    exact hit ⟨b, hb, hbO⟩

/-- The typed A4 conclusion at a root-fixed source cut. The original tree is
already homogeneous and belongs to its own neighborhood at every depth d. -/
theorem typed_a4_at_fixedRoot
    {n : Nat} (a : (approximationSystem H).Approx n) (U : FatTree H)
    (hcut : a.1.terminalCut = 0)
    (hno : ¬ Nonempty (OneLevelLetter H 0))
    (d : Nat) (O : Set ((approximationSystem H).Approx (n + 1))) :
    ∃ V : FatTree H,
      V ∈ (approximationSystem H).levelNeighborhood d U ∧
      ((approximationSystem H).oneStepApproximations a V ⊆ O ∨
        (approximationSystem H).oneStepApproximations a V ⊆ Oᶜ) := by
  refine ⟨U, (approximationSystem H).self_mem_levelNeighborhood d U, ?_⟩
  exact oneStep_homogeneous_of_subsingleton H a U
    (oneStep_subsingleton_at_fixedRoot H a U hcut hno) O

end SuccessorTree.SMTree.FatTree

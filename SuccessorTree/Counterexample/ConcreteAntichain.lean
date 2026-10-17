import SuccessorTree.Counterexample.CompatibilityMarker
import SuccessorTree.Counterexample.BinarySupports
import SuccessorTree.Counterexample.GreedySelection
import SuccessorTree.Counterexample.PureEnumeration
import Mathlib.Tactic

/-!
# A ZFC right-incompatible transversal meeting every pure monoid cone

This assembles all the previously kernel-checked ingredients of the
counterexample to the original shape-map Ellentuck Theorem 1.11:

* every pure free-ancestral map can be enumerated by binary sequences;
* every binary sequence supplies an infinite marked shape map Q_A;
* two different binary branches have almost-disjoint retained levels;
* a given old root-raised map is compatible with at most one marked
  candidate beneath each fixed pure map;
* in an initial well-order of continuum type, every predecessor set
  is smaller than the full support-index set;
* the generic well-founded greedy recursion picks incompatible maps.

The resulting antichain is **cofinal across pure algebraic cones**.
Its nowhere-density is provided by the separate general
\`incompatible_family_isNowhereDense\` theorem.
-/

namespace SuccessorTree.Counterexample

open SuccessorTree.FreeAncestral
open SuccessorTree.SMTree

abbrev ExampleMap := SMTree.MMap markerMonoid
abbrev BinaryBranch := ℕ → Bool

/-- The unique source-level-one successor of the root. -/
def markedFirstNode : Node Unit 1 :=
  ⟨1, History.step History.root initialEmptyCode⟩

@[simp] theorem markedFirstNode_level : markedFirstNode.level = 1 := rfl

/-- Maps whose image of the original root lies at a positive level.
All greedy candidates lie in this subtype, an essential hypothesis
of the universal retained-level marker obstruction. -/
def RootRaisedMap : Type :=
  {F : ExampleMap //
    0 < (F (rootNode (Label := Unit) (arity := 1))).level}

/-- Every pure map fixes both the original root and its unique
level-one successor. -/
theorem pureFree_fixes_root (H : PureFreeMap) :
    H.val (rootNode (Label := Unit) (arity := 1)) =
      rootNode (Label := Unit) (arity := 1) :=
  H.property _ (by decide)

theorem pureFree_fixes_first (H : PureFreeMap) :
    H.val markedFirstNode = markedFirstNode :=
  H.property _ (by decide)

/-- The marked map with binary-prefix retained levels, acted on by a
pure outer map. The positive-root certificate is proved from the
verified root image of the M1-fusion and pointwise purity of H. -/
noncomputable def raisedCandidate (H : PureFreeMap) (b : BinaryBranch) :
    RootRaisedMap := by
  let Q : ExampleMap :=
    markedFusion (branchLevel b) (branchLevel_strictMono b)
      (branchLevel_zero b)
  refine ⟨SMTree.MMap.comp markerMonoid H.val Q, ?_⟩
  change 0 < (H.val (Q (rootNode (Label := Unit) (arity := 1)))).level
  have hroot : Q (rootNode (Label := Unit) (arity := 1)) =
      markedFirstNode := markedFusion_root
        (branchLevel b) (branchLevel_strictMono b) (branchLevel_zero b)
  rw [hroot, pureFree_fixes_first]
  decide

/-- Every selected candidate is literally below its prescribed pure
map in the right-composition reduction. -/
theorem raisedCandidate_reduces (H : PureFreeMap) (b : BinaryBranch) :
    SMTree.RamseyReduction markerMonoid
      (raisedCandidate H b).val H.val := by
  refine ⟨markedFusion (branchLevel b) (branchLevel_strictMono b)
      (branchLevel_zero b), ?_⟩
  intro x
  rfl

/-- All candidates have precisely the desired finite root approximation
\`f(root)=markedFirstNode\`. -/
theorem raisedCandidate_root (H : PureFreeMap) (b : BinaryBranch) :
    (raisedCandidate H b).val
      (rootNode (Label := Unit) (arity := 1)) =
      markedFirstNode := by
  change H.val
    (markedFusion (branchLevel b) (branchLevel_strictMono b)
      (branchLevel_zero b)
      (rootNode (Label := Unit) (arity := 1))) =
      markedFirstNode
  rw [markedFusion_root]
  exact pureFree_fixes_first H

/-- The concrete uniqueness lemma: once H is fixed and G sends the
original root to a positive level, at most **one** binary support can
produce an H∘Q_A compatible with G. -/
theorem raisedCandidate_compatible_unique
    (H : PureFreeMap) (G : RootRaisedMap)
    (b c : BinaryBranch)
    (hb : SMTree.RightCompatible markerMonoid G.val
      (raisedCandidate H b).val)
    (hc : SMTree.RightCompatible markerMonoid G.val
      (raisedCandidate H c).val) : b = c := by
  by_contra hne
  have hroot : H.val (rootNode (Label := Unit) (arity := 1)) =
      rootNode (Label := Unit) (arity := 1) :=
    pureFree_fixes_root H
  have hB :=
    compatible_marked_has_infinite_support
      (branchLevel b) (branchLevel_strictMono b)
      (branchLevel_zero b) G.val H.val G.property hroot hb
  have hC :=
    compatible_marked_has_infinite_support
      (branchLevel c) (branchLevel_strictMono c)
      (branchLevel_zero c) G.val H.val G.property hroot hc
  have hfinite : (MeetingLevels G.val H.val).Finite :=
    (branchLevel_almostDisjoint b c hne).subset
      (fun k hk => ⟨hB.2 hk, hC.2 hk⟩)
  exact hB.1 hfinite

/-- The exact algebraic antichain required by the counterexample:
a pairwise right-incompatible set of total shape maps meets every
pure cone [f,H], with f mapping the source root to the first successor.

The proof uses a well-order of *least* ordinal type for the continuum.
Its proper initial segments are strictly smaller without requiring
the continuum to be regular. -/
theorem exists_pure_meeting_incompatible_family :
    ∃ N : Set ExampleMap,
      SMTree.PairwiseRightIncompatible markerMonoid N ∧
      ∀ H : PureFreeMap, ∃ F : ExampleMap,
        F ∈ N ∧
        SMTree.RamseyReduction markerMonoid F H.val ∧
        F (rootNode (Label := Unit) (arity := 1)) = markedFirstNode := by
  classical
  obtain ⟨schedule, hsurj⟩ := exists_pureFree_enumeration
  obtain ⟨ord, wfInst, hminimal⟩ :=
    Cardinal.exists_ord_eq_type_lt BinaryBranch
  letI : LinearOrder BinaryBranch := ord
  -- The function type carries a pre-existing pointwise Pi.preorder.
  -- Fix the precedence explicitly: the transfinite recursion must use
  -- the *well-order* supplied by ord, never the pointwise function order.
  letI : Preorder BinaryBranch := ord.toPreorder
  letI : WellFoundedLT BinaryBranch := wfInst
  let wf : WellFounded (fun a b : BinaryBranch => a < b) :=
    wellFounded_lt
  let candidates : BinaryBranch → BinaryBranch → RootRaisedMap :=
    fun stage b => raisedCandidate (schedule stage) b
  let conflicts : RootRaisedMap → RootRaisedMap → Prop :=
    fun F G => SMTree.RightCompatible markerMonoid F.val G.val
  have hUnique :
      ∀ (stage : BinaryBranch) (g : RootRaisedMap)
        (b c : BinaryBranch),
        conflicts g (candidates stage b) →
        conflicts g (candidates stage c) → b = c := by
    intro stage g b c hb hc
    exact raisedCandidate_compatible_unique (schedule stage) g b c hb hc
  have hSmall : ∀ stage : BinaryBranch,
      ¬ Nonempty (BinaryBranch ↪ {j : BinaryBranch // j < stage}) := by
    intro stage
    exact no_embedding_earlier_of_minimal_ord hminimal stage
  let selected : BinaryBranch → RootRaisedMap :=
    greedySelection wf candidates conflicts hUnique hSmall
  let N : Set ExampleMap := Set.range (fun stage => (selected stage).val)
  refine ⟨N, ?_, ?_⟩
  · intro F G hFN hGN hc
    obtain ⟨i, rfl⟩ := hFN
    obtain ⟨j, rfl⟩ := hGN
    by_cases hij : i = j
    · subst j
      rfl
    · have hSymm : ∀ a b : RootRaisedMap,
          conflicts a b → conflicts b a := by
        intro a b h
        obtain ⟨K, hKa, hKb⟩ := h
        exact ⟨K, hKb, hKa⟩
      have hBad :=
        greedySelection_pairwise wf candidates conflicts
          hUnique hSmall hSymm hij
      exact False.elim (hBad hc)
  · intro H
    obtain ⟨stage, hsched⟩ := hsurj H
    obtain ⟨b, hsel⟩ :=
      greedySelection_is_candidate wf candidates conflicts
        hUnique hSmall stage
    refine ⟨(selected stage).val, ⟨stage, rfl⟩, ?_, ?_⟩
    · have hred :
          SMTree.RamseyReduction markerMonoid
            (candidates stage b).val H.val := by
        dsimp only [candidates]
        rw [hsched]
        exact raisedCandidate_reduces H b
      simpa only [selected] using hsel ▸ hred
    · have hroot :
          (candidates stage b).val
            (rootNode (Label := Unit) (arity := 1)) =
            markedFirstNode := by
        dsimp only [candidates]
        rw [hsched]
        exact raisedCandidate_root H b
      simpa only [selected] using hsel ▸ hroot

end SuccessorTree.Counterexample

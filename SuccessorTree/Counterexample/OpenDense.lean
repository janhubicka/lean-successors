import SuccessorTree.Counterexample.Final
import RamseySpace.Ellentuck
import Mathlib.Topology.GDelta.Basic

/-!
# The open dense complement is not Ramsey under pure-depth refinements

This is the second, Baire-property half of the refutation of the
manuscript's Theorem 1.11. Its first half (meagre but not pure-Ramsey
null) is already proved in `Counterexample.Final`.

We do **not** assume A.3(2) for the direct shape-map monoid.
The source's Ramsey notion is depth-preserving, so a homogeneous
refinement must retain the original root stem and lie under a
pure map fixing source levels 0 and 1. This is strictly stronger
than allowing arbitrary end-extensions of the finite stem.
-/

namespace SuccessorTree.Counterexample

open SuccessorTree.FreeAncestral
open SuccessorTree.SMTree

/-- A dense open subset of the genuine direct shape-map monoid Ellentuck
topology such that *each* depth-preserving pure root neighborhood
meets **both** the set and its complement. Thus the open set is
not Ramsey under the manuscript's definition.

This is the explicit positive-Baire-side counterpart to
`exists_meagre_not_avoidable`. -/
theorem exists_open_dense_no_pure_homogeneous_root :
    ∃ O : Set ExampleMap,
      @IsOpen ExampleMap
        (SMTree.ramseyApproximationSystem markerMonoid).ellentuckTopology O ∧
      @Dense ExampleMap
        (SMTree.ramseyApproximationSystem markerMonoid).ellentuckTopology O ∧
      ∀ H : PureFreeMap,
        (RootNeighborhood H.val ∩ O).Nonempty ∧
        (RootNeighborhood H.val ∩ Oᶜ).Nonempty := by
  classical
  letI : TopologicalSpace ExampleMap :=
    (SMTree.ramseyApproximationSystem markerMonoid).ellentuckTopology
  letI : TopologicalSpace
      (SMTree.ramseyApproximationSystem markerMonoid).Point :=
    (SMTree.ramseyApproximationSystem markerMonoid).ellentuckTopology
  obtain ⟨N, hIncompatible, hMeet⟩ :=
    exists_pure_meeting_incompatible_family
  have hND : IsNowhereDense N :=
    SMTree.incompatible_family_isNowhereDense
      markerMonoid N hIncompatible freeAncestral_hasLateProperGaps
  let Z : Set ExampleMap := closure N
  let O : Set ExampleMap := Zᶜ
  have hOpenDense : IsOpen O ∧ Dense O := by
    change IsOpen (closure N)ᶜ ∧ Dense (closure N)ᶜ
    exact isClosed_isNowhereDense_iff_compl.mp
      ⟨isClosed_closure, hND.closure⟩
  refine ⟨O, hOpenDense.1, hOpenDense.2, ?_⟩
  intro H
  obtain ⟨F, hFN, hFRed, hFRoot⟩ := hMeet H
  let a : SMTree.RamseyApprox markerMonoid 1 :=
    SMTree.ramseyApprox markerMonoid 1 F
  have hOpenBasic : IsOpen
      ((SMTree.ramseyApproximationSystem markerMonoid).neighborhood
        (n := 1) a H.val) :=
    (SMTree.ramseyApproximationSystem markerMonoid).isOpen_neighborhood
      (n := 1) a H.val
  have hNonemptyBasic :
      ((SMTree.ramseyApproximationSystem markerMonoid).neighborhood
        (n := 1) a H.val).Nonempty := by
    exact ⟨F, hFRed, rfl⟩
  obtain ⟨Y, hYBasic, hYO⟩ :=
    hOpenDense.2.inter_open_nonempty _ hOpenBasic hNonemptyBasic
  have hYApprox :
      SMTree.ramseyApprox markerMonoid 1 Y =
        SMTree.ramseyApprox markerMonoid 1 F := hYBasic.2
  have hYRest := congrArg Subtype.val hYApprox
  change Y.restrictLe markerMonoid 0 =
    F.restrictLe markerMonoid 0 at hYRest
  have hYRoot : Y (rootNode (Label := Unit) (arity := 1)) =
      markedFirstNode := by
    have hEval := congrFun hYRest
      (⟨rootNode (Label := Unit) (arity := 1), by decide⟩ :
        SMTree.InitialNode (Node Unit 1) 0)
    exact hEval.trans hFRoot
  refine ⟨?_, ?_⟩
  · exact ⟨Y, ⟨hYBasic.1, hYRoot⟩, hYO⟩
  · have hFZ : F ∈ Z := subset_closure hFN
    exact ⟨F, ⟨hFRed, hFRoot⟩, hFZ⟩

end SuccessorTree.Counterexample

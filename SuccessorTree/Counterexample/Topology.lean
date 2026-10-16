import SuccessorTree.Counterexample.NowhereDense
import RamseySpace.Ellentuck
import Mathlib.Topology.GDelta.Basic

/-!
# Right-incompatible families are nowhere dense in the direct Ellentuck topology

This theorem converts the proved *local escape* lemma into the genuine
topological assertion. The topology is that of the **direct M-map
approximation system**, not the separate fat-tree topology.

No application of the (false) direct shape-map Ellentuck theorem is made.
-/

namespace SuccessorTree.SMTree

universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

/-- Under late proper gaps, every family of pairwise incompatible
right-composition maps is nowhere dense in the *actual direct monoid
Ellentuck topology*. -/
theorem incompatible_family_isNowhereDense
    (H : SMTree S) (N : Set (MMap H))
    (hN : PairwiseRightIncompatible H N)
    (hGap : HasLateProperGaps H) :
    @IsNowhereDense (MMap H)
      (ramseyApproximationSystem H).ellentuckTopology N := by
  -- Lean sees the same point type both through the SMTree and the
  -- approximation-system projection. Register the chosen topology in
  -- both syntactic forms to make all closure/open-set expressions infer.
  letI : TopologicalSpace (MMap H) :=
    (ramseyApproximationSystem H).ellentuckTopology
  letI : TopologicalSpace (ramseyApproximationSystem H).Point :=
    (ramseyApproximationSystem H).ellentuckTopology
  change interior (closure N) = (∅ : Set (MMap H))
  apply Set.eq_empty_of_subset_empty
  intro x hx
  let U : Set (MMap H) := interior (closure N)
  have hOpen : (ramseyApproximationSystem H).IsEllentuckOpen U := by
    have hIsOpen :
        @IsOpen (MMap H)
          (ramseyApproximationSystem H).ellentuckTopology U := by
      exact isOpen_interior
    exact ((ramseyApproximationSystem H).isOpen_ellentuck_iff U).mp hIsOpen
  obtain ⟨n, a, B, hxAB, hsub⟩ := hOpen hx
  let a1 : RamseyApprox H (n + 1) := ramseyApprox H (n + 1) x
  have hne : ((ramseyApproximationSystem H).neighborhood (n := n + 1) a1 x).Nonempty := by
    exact ⟨x, H.ramseyReduction_refl x, rfl⟩
  obtain ⟨G, hGne, hGsub, hGdis⟩ :=
    H.incompatible_family_local_escape N hN hGap a1 x hne
  obtain ⟨y, hy⟩ := hGne
  have hyx : y ∈ (ramseyApproximationSystem H).neighborhood (n := n + 1) a1 x := hGsub hy
  have hyAB : y ∈ (ramseyApproximationSystem H).neighborhood (n := n) a B := by
    have hprefix : (ramseyApproximationSystem H).approx n y = (ramseyApproximationSystem H).approx n x :=
      (ramseyApproximationSystem H).coherent hyx.2 n (Nat.lt_succ_self n)
    exact ⟨(ramseyApproximationSystem H).le_trans hyx.1 hxAB.1, hprefix.trans hxAB.2⟩
  have hyClosed : y ∈ closure N := interior_subset (hsub hyAB)
  have hopenG : IsOpen ((ramseyApproximationSystem H).neighborhood (n := n + 1) a1 G) :=
    (ramseyApproximationSystem H).isOpen_neighborhood (n := n + 1) a1 G
  obtain ⟨z, hzG, hzN⟩ :=
    (mem_closure_iff.mp hyClosed)
      ((ramseyApproximationSystem H).neighborhood (n := n + 1) a1 G) hopenG hy
  have hzempty : z ∈ (∅ : Set (MMap H)) :=
    (disjoint_iff_inf_le.mp hGdis) ⟨hzG, hzN⟩
  exact False.elim hzempty

end SuccessorTree.SMTree

namespace SuccessorTree.FreeAncestral

/-- An antichain of free-ancestral shape maps, if supplied, is
automatically nowhere dense in the correct shape-map monoid topology. -/
theorem freeAncestral_incompatible_isNowhereDense
    (N : Set (SMTree.MMap
      (freeSMTree (Label := Unit) (arity := 1))))
    (hN : SMTree.PairwiseRightIncompatible
      (freeSMTree (Label := Unit) (arity := 1)) N) :
    @IsNowhereDense
      (SMTree.MMap (freeSMTree (Label := Unit) (arity := 1)))
      ((SMTree.ramseyApproximationSystem
        (freeSMTree (Label := Unit) (arity := 1))).ellentuckTopology)
      N :=
  SMTree.incompatible_family_isNowhereDense _
    N hN freeAncestral_hasLateProperGaps

end SuccessorTree.FreeAncestral

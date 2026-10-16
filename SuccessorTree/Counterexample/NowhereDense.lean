import SuccessorTree.RamseySpace.Basic
import SuccessorTree.FreeAncestralSMTree
import Mathlib.Tactic

/-!
# Algebraic incompatibility and local Ellentuck escape

The final topological step of the shape-map Ellentuck counterexample
needs no special property of the free tree except **late proper gaps**.

These theorems concern the actual right-composition reduction of M-maps.
They do not use geometric fat-tree reductions, A.3(2), or a hypothetical
abstract Ellentuck theorem for the direct M-map space.

Companion English proof:
\`docs/theorem111-zfc-counterexample-20261016.md\`.
-/

namespace SuccessorTree.SMTree

universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

/-- Two maps are compatible if they have a common algebraic right
multiple. Distinct members of the counterexample antichain will
be incompatible in this precise sense. -/
def RightCompatible (H : SMTree S) (F G : MMap H) : Prop :=
  ∃ K : MMap H, RamseyReduction H K F ∧ RamseyReduction H K G

/-- Antichain formulation avoiding any reliance on an antisymmetric
reduction order (the order is generally only a quasi-order). -/
def PairwiseRightIncompatible (H : SMTree S) (N : Set (MMap H)) : Prop :=
  ∀ ⦃F G : MMap H⦄, F ∈ N → G ∈ N →
    RightCompatible H F G → F = G

/-- The only geometric input needed for the nowhere-density proof:
we can insert a target-level gap beyond any fixed initial segment. -/
def HasLateProperGaps (H : SMTree S) : Prop :=
  ∀ n : Nat, ∃ D : MMap H,
    (∀ x : T, LevelTree.lev x ≤ n → D x = x) ∧
    ¬ Function.Surjective (fun x : T => D x)

/-- No injective M-map can factor through its own composition
with a map omitting a target point. This argument does not assume
that the reduction preorder is antisymmetric. -/
theorem not_reduction_self_comp_of_not_surjective
    (H : SMTree S) (K D : MMap H)
    (hD : ¬ Function.Surjective (fun x : T => D x)) :
    ¬ RamseyReduction H K (MMap.comp H K D) := by
  rintro ⟨E, hE⟩
  apply hD
  intro x
  refine ⟨E x, ?_⟩
  apply K.map.injective
  exact (hE x).symm

/-- **Local escape lemma.** Any nonempty basic right-composition
neighborhood admits a nonempty smaller neighborhood missing a
pairwise incompatible family, provided proper gaps can be inserted
after every finite source segment.

This is the substantive topological argument establishing that
the antichain constructed later is nowhere dense. -/
theorem incompatible_family_local_escape
    (H : SMTree S) (N : Set (MMap H))
    (hN : PairwiseRightIncompatible H N)
    (hGap : HasLateProperGaps H)
    {n : Nat} (a : RamseyApprox H (n + 1)) (F : MMap H)
    (hne : ((ramseyApproximationSystem H).neighborhood a F).Nonempty) :
    ∃ G : MMap H,
      ((ramseyApproximationSystem H).neighborhood a G).Nonempty ∧
      (ramseyApproximationSystem H).neighborhood a G ⊆
        (ramseyApproximationSystem H).neighborhood a F ∧
      Disjoint ((ramseyApproximationSystem H).neighborhood a G) N := by
  classical
  let R := ramseyApproximationSystem H
  by_cases hdis : Disjoint (R.neighborhood a F) N
  · exact ⟨F, hne, Set.Subset.rfl, hdis⟩
  · have hmeet : ∃ K : MMap H, K ∈ R.neighborhood a F ∧ K ∈ N := by
      by_contra hm
      apply hdis
      rw [Set.disjoint_left]
      intro K hKF hKN
      exact hm ⟨K, hKF, hKN⟩
    obtain ⟨K, hKF, hKN⟩ := hmeet
    rcases hGap n with ⟨D, hDfix, hDsurj⟩
    let G : MMap H := MMap.comp H K D
    have hGF : RamseyReduction H G F :=
      H.ramseyReduction_trans
        (⟨D, fun _ => rfl⟩ : RamseyReduction H G K) hKF.1
    have hGapprox : ramseyApprox H (n + 1) G = a := by
      apply Subtype.ext
      have hKa : K.restrictLe H n = a.1 :=
        congrArg Subtype.val hKF.2
      calc
        G.restrictLe H n = K.restrictLe H n := by
          funext x
          change K (D x.1) = K x.1
          rw [hDfix x.1 x.2]
        _ = a.1 := hKa
    refine ⟨G, ?_, ?_, ?_⟩
    · exact ⟨G, H.ramseyReduction_refl G, hGapprox⟩
    · intro J hJG
      exact ⟨H.ramseyReduction_trans hJG.1 hGF, hJG.2⟩
    · rw [Set.disjoint_left]
      intro J hJG hJN
      have hJK : RamseyReduction H J K :=
        H.ramseyReduction_trans hJG.1
          (⟨D, fun _ => rfl⟩ : RamseyReduction H G K)
      have hJKeq : J = K :=
        hN hJN hKN ⟨J, H.ramseyReduction_refl J, hJK⟩
      have hKG : RamseyReduction H K G := by
        simpa [hJKeq] using hJG.1
      exact (H.not_reduction_self_comp_of_not_surjective
        K D hDsurj) hKG

end SuccessorTree.SMTree

namespace SuccessorTree.FreeAncestral

/-- Proper one-gap maps exist above every protected initial segment
in the *verified* full free-ancestral M1--M3 monoid. -/
theorem freeAncestral_hasLateProperGaps :
    SMTree.HasLateProperGaps
      (freeSMTree (Label := Unit) (arity := 1)) := by
  intro n
  let m : Nat := n + 1
  let choice : History Unit 1 m → Code Unit 1 m :=
    fun _ => ⟨(), emptyParamTuple 1 m⟩
  let D : SMTree.MMap (freeSMTree (Label := Unit) (arity := 1)) :=
    ⟨oneGapShapeMap m choice, by simp [freeSMTree]⟩
  refine ⟨D, ?_, ?_⟩
  · intro x hx
    change gapNode m choice x = x
    exact gapNode_eq_self_of_lt m choice (by dsimp [m]; omega)
  · intro hsurj
    obtain ⟨x, hx⟩ :=
      hsurj (canonicalNode (Label := Unit) (arity := 1) m)
    have hlevel : (gapNode m choice x).level = m := by
      have hc := congrArg Node.level hx
      simpa [D, oneGapShapeMap_apply] using hc
    rw [gapNode_level] at hlevel
    by_cases hlt : x.level < m
    · rw [gapLevel_of_lt hlt] at hlevel
      omega
    · rw [gapLevel_of_ge (Nat.le_of_not_gt hlt)] at hlevel
      omega

end SuccessorTree.FreeAncestral

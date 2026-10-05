import SuccessorTree.FatTree.RamseyFinitization
import SuccessorTree.FatTree.Amalgamation
import RamseySpace.Axioms

/-!
# Typed A3 interface for the fat-tree Ramsey space

This file translates the concrete stem/depth-cone amalgamation lemmas into
the typed `RamseySpace.ApproximationSystem` interface.  No A4 or topological
Ramsey theorem is used.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

private noncomputable def S0 := approximationSystem H

/-- Abstract basic-neighborhood membership is exactly the manuscript's
concrete fat-tree neighborhood predicate. -/
theorem mem_neighborhood_iff_inNeighborhood
    {n : Nat} (a : (S0 H).Approx n)
    (U W : FatTree H) :
    W ∈ (S0 H).neighborhood a U ↔
      InNeighborhood H a.1 U W := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    apply extendsStem_of_initialSegment_eq H
    have ha := congrArg Subtype.val h.2
    change W.initialSegment H n = a.1 at ha
    simpa [a.2] using ha
  · intro h
    refine ⟨h.1, ?_⟩
    apply Subtype.ext
    have hs := initialSegment_eq_of_extendsStem H h.2
    change W.initialSegment H n = a.1
    simpa [a.2] using hs

/-- Todorčević A3(1) in the typed approximation-system interface. -/
theorem typed_amalgamation_nonempty
    {n : Nat} (a : (S0 H).Approx n)
    (B : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a B d)
    ⦃A : FatTree H⦄
    (hA : A ∈ (S0 H).levelNeighborhood d B) :
    ((S0 H).neighborhood a A).Nonempty := by
  have hxB : StemAt H a.1 B d :=
    (hasDepth_iff_stemAt H a B).1 hd
  have hcone : InDepthCone H d B A :=
    (mem_levelNeighborhood_iff_depthCone H d B A).1 hA
  obtain ⟨W, hW⟩ := a3_one_nonempty H hxB hcone
  refine ⟨W, ?_⟩
  exact (mem_neighborhood_iff_inNeighborhood H a A W).2 hW

/-- Todorčević's standard A3(2) in the typed approximation-system interface. -/
theorem typed_amalgamation_refine_standard
    {n : Nat} (a : (S0 H).Approx n)
    (B : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a B d)
    {A : FatTree H}
    (hA : A ∈ (S0 H).neighborhood a B) :
    ∃ A', A' ∈ (S0 H).levelNeighborhood d B ∧
      (S0 H).neighborhood a A' ⊆
        (S0 H).neighborhood a A := by
  have hxB : StemAt H a.1 B d :=
    (hasDepth_iff_stemAt H a B).1 hd
  have hconcreteA : InNeighborhood H a.1 B A :=
    (mem_neighborhood_iff_inNeighborhood H a B A).1 hA
  have hne :
      ∃ W : FatTree H, InNeighborhood H a.1 A W := by
    exact ⟨A, FatTree.reduces_refl H A, hconcreteA.2⟩
  obtain ⟨m, A', hxm, hdepth, hne', hsub⟩ :=
    a3_two_amalgamation H hconcreteA.1 hne
  have hmd : m = d :=
    stemAt_unique H hxm hxB
  subst m
  refine ⟨A',
    (mem_levelNeighborhood_iff_depthCone H d B A').2 hdepth,
    ?_⟩
  intro W hW
  have hWc : InNeighborhood H a.1 A' W :=
    (mem_neighborhood_iff_inNeighborhood H a A' W).1 hW
  exact (mem_neighborhood_iff_inNeighborhood H a A W).2
    (hsub W hWc)

end FatTree
end SMTree
end SuccessorTree

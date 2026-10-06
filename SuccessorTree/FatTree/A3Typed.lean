import SuccessorTree.FatTree.RamseyFinitization
import SuccessorTree.FatTree.Amalgamation

/-!
# Typed A3 interface for the fat-tree Ramsey space

Translate the concrete amalgamation lemmas into the approximation-system
interface. The published A3(2) follows directly from the same splice used
in the manuscript; the basic-member version is a consequence.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- Abstract basic-neighborhood membership is exactly the manuscript's
concrete fat-tree neighborhood predicate. -/
theorem mem_neighborhood_iff_inNeighborhood
    {n : Nat} (a : (approximationSystem H).Approx n)
    (U W : FatTree H) :
    W ∈ (approximationSystem H).neighborhood a U ↔
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
    {n : Nat} (a : (approximationSystem H).Approx n)
    (B : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a B d)
    ⦃A : FatTree H⦄
    (hA : A ∈ (approximationSystem H).levelNeighborhood d B) :
    ((approximationSystem H).neighborhood a A).Nonempty := by
  have hxB : StemAt H a.1 B d :=
    (hasDepth_iff_stemAt H a B).1 hd
  have hcone : InDepthCone H d B A :=
    (mem_levelNeighborhood_iff_depthCone H d B A).1 hA
  obtain ⟨W, hW⟩ := a3_one_nonempty H hxB hcone
  exact ⟨W, (mem_neighborhood_iff_inNeighborhood H a A W).2 hW⟩

/-- Todorčević's printed A3(2), including nonemptiness of the refined
neighborhood, obtained directly from the concrete amalgamation theorem. -/
theorem typed_amalgamation_refine_published
    {n : Nat} (a : (approximationSystem H).Approx n)
    (B : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a B d)
    {A : FatTree H} (hAB : (approximationSystem H).le A B)
    (hne : ((approximationSystem H).neighborhood a A).Nonempty) :
    ∃ A', A' ∈ (approximationSystem H).levelNeighborhood d B ∧
      ((approximationSystem H).neighborhood a A').Nonempty ∧
      (approximationSystem H).neighborhood a A' ⊆
        (approximationSystem H).neighborhood a A := by
  obtain ⟨W, hW⟩ := hne
  obtain ⟨m, A', hm, hdepth, ⟨X, hX⟩, hsub⟩ :=
    a3_two_amalgamation H hAB
      ⟨W, (mem_neighborhood_iff_inNeighborhood H a A W).1 hW⟩
  have hmd : m = d :=
    stemAt_unique H hm ((hasDepth_iff_stemAt H a B).1 hd)
  subst m
  refine ⟨A', (mem_levelNeighborhood_iff_depthCone H d B A').2 hdepth,
    ⟨X, (mem_neighborhood_iff_inNeighborhood H a A' X).2 hX⟩, ?_⟩
  intro W hW
  exact (mem_neighborhood_iff_inNeighborhood H a A W).2
    (hsub W ((mem_neighborhood_iff_inNeighborhood H a A' W).1 hW))

/-- The basic-member special case of A3(2). -/
theorem typed_amalgamation_refine_standard
    {n : Nat} (a : (approximationSystem H).Approx n)
    (B : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a B d)
    {A : FatTree H}
    (hA : A ∈ (approximationSystem H).neighborhood a B) :
    ∃ A', A' ∈ (approximationSystem H).levelNeighborhood d B ∧
      (approximationSystem H).neighborhood a A' ⊆
        (approximationSystem H).neighborhood a A := by
  have hne : ((approximationSystem H).neighborhood a A).Nonempty :=
    ⟨A, (approximationSystem H).le_refl A, hA.2⟩
  obtain ⟨A', hA'B, _, hsub⟩ :=
    typed_amalgamation_refine_published H a B hd hA.1 hne
  exact ⟨A', hA'B, hsub⟩

end FatTree
end SMTree
end SuccessorTree

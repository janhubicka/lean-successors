import SuccessorTree.FatTree.A3Typed
import SuccessorTree.FatTree.CanonicalMap
import SuccessorTree.RamseySpace.Ellentuck

/-!
# Transfer of Ellentuck amalgamation from fat trees to shape maps

This is the formal version of the manuscript's regular-tree transfer proof.

Write pi(U) = F_U for the canonical shape map of a fat tree, and pi_n(y) for
its finite canonical approximation.  The transfer uses exactly three facts:

* every shape map has a fat widening (surjectivity of pi);
* abstract depth is preserved by the widening;
* basic neighborhoods are exact images:
      pi[[y,U]] = [pi_n(y), pi(U)].

The last item packages the hereditary quotient / relative-widening argument
used for regular word trees.  From these three facts, fat-tree A3(2)
immediately gives the optional shape-map amalgamation (EA).  Combining this
with the independently checked shape A1/A2/A4/closedness yields the full
shape-preserving Ellentuck theorem.

The unrestricted successor-tree setting need not satisfy these transfer
hypotheses; this file therefore does not reintroduce the false general
projection theorem.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Exact structural data needed to transfer fat basic neighborhoods to the
shape-preserving map space. -/
structure FatShapeEllentuckTransfer (H : SMTree S) : Prop where
  surjective :
    Function.Surjective (FatTree.canonicalMap H)
  depth_exact :
    ∀ {n : Nat} (x : FatTree.ExactApprox H n)
      (U : FatTree H) (d : Nat),
      (FatTree.finitization H).HasDepth x U d ↔
        (ramseyFinitization H).HasDepth
          (FatTree.exactCanonicalApprox H x)
          (FatTree.canonicalMap H U) d
  basic_exact :
    ∀ {n : Nat} (x : FatTree.ExactApprox H n)
      (U : FatTree H) (G : MMap H),
      G ∈ (ramseyApproximationSystem H).neighborhood
          (FatTree.exactCanonicalApprox H x)
          (FatTree.canonicalMap H U) ↔
        ∃ V : FatTree H,
          V ∈ (FatTree.approximationSystem H).neighborhood x U ∧
          FatTree.canonicalMap H V = G

namespace FatShapeEllentuckTransfer

variable (H : SMTree S)
variable (Q : FatShapeEllentuckTransfer H)

/-- The exact basic-neighborhood correspondence sends a fat depth cone to
the corresponding shape depth cone. -/
theorem levelNeighborhood_forward
    (d : Nat) (U V : FatTree H)
    (hVU :
      V ∈ (FatTree.approximationSystem H).levelNeighborhood d U) :
    FatTree.canonicalMap H V ∈
      (ramseyApproximationSystem H).levelNeighborhood d
        (FatTree.canonicalMap H U) := by
  have hfat :
      V ∈ (FatTree.approximationSystem H).neighborhood
        (FatTree.exactApprox H d U) U := hVU
  have hshape :=
    (Q.basic_exact (FatTree.exactApprox H d U) U
      (FatTree.canonicalMap H V)).2
      ⟨V, hfat, rfl⟩
  have happrox :=
    FatTree.exactCanonicalApprox_exactApprox H U d
  simpa only [happrox] using hshape

/-- The exact fat-to-shape correspondence supplies Todorčević A3(2) in the
shape map space.  This is the core of the Ellentuck transfer proof. -/
theorem shapeAmalgamation
    : ShapeEllentuckAmalgamation H := by
  intro n a B d hd A hA

  obtain ⟨U, hU⟩ := Q.surjective B
  obtain ⟨V0, hV0⟩ := Q.surjective A
  let x : FatTree.ExactApprox H n := FatTree.exactApprox H n V0

  have hxproj :
      FatTree.exactCanonicalApprox H x = a := by
    calc
      FatTree.exactCanonicalApprox H x =
          ramseyApprox H n (FatTree.canonicalMap H V0) := by
        exact FatTree.exactCanonicalApprox_exactApprox H V0 n
      _ = ramseyApprox H n A := by
        rw [hV0]
      _ = a := hA.2

  have hAproj :
      A ∈ (ramseyApproximationSystem H).neighborhood
          (FatTree.exactCanonicalApprox H x)
          (FatTree.canonicalMap H U) := by
    simpa only [hxproj, hU] using hA

  obtain ⟨V, hVxU, hVproj⟩ :=
    (Q.basic_exact x U A).1 hAproj

  have hshapeDepth :
      (ramseyFinitization H).HasDepth
        (FatTree.exactCanonicalApprox H x)
        (FatTree.canonicalMap H U) d := by
    simpa only [hxproj, hU] using hd
  have hfatDepth :
      (FatTree.finitization H).HasDepth x U d :=
    (Q.depth_exact x U d).2 hshapeDepth

  obtain ⟨W, hWUd, hsub⟩ :=
    FatTree.typed_amalgamation_refine_standard H x U hfatDepth hVxU

  let A' : MMap H := FatTree.canonicalMap H W
  have hA'B :
      A' ∈ (ramseyApproximationSystem H).levelNeighborhood d B := by
    have hlevel := Q.levelNeighborhood_forward d U W hWUd
    simpa only [A', hU] using hlevel

  refine ⟨A', hA'B, ?_⟩
  intro G hGaA'

  have hGproj :
      G ∈ (ramseyApproximationSystem H).neighborhood
          (FatTree.exactCanonicalApprox H x)
          (FatTree.canonicalMap H W) := by
    simpa only [A', hxproj] using hGaA'

  obtain ⟨Z, hZxW, hZproj⟩ :=
    (Q.basic_exact x W G).1 hGproj
  have hZxV := hsub hZxW
  have hshapeV :=
    (Q.basic_exact x V (FatTree.canonicalMap H Z)).2
      ⟨Z, hZxV, rfl⟩

  have htarget :
      G ∈ (ramseyApproximationSystem H).neighborhood a A := by
    simpa only [hZproj, hxproj, hVproj] using hshapeV
  exact htarget

/-- Consequently the shape-preserving map space satisfies the optional
Ellentuck amalgamation hypothesis. -/
theorem normalizedEA :
    ShapeNormalizedEA H := by
  apply normalized_of_shapeEllentuckAmalgamation H
  exact Q.shapeAmalgamation H

/-- Shape-preserving Ellentuck theorem transferred from the fat-tree
neighborhood geometry. -/
theorem shapeEllentuck_from_fatTree :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := ramseyApproximationSystem H) :=
  shapeEllentuck H (Q.shapeAmalgamation H)

end FatShapeEllentuckTransfer

end SMTree
end SuccessorTree

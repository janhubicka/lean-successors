import SuccessorTree.Counterexample.MarkerTransfer
import Mathlib.Tactic

/-!
# Meeting image levels of two compatible shape maps

This module isolates the purely algebraic half of the counterexample's
decisive compatibility lemma. Common right-composition multiples force
infinitely many image levels of H to be retained by G; this does not
use the root-marker construction or the fat-tree topology.

The *separate* rigidity argument forces this fixed infinite set
inside the marked support A. The resulting almost-disjoint uniqueness
is already proved abstractly in SupportRigidity.
-/

namespace SuccessorTree.FreeAncestral

/-- A level j of the inner H-coordinate meets the range of the
level map of G after applying H. -/
def MeetingLevels (G H : SMTree.MMap markerMonoid) : Set Nat :=
  {j | ∃ k, markerMonoid.levelMap H.map j =
    markerMonoid.levelMap G.map k}

/-- Any common right multiple of G and H∘Q gives an actual equality
of total shape maps G∘R = H∘Q∘S. -/
theorem compatible_outer_factor
    (G H Q : SMTree.MMap markerMonoid)
    (hc : SMTree.RightCompatible markerMonoid G
      (SMTree.MMap.comp markerMonoid H Q)) :
    ∃ (R S : SMTree.MMap markerMonoid),
      SMTree.MMap.comp markerMonoid G R =
        SMTree.MMap.comp markerMonoid H
          (SMTree.MMap.comp markerMonoid Q S) := by
  obtain ⟨C, ⟨R, hR⟩, ⟨S, hS⟩⟩ := hc
  refine ⟨R, S, ?_⟩
  apply SMTree.MMap.ext_apply
  intro x
  change G (R x) = H (Q (S x))
  calc
    G (R x) = C x := (hR x).symm
    _ = (SMTree.MMap.comp markerMonoid H Q) (S x) := hS x
    _ = H (Q (S x)) := rfl

/-- An equality G∘R = H∘Q∘S already gives infinitely many meeting
levels between G and H, witnessed by the strictly increasing range
of the numerical level map Q∘S. -/
theorem meetingLevels_infinite_of_common_multiple
    (G H Q R S : SMTree.MMap markerMonoid)
    (heq : SMTree.MMap.comp markerMonoid G R =
      SMTree.MMap.comp markerMonoid H
        (SMTree.MMap.comp markerMonoid Q S)) :
    (MeetingLevels G H).Infinite := by
  let f : Nat → Nat := fun n =>
    markerMonoid.levelMap Q.map (markerMonoid.levelMap S.map n)
  have hstrict : StrictMono f :=
    (markerMonoid.levelMap_strictMono Q.map).comp
      (markerMonoid.levelMap_strictMono S.map)
  have hinfinite : (Set.range f).Infinite :=
    Set.infinite_range_of_injective hstrict.injective
  apply hinfinite.mono
  intro j hj
  rcases hj with ⟨n, rfl⟩
  refine ⟨markerMonoid.levelMap R.map n, ?_⟩
  have hmap := congrArg
    (fun F : SMTree.MMap markerMonoid =>
      markerMonoid.levelMap F.map n) heq
  simp only [SMTree.MMap.levelMap_comp] at hmap
  exact hmap.symm

/-- The fixed witness set D^H_G used to distinguish almost-disjoint
supports is always infinite whenever G and H∘Q share a right multiple. -/
theorem meetingLevels_infinite_of_compatible
    (G H Q : SMTree.MMap markerMonoid)
    (hc : SMTree.RightCompatible markerMonoid G
      (SMTree.MMap.comp markerMonoid H Q)) :
    (MeetingLevels G H).Infinite := by
  obtain ⟨R, S, hRS⟩ := compatible_outer_factor G H Q hc
  exact meetingLevels_infinite_of_common_multiple G H Q R S hRS

end SuccessorTree.FreeAncestral

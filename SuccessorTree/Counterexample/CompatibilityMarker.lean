import SuccessorTree.Counterexample.CompatibilityLevels
import SuccessorTree.RamseySpace.Finitization
import Mathlib.Tactic

/-!
# The concrete root-marker compatibility obstruction

This is the central mathematical lemma for the ZFC counterexample to
shape-map Ellentuck Theorem 1.11. It combines:

* Every common right multiple has infinitely many meeting image levels;
* Q_A marks each target level omitted by its prescribed level range;
* root-fixing outer maps preserve those markers;
* no G which maps the original root above level zero has a marker after
  a retained image level.

Thus, if G is compatible with H∘Q_A, the *fixed* infinite set
D_G^H of meeting levels must lie inside the retained level range of Q_A.

No direct A.3(2), non-validated transfer lemma, new axioms or admissions.
-/

namespace SuccessorTree.FreeAncestral

/-- Every monoid shape map weakly increases the level of each node. -/
theorem mmap_level_ge_self
    (F : SMTree.MMap markerMonoid) (x : Node Unit 1) :
    x.level ≤ (F x).level := by
  calc
    x.level ≤ markerMonoid.levelMap F.map x.level :=
      markerMonoid.levelMap_id_le F.map x.level
    _ = (F x).level := markerMonoid.levelMap_eq F.map (a := x)

/-- Any map fixing the original root has level-map value zero at zero. -/
theorem root_fixed_levelMap_zero
    (H : SMTree.MMap markerMonoid)
    (hfix : H (rootNode (Label := Unit) (arity := 1)) =
      rootNode (Label := Unit) (arity := 1)) :
    markerMonoid.levelMap H.map 0 = 0 := by
  have h := markerMonoid.levelMap_eq H.map
    (a := rootNode (Label := Unit) (arity := 1))
  change markerMonoid.levelMap H.map 0 =
    (H (rootNode (Label := Unit) (arity := 1))).level at h
  rw [hfix] at h
  exact h

/-- The decisive support inclusion: any meeting H-coordinate level
with G is retained by the marked inner map Q_A, provided G maps the
root to a positive level and H fixes the root. -/
theorem meetingLevels_subset_marked_range
    (levels : Nat → Nat) (mono : StrictMono levels)
    (hroot : levels 0 = 1)
    (G H : SMTree.MMap markerMonoid)
    (hgroot : 0 < (G (rootNode (Label := Unit) (arity := 1))).level)
    (hhroot : H (rootNode (Label := Unit) (arity := 1)) =
      rootNode (Label := Unit) (arity := 1))
    (hc : SMTree.RightCompatible markerMonoid G
      (SMTree.MMap.comp markerMonoid H
        (markedFusion levels mono hroot))) :
    MeetingLevels G H ⊆ Set.range levels := by
  obtain ⟨R, S, heq⟩ :=
    compatible_outer_factor G H (markedFusion levels mono hroot) hc
  intro j hj
  obtain ⟨k, hjk⟩ := hj
  by_contra hskip
  have hGpositive : 0 < markerMonoid.levelMap G.map k := by
    have hk0 := (markerMonoid.levelMap_strictMono G.map).monotone
      (Nat.zero_le k)
    have hg0 : 0 < markerMonoid.levelMap G.map 0 := by
      have h := markerMonoid.levelMap_eq G.map
        (a := rootNode (Label := Unit) (arity := 1))
      change markerMonoid.levelMap G.map 0 =
        (G (rootNode (Label := Unit) (arity := 1))).level at h
      rw [h]
      exact hgroot
    omega
  have hjpos : 1 ≤ j := by
    by_contra hjz
    have heq0 : j = 0 := by omega
    have hH0 := root_fixed_levelMap_zero H hhroot
    rw [heq0, hH0] at hjk
    omega
  obtain ⟨n, hQmarker⟩ :=
    markedFusion_skipped_level levels mono hroot j hjpos hskip
  let high : Nat := max (k + 1) (n + 1)
  let x : Node Unit 1 :=
    canonicalNode (Label := Unit) (arity := 1) high
  have hRhigh : k + 1 ≤ (R x).level := by
    have hle : k + 1 ≤ x.level := by
      change k + 1 ≤ high
      exact Nat.le_max_left _ _
    exact hle.trans (mmap_level_ge_self R x)
  have hShigh : n + 1 ≤ (S x).level := by
    have hle : n + 1 ≤ x.level := by
      change n + 1 ≤ high
      exact Nat.le_max_right _ _
    exact hle.trans (mmap_level_ge_self S x)
  have hQ : HasRootMarkerAt
      (markedFusion levels mono hroot (S x)) j :=
    hQmarker (S x) hShigh
  have hHmark : HasRootMarkerAt
      (H (markedFusion levels mono hroot (S x)))
      (markerMonoid.levelMap G.map k) := by
    rw [← hjk]
    exact root_marker_transported H.map hhroot _ j hQ
  have heqX : G (R x) = H (markedFusion levels mono hroot (S x)) := by
    have h := congrArg
      (fun F : SMTree.MMap markerMonoid => F x) heq
    exact h
  rw [← heqX] at hHmark
  let b : Node Unit 1 :=
    LevelTree.ancestor (R x) (k + 1) (by exact hRhigh)
  have hbLevel : b.level = k + 1 := by
    change LevelTree.lev (LevelTree.ancestor (R x) (k + 1) hRhigh) = k + 1
    exact LevelTree.level_ancestor _ _ _
  have hbR : b ≤ R x := LevelTree.ancestor_le _ _ _
  let a : Node Unit 1 :=
    LevelTree.ancestor b k (by
      change k ≤ b.level
      omega)
  have haLevel : a.level = k := by
    change LevelTree.lev a = k
    exact LevelTree.level_ancestor b k _
  have hab : a ≤ b := LevelTree.ancestor_le _ _ _
  have hcover : a ⋖ b := by
    apply LevelTree.covBy_of_le_level_succ hab
    change b.level = a.level + 1
    omega
  obtain ⟨p, c, hstep⟩ := freeSucc_s3 hcover
  have hNo : ¬HasRootMarkerAt
      (G (R x)) (markerMonoid.levelMap G.map k) := by
    have hNo' := retained_level_avoids_root
      G.map hgroot hstep hbR
    have haImageLevel :
        (G a).level = markerMonoid.levelMap G.map k := by
      calc
        (G a).level = markerMonoid.levelMap G.map a.level := by
          exact (markerMonoid.levelMap_eq G.map (a := a)).symm
        _ = markerMonoid.levelMap G.map k := by rw [haLevel]
    rwa [haImageLevel] at hNo'
  exact hNo hHmark

/-- The exact infinite-support compatibility lemma asserted in the
counterexample note: the fixed infinite set D^H_G is included in the
retained support of the marked map. -/
theorem compatible_marked_has_infinite_support
    (levels : Nat → Nat) (mono : StrictMono levels)
    (hroot : levels 0 = 1)
    (G H : SMTree.MMap markerMonoid)
    (hgroot : 0 < (G (rootNode (Label := Unit) (arity := 1))).level)
    (hhroot : H (rootNode (Label := Unit) (arity := 1)) =
      rootNode (Label := Unit) (arity := 1))
    (hc : SMTree.RightCompatible markerMonoid G
      (SMTree.MMap.comp markerMonoid H
        (markedFusion levels mono hroot))) :
    (MeetingLevels G H).Infinite ∧
      MeetingLevels G H ⊆ Set.range levels :=
  ⟨meetingLevels_infinite_of_compatible
      G H (markedFusion levels mono hroot) hc,
    meetingLevels_subset_marked_range
      levels mono hroot G H hgroot hhroot hc⟩

end SuccessorTree.FreeAncestral

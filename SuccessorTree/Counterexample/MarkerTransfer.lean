import SuccessorTree.Counterexample.MarkerIntervals
import Mathlib.Tactic

/-!
# Shape-map transport of marked outgoing levels

Every source root-marker edge survives a shape map fixing the root.
This remains true when the map inserts arbitrary target levels.
The quantified statement below uses exactly the *level map of the
verified M1--M3 monoid*.

We also supply the elementary order-theoretic bracketing lemma
locating any omitted level between consecutive retained levels.
-/

namespace SuccessorTree.FreeAncestral

/-- A root-marked target level m of x is transported to the
corresponding target level of H(x), provided H fixes the original
root. No \`A.3(2)\` or any monoid Ellentuck theorem is assumed. -/
theorem root_marker_transported
    (H : ShapeMap (freeSTree (Label := Unit) (arity := 1)))
    (hroot : H (rootNode (Label := Unit) (arity := 1)) =
      rootNode (Label := Unit) (arity := 1))
    (x : Node Unit 1) (m : Nat)
    (hm : HasRootMarkerAt x m) :
    HasRootMarkerAt (H x) (markerMonoid.levelMap H m) := by
  obtain ⟨b, hbx, hbLevel, hbMarked⟩ := hm
  have hmle : m ≤ b.level := by omega
  let a : Node Unit 1 := LevelTree.ancestor b m hmle
  have haLevel : a.level = m :=
    LevelTree.level_ancestor b m hmle
  have hab : a ≤ b := LevelTree.ancestor_le b m hmle
  have hcov : a ⋖ b := by
    apply LevelTree.covBy_of_le_level_succ hab
    change b.level = a.level + 1
    omega
  obtain ⟨p, c, hstep⟩ := freeSucc_s3 hcov
  have htransport :
      HasRootMarkerAt (H x) (H a).level :=
    root_marker_transported_from_code H hroot hstep hbMarked hbx
  have hLevel :
      (H a).level = markerMonoid.levelMap H m := by
    calc
      (H a).level = markerMonoid.levelMap H a.level := by
        exact (markerMonoid.levelMap_eq H (a := a)).symm
      _ = markerMonoid.levelMap H m := by rw [haLevel]
  rwa [hLevel] at htransport

/-- Every level at or beyond the first retained level lies between
two consecutive retained levels of a strictly increasing sequence.
In particular, this holds for every omitted level of Q_A. -/
theorem retained_levels_bracket
    (levels : Nat → Nat) (mono : StrictMono levels)
    (m : Nat) (hfirst : levels 0 ≤ m) :
    ∃ n : Nat, levels n ≤ m ∧ m < levels (n + 1) := by
  have hbound : ∀ n : Nat, n ≤ levels n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        have hs := mono (Nat.lt_succ_self n)
        omega
  have hex : ∃ k : Nat, m < levels k := by
    refine ⟨m + 1, ?_⟩
    have hb := hbound (m + 1)
    omega
  let k : Nat := Nat.find hex
  have hk : m < levels k := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra hkpos
    have hkzero : k = 0 := by omega
    rw [hkzero] at hk
    omega
  let n : Nat := k - 1
  have hsmall : ¬m < levels n := Nat.find_min hex (by
    dsimp [n]
    omega)
  refine ⟨n, Nat.le_of_not_gt hsmall, ?_⟩
  have hnk : n + 1 = k := by dsimp [n]; omega
  simpa only [hnk] using hk

/-- The particular Q_A map has a root marker at any omitted target
level m >= 2, along the image of every sufficiently high source node.
The height threshold is supplied by the bracketing witness. -/
theorem markedFusion_skipped_level
    (levels : Nat → Nat) (mono : StrictMono levels)
    (hroot : levels 0 = 1)
    (m : Nat) (hm : 1 ≤ m)
    (hskip : m ∉ Set.range levels) :
    ∃ n : Nat, ∀ (x : Node Unit 1),
      n + 1 ≤ x.level →
        HasRootMarkerAt (markedFusion levels mono hroot x) m := by
  obtain ⟨n, hleft, hright⟩ :=
    retained_levels_bracket levels mono m (by simpa [hroot] using hm)
  have hne : levels n ≠ m := by
    intro heq
    exact hskip ⟨n, heq⟩
  have hlow : levels n + 1 ≤ m := by omega
  exact ⟨n, fun x hx =>
    markedFusion_root_interval levels mono hroot n x hx m hlow hright⟩

end SuccessorTree.FreeAncestral

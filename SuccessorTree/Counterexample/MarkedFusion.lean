import SuccessorTree.Counterexample.StretchHistory
import Mathlib.Tactic

/-!
# Marked maps as fusion of verified one-gap shape maps

This is an alternative construction of the all-level counterexample map Q_A:
use the already proved one-gap shape maps, insert a one-parameter root
marker at every omitted target level, and take their pointwise fusion.

Unlike a direct proof that a raw recursive history map is injective and
preserves weak successors, this approach **inherits** those properties
from the verified \`oneGapShapeMap\` and \`ShapeMap.fusionLimit\` theorems.
The finite stages and gap blocks are separate reusable M-map operations.
-/

namespace SuccessorTree.FreeAncestral

noncomputable def markerMonoid :
    SMTree (freeSTree (Label := Unit) (arity := 1)) :=
  freeSMTree (Label := Unit) (arity := 1)

/-- Insert one gap whose new outgoing edge uses the original root as
its unique ancestral parameter. This gap must be above level zero. -/
noncomputable def markerGap (m : Nat) (hm : 0 < m) :
    SMTree.MMap markerMonoid :=
  ⟨oneGapShapeMap m (fun _ => rootMarkerCode m hm),
    by simp [markerMonoid, freeSMTree]⟩

@[simp] theorem markerGap_apply (m : Nat) (hm : 0 < m)
    (x : Node Unit 1) :
    markerGap m hm x =
      gapNode m (fun _ => rootMarkerCode m hm) x := rfl

theorem markerGap_fixes_below (m : Nat) (hm : 0 < m)
    (x : Node Unit 1) (hx : x.level < m) :
    markerGap m hm x = x := by
  rw [markerGap_apply]
  exact gapNode_eq_self_of_lt m (fun _ => rootMarkerCode m hm) hx

theorem markerGap_level (m : Nat) (hm : 0 < m)
    (x : Node Unit 1) :
    (markerGap m hm x).level =
      if x.level < m then x.level else x.level + 1 := by
  rw [markerGap_apply, gapNode_level]
  rfl

/-- Insert an empty successor at the original root, so mandatory
parameters thereafter cannot refer to target level zero. -/
noncomputable def initialRootGap : SMTree.MMap markerMonoid :=
  ⟨oneGapShapeMap 0 (fun _ => initialEmptyCode),
    by simp [markerMonoid, freeSMTree]⟩

theorem initialRootGap_level (x : Node Unit 1) :
    (initialRootGap x).level = x.level + 1 := by
  change (gapNode 0 (fun _ => initialEmptyCode) x).level =
    x.level + 1
  exact gapNode_level_of_ge 0 (fun _ => initialEmptyCode)
    (Nat.zero_le _)

/-- Insert root-marker gaps at consecutive target levels
\`start, start+1, ..., start+k-1\`, composing in this precise
order. The block is itself a fully verified M-map. -/
noncomputable def markerBlock (start : Nat) (hs : 0 < start) :
    Nat → SMTree.MMap markerMonoid
  | 0 => SMTree.MMap.id markerMonoid
  | k + 1 =>
      SMTree.MMap.comp markerMonoid
        (markerGap (start + k) (by omega))
        (markerBlock start hs k)

/-- Every block fixes nodes below its first skipped level. -/
theorem markerBlock_fixes_below (start : Nat) (hs : 0 < start) :
    ∀ (k : Nat) (x : Node Unit 1),
      x.level < start → markerBlock start hs k x = x
  | 0, _, _ => rfl
  | k + 1, x, hx => by
      change markerGap (start + k) _ (markerBlock start hs k x) = x
      rw [markerBlock_fixes_below start hs k x hx]
      exact markerGap_fixes_below (start + k) (by omega) x (by omega)

/-- Every block shifts each node at or above its starting level by
exactly its number of inserted gaps. -/
theorem markerBlock_level_above (start : Nat) (hs : 0 < start) :
    ∀ (k : Nat) (x : Node Unit 1),
      start ≤ x.level →
        (markerBlock start hs k x).level = x.level + k
  | 0, _, _ => rfl
  | k + 1, x, hx => by
      change
        (markerGap (start + k) _
          (markerBlock start hs k x)).level = x.level + (k + 1)
      rw [markerGap_level]
      have hprev := markerBlock_level_above start hs k x hx
      have hnot :
          ¬ (markerBlock start hs k x).level < start + k := by
        omega
      simp only [if_neg hnot]
      omega

/-- The n-th finite stage inserts the root gap, then all skipped
levels up to the n-th *retained* target level. Its action agrees with
the desired limit on source levels at most n. -/
noncomputable def markedStage
    (levels : Nat → Nat) (mono : StrictMono levels)
    (hroot : levels 0 = 1) :
    Nat → SMTree.MMap markerMonoid
  | 0 => initialRootGap
  | n + 1 =>
      SMTree.MMap.comp markerMonoid
        (markerBlock (levels n + 1) (by
            have hm := mono (Nat.lt_succ_self n)
            omega)
          (levels (n + 1) - (levels n + 1)))
        (markedStage levels mono hroot n)


/-- The level function of each finite stage: retained levels through
stage n agree with the target sequence; all later source levels are
shifted by a constant until the next block is inserted. -/
theorem markedStage_level
    (levels : Nat → Nat) (mono : StrictMono levels)
    (hroot : levels 0 = 1) :
    ∀ (n : Nat) (x : Node Unit 1),
      (markedStage levels mono hroot n x).level =
        if x.level ≤ n then levels x.level
        else levels n + (x.level - n) := by
  intro n
  induction n with
  | zero =>
      intro x
      change (initialRootGap x).level =
        (if x.level ≤ 0 then levels x.level
         else levels 0 + (x.level - 0))
      rw [initialRootGap_level]
      by_cases hx : x.level = 0
      · simp [hx, hroot]
      · have hp : 0 < x.level := Nat.pos_of_ne_zero hx
        have hn : ¬x.level ≤ 0 := by omega
        simp [hn, hroot]
        omega
  | succ n ih =>
      intro x
      let start : Nat := levels n + 1
      let length : Nat := levels (n + 1) - start
      have hmono : start ≤ levels (n + 1) := by
        dsimp [start]
        exact mono (Nat.lt_succ_self n)
      have hstart : 0 < start := by dsimp [start]; omega
      change
        (markerBlock start hstart length
          (markedStage levels mono hroot n x)).level =
        (if x.level ≤ n + 1 then levels x.level
         else levels (n + 1) + (x.level - (n + 1)))
      by_cases hx : x.level ≤ n
      · have hprevious :
            (markedStage levels mono hroot n x).level =
              levels x.level := by
          simpa [hx] using ih x
        have hbelow :
            (markedStage levels mono hroot n x).level < start := by
          rw [hprevious]
          have hlev := mono.monotone hx
          dsimp [start]
          omega
        rw [markerBlock_fixes_below start hstart length _ hbelow, hprevious]
        simp [Nat.le_trans hx (Nat.le_succ n)]
      · have hprevious :
            (markedStage levels mono hroot n x).level =
              levels n + (x.level - n) := by
          simpa [hx] using ih x
        have hge :
            start ≤ (markedStage levels mono hroot n x).level := by
          rw [hprevious]
          dsimp [start]
          omega
        rw [markerBlock_level_above start hstart length _ hge, hprevious]
        by_cases heq : x.level = n + 1
        · simp [heq, length, start]
          omega
        · have hgt : n + 1 < x.level := by omega
          have hn : ¬ x.level ≤ n + 1 := by omega
          simp [hn, length, start]
          omega

/-- Stage n already stabilizes its source levels ≤ n; consequently
the stage sequence meets exactly the verified M1 fusion-stability
hypothesis. -/
theorem markedStage_fusionStable
    (levels : Nat → Nat) (mono : StrictMono levels)
    (hroot : levels 0 = 1) :
    ShapeMap.FusionStable
      (fun n => (markedStage levels mono hroot n).map) := by
  intro n x hx
  change x.level ≤ n at hx
  have hprevious :
      (markedStage levels mono hroot n x).level =
        levels x.level := by
    simpa [hx] using markedStage_level levels mono hroot n x
  have hbelow :
      (markedStage levels mono hroot n x).level <
        levels n + 1 := by
    rw [hprevious]
    have hlevels := mono.monotone hx
    omega
  change
    markedStage levels mono hroot n x =
      markerBlock (levels n + 1) _
        (levels (n + 1) - (levels n + 1))
        (markedStage levels mono hroot n x)
  exact (markerBlock_fixes_below _ _ _ _ hbelow).symm

/-- The complete marked map Q_A, obtained from *verified*
one-gap shape maps by an honest M1 fusion. -/
noncomputable def markedFusion
    (levels : Nat → Nat) (mono : StrictMono levels)
    (hroot : levels 0 = 1) :
    SMTree.MMap markerMonoid :=
  ⟨ShapeMap.fusionLimit
      (fun n => (markedStage levels mono hroot n).map)
      (markedStage_fusionStable levels mono hroot),
    by simp [markerMonoid, freeSMTree]⟩

/-- Image levels of the complete fusion are precisely the supplied
strictly increasing sequence. -/
theorem markedFusion_level
    (levels : Nat → Nat) (mono : StrictMono levels)
    (hroot : levels 0 = 1) (x : Node Unit 1) :
    (markedFusion levels mono hroot x).level = levels x.level := by
  change
    (markedStage levels mono hroot x.level x).level = levels x.level
  simpa using markedStage_level levels mono hroot x.level x

/-- The original root is mapped to the empty-parameter node at level one. -/
theorem markedFusion_root
    (levels : Nat → Nat) (mono : StrictMono levels)
    (hroot : levels 0 = 1) :
    markedFusion levels mono hroot (rootNode (Label := Unit) (arity := 1)) =
      (⟨1, History.step History.root initialEmptyCode⟩ : Node Unit 1) := by
  change initialRootGap (rootNode (Label := Unit) (arity := 1)) =
    (⟨1, History.step History.root initialEmptyCode⟩ : Node Unit 1)
  change gapNode 0 (fun _ => initialEmptyCode)
    (⟨0, History.root⟩ : Node Unit 1) = _
  rw [gapNode_at_level]
  rfl

end SuccessorTree.FreeAncestral

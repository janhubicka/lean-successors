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

private noncomputable def markerMonoid :
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

end SuccessorTree.FreeAncestral

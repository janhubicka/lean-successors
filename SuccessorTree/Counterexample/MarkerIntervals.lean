import SuccessorTree.Counterexample.MarkedFusion
import SuccessorTree.Counterexample.RootMarkerTransport
import Mathlib.Tactic

/-!
# Every omitted image level carries a persistent root marker

We now prove the **specific Q_A half** of the counterexample's
compatibility obstruction. One-gap maps insert a root marker at their
omitted target level; a block of consecutive gaps retains all
previously inserted markers because each later gap extends its input
node. The fusion therefore preserves the markers below the next
retained target level.

A root-fixing outer map transports this marker by the weak successor
condition (proved separately in RootMarkerTransport).
-/

namespace SuccessorTree.FreeAncestral

/-- At its omitted target level m, a marker gap appends an immediate
successor to every source node of level m. -/
theorem markerGap_extends_at_level (m : Nat) (hm : 0 < m)
    (x : Node Unit 1) (hx : x.level = m) :
    x ≤ markerGap m hm x := by
  rcases x with ⟨n, h⟩
  change n = m at hx
  subst n
  change (⟨m, h⟩ : Node Unit 1) ≤
    gapNode m (fun _ => rootMarkerCode m hm) ⟨m, h⟩
  rw [gapNode_at_level]
  exact base_le_child _ _ _

/-- The new outgoing edge has exactly the root marker as its
intrinsic ancestral parameter. -/
theorem markerGap_has_root_at_level (m : Nat) (hm : 0 < m)
    (x : Node Unit 1) (hx : x.level = m) :
    HasRootMarkerAt (markerGap m hm x) m := by
  refine ⟨markerGap m hm x, le_rfl, ?_, ?_⟩
  · rw [markerGap_level, hx]
    simp
  · rcases x with ⟨n, h⟩
    change n = m at hx
    subst n
    change 0 ∈ lastParamLevelsNode
      (gapNode m (fun _ => rootMarkerCode m hm) ⟨m, h⟩)
    rw [gapNode_at_level]
    change 0 ∈ levelList (rootMarkerCode m hm).params
    exact rootMarkerCode_has_root m hm

/-- A block of k consecutive root-marker gaps marks *every*
target level in [start,start+k), when its input lies at level
start. -/
theorem markerBlock_root_interval (start : Nat) (hs : 0 < start) :
    ∀ (k : Nat) (x : Node Unit 1),
      x.level = start →
      ∀ (m : Nat), start ≤ m → m < start + k →
        HasRootMarkerAt (markerBlock start hs k x) m := by
  intro k
  induction k with
  | zero =>
      intro x hx m hm hlt
      omega
  | succ k ih =>
      intro x hx m hm hlt
      let prev : Node Unit 1 := markerBlock start hs k x
      have hprevLevel : prev.level = start + k := by
        dsimp [prev]
        rw [markerBlock_level_above start hs k x (by omega)]
        omega
      have hprevLe : prev ≤ markerGap (start + k) (by omega) prev :=
        markerGap_extends_at_level (start + k) (by omega) prev hprevLevel
      change HasRootMarkerAt
        (markerGap (start + k) _
          (markerBlock start hs k x)) m
      by_cases hmk : m < start + k
      · have hbefore :
            HasRootMarkerAt prev m :=
          ih x hx m hm hmk
        exact hbefore.mono hprevLe
      · have heq : m = start + k := by omega
        subst m
        exact markerGap_has_root_at_level (start + k) (by omega)
          prev hprevLevel

/-- Immediately after finishing the block between retained levels
levels n and levels(n+1), all skipped levels in this interval have
the root marker on each image node of source level n+1. -/
theorem markedStage_root_interval
    (levels : Nat → Nat) (mono : StrictMono levels)
    (hroot : levels 0 = 1)
    (n : Nat) (x : Node Unit 1) (hx : x.level = n + 1)
    (m : Nat) (hlo : levels n + 1 ≤ m)
    (hhi : m < levels (n + 1)) :
    HasRootMarkerAt (markedStage levels mono hroot (n + 1) x) m := by
  let start : Nat := levels n + 1
  have hs : 0 < start := by dsimp [start]; omega
  let length : Nat := levels (n + 1) - start
  let prev : Node Unit 1 := markedStage levels mono hroot n x
  have hprev : prev.level = start := by
    dsimp [prev, start]
    rw [markedStage_level]
    have hn : ¬ x.level ≤ n := by omega
    simp [hn, hx]
  have hlen : levels (n + 1) = start + length := by
    dsimp [start, length]
    have hm := mono (Nat.lt_succ_self n)
    omega
  change HasRootMarkerAt (markerBlock start hs length prev) m
  exact markerBlock_root_interval start hs length prev
    hprev m (by simpa [start] using hlo) (by omega)

/-- In the *completed M1-fusion shape map*, every target level
strictly between two consecutive retained levels is root-marked
along the image of every sufficiently high source node. -/
theorem markedFusion_root_interval
    (levels : Nat → Nat) (mono : StrictMono levels)
    (hroot : levels 0 = 1)
    (n : Nat) (x : Node Unit 1) (hx : n + 1 ≤ x.level)
    (m : Nat) (hlo : levels n + 1 ≤ m)
    (hhi : m < levels (n + 1)) :
    HasRootMarkerAt (markedFusion levels mono hroot x) m := by
  let v : Node Unit 1 :=
    LevelTree.ancestor x (n + 1) (by exact hx)
  have hvlev : v.level = n + 1 := by
    change LevelTree.lev (LevelTree.ancestor x (n + 1) hx) = n + 1
    exact LevelTree.level_ancestor x (n + 1) hx
  have hvx : v ≤ x := LevelTree.ancestor_le _ _ _
  have hstage := markedStage_root_interval levels mono hroot
    n v hvlev m hlo hhi
  have hfusion :
      markedFusion levels mono hroot v =
        markedStage levels mono hroot (n + 1) v := by
    change
      ShapeMap.fusionLimit
        (fun i => (markedStage levels mono hroot i).map)
        (markedStage_fusionStable levels mono hroot) v =
      (markedStage levels mono hroot (n + 1)).map v
    exact ShapeMap.fusionLimit_eq_stage
      (fun i => (markedStage levels mono hroot i).map)
      (markedStage_fusionStable levels mono hroot)
      (by change v.level ≤ n + 1; omega)
  have hmono :
      markedFusion levels mono hroot v ≤
        markedFusion levels mono hroot x :=
    (markedFusion levels mono hroot).map.map_le_of_le hvx
  rw [← hfusion] at hstage
  exact hstage.mono hmono

end SuccessorTree.FreeAncestral

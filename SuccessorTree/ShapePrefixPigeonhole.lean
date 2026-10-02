import SuccessorTree.ShapePigeonhole
import SuccessorTree.ShapeFusion

/-!
# The one-dimensional pigeonhole below an arbitrary finite shape prefix

A finite approximation a of depth d+1 in B has a finite factor whose top
source level lands exactly on target level d.  Canonically extend that factor;
its next source level then lands on d+1.  We can therefore run the verified
M3 replay at local level d+1 and transport the resulting line through the
canonical factor and the outer map B.

This is the direct shape-preserving replacement for the fat-tree restatement
of Lemma 3.1.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- The canonical total extension of a finite depth factor. -/
noncomputable def prefixCanonical
    (H : SMTree S)
    {n d : Nat}
    {a : RamseyApprox H (n + 1)}
    {B : MMap H}
    (hd : (ramseyFinitization H).HasDepth (n := n + 1) a B (d + 1)) :
    MMap H := by
  let fac : RamseyFiniteFactor H a (ramseyApprox H (d + 1) B) :=
    Classical.choice hd.1
  exact H.canonicalExtension fac.map n

/-- The canonical factor hits level d at the end of the prescribed prefix. -/
theorem prefixCanonical_level
    (H : SMTree S)
    {n d : Nat}
    {a : RamseyApprox H (n + 1)}
    {B : MMap H}
    (hd : (ramseyFinitization H).HasDepth (n := n + 1) a B (d + 1)) :
    H.levelMap (H.prefixCanonical hd).map n = d := by
  let fac : RamseyFiniteFactor H a (ramseyApprox H (d + 1) B) :=
    Classical.choice hd.1
  have htop : H.levelMap fac.map.map n = d :=
    H.ramseyFiniteFactor_topLevel_of_depth hd fac
  change H.levelMap (H.canonicalExtension fac.map n).map n = d
  rw [H.canonicalExtension_level_at_prefix fac.map n]
  exact htop

/-- The next canonical source level lands on the next target level d+1. -/
theorem prefixCanonical_level_succ
    (H : SMTree S)
    {n d : Nat}
    {a : RamseyApprox H (n + 1)}
    {B : MMap H}
    (hd : (ramseyFinitization H).HasDepth (n := n + 1) a B (d + 1)) :
    H.levelMap (H.prefixCanonical hd).map (n + 1) = d + 1 := by
  rw [H.canonicalExtension_level_succ]
  · rw [H.prefixCanonical_level hd]
  · exact le_rfl

/-- Every point in the one-step source domain is sent inside the local replay
domain through level d+1. -/
theorem prefixCanonical_bound_succ
    (H : SMTree S)
    {n d : Nat}
    {a : RamseyApprox H (n + 1)}
    {B : MMap H}
    (hd : (ramseyFinitization H).HasDepth (n := n + 1) a B (d + 1))
    (x : T) (hx : LevelTree.lev x ≤ n + 1) :
    LevelTree.lev (H.prefixCanonical hd x) ≤ d + 1 := by
  calc
    LevelTree.lev (H.prefixCanonical hd x) =
        H.levelMap (H.prefixCanonical hd).map (LevelTree.lev x) :=
      (H.levelMap_eq (H.prefixCanonical hd).map (a := x)).symm
    _ ≤ H.levelMap (H.prefixCanonical hd).map (n + 1) :=
      (H.levelMap_strictMono (H.prefixCanonical hd).map).monotone hx
    _ = d + 1 := H.prefixCanonical_level_succ hd

/-- On the old prefix itself the canonical factor lands strictly below the
local replay level d+1. -/
theorem prefixCanonical_bound_prefix
    (H : SMTree S)
    {n d : Nat}
    {a : RamseyApprox H (n + 1)}
    {B : MMap H}
    (hd : (ramseyFinitization H).HasDepth (n := n + 1) a B (d + 1))
    (x : T) (hx : LevelTree.lev x ≤ n) :
    LevelTree.lev (H.prefixCanonical hd x) < d + 1 := by
  calc
    LevelTree.lev (H.prefixCanonical hd x) =
        H.levelMap (H.prefixCanonical hd).map (LevelTree.lev x) :=
      (H.levelMap_eq (H.prefixCanonical hd).map (a := x)).symm
    _ ≤ H.levelMap (H.prefixCanonical hd).map n :=
      (H.levelMap_strictMono (H.prefixCanonical hd).map).monotone hx
    _ = d := H.prefixCanonical_level hd
    _ < d + 1 := Nat.lt_succ_self d

/-- The total local input map: identity for the base point, or one one-level
letter. -/
def localInputMMap
    (H : SMTree S) (m : Nat) :
    LineInput (OneLevelLetter H m) → MMap H
  | .base => MMap.id H
  | .letter e => e.toMMap

theorem localInputMMap_fixesBelow
    (H : SMTree S) (m : Nat)
    (x : LineInput (OneLevelLetter H m)) :
    (localInputMMap H m x).FixesBelow H m := by
  cases x with
  | base =>
      exact MMap.id_fixesBelow H m
  | letter e =>
      intro z hz
      exact e.eq_id_below H hz

/-- Global finite approximation obtained by transporting a local word through
the canonical factor and then through the outer map B. -/
noncomputable def prefixWordApprox
    (H : SMTree S)
    {n d : Nat}
    {a : RamseyApprox H (n + 1)}
    {B : MMap H}
    (hd : (ramseyFinitization H).HasDepth (n := n + 1) a B (d + 1))
    (w : List (OneLevelLetter H (d + 1))) :
    RamseyApprox H (n + 2) :=
  ramseyApprox H (n + 2)
    (MMap.comp H B
      (MMap.comp H (wordMap H (d + 1) w)
        (H.prefixCanonical hd)))

/-- Global line member produced by a replay block at the local target level. -/
noncomputable def prefixReplayApply
    (H : SMTree S)
    {n d : Nat}
    {a : RamseyApprox H (n + 1)}
    {B : MMap H}
    (hd : (ramseyFinitization H).HasDepth (n := n + 1) a B (d + 1))
    (R : ReplayBlock H (d + 1))
    (x : LineInput (OneLevelLetter H (d + 1))) :
    RamseyApprox H (n + 2) :=
  ramseyApprox H (n + 2)
    (MMap.comp H B
      (MMap.comp H R.toMMap
        (MMap.comp H (localInputMMap H (d + 1) x)
          (H.prefixCanonical hd))))

/-- M3 replay transported through an arbitrary finite prefix. -/
noncomputable def prefixReplaySystem
    (H : SMTree S)
    {n d : Nat}
    {a : RamseyApprox H (n + 1)}
    {B : MMap H}
    (hd : (ramseyFinitization H).HasDepth (n := n + 1) a B (d + 1)) :
    ReplaySystem
      (OneLevelLetter H (d + 1))
      (RamseyApprox H (n + 2))
      (ReplayBlock H (d + 1)) where
  wordApprox := H.prefixWordApprox hd
  apply := H.prefixReplayApply hd
  replay := fun L hs => H.replayBlock L hs
  replay_base := by
    intro L hs
    apply Subtype.ext
    funext y
    let z : {z : T // LevelTree.lev z ≤ d + 1} :=
      ⟨H.prefixCanonical hd y.1,
        H.prefixCanonical_bound_succ hd y.1 (by omega)⟩
    have hraw := congrFun
      ((H.replaySystem (d + 1)).replay_base L hs) z
    change
      B ((H.replayBlock L hs).toMMap (H.prefixCanonical hd y.1)) =
        B (wordMap H (d + 1) L.star (H.prefixCanonical hd y.1))
    exact congrArg B hraw
  replay_letter := by
    intro L hs e
    apply Subtype.ext
    funext y
    let z : {z : T // LevelTree.lev z ≤ d + 1} :=
      ⟨H.prefixCanonical hd y.1,
        H.prefixCanonical_bound_succ hd y.1 (by omega)⟩
    have hraw := congrFun
      ((H.replaySystem (d + 1)).replay_letter L hs e) z
    change
      B ((H.replayBlock L hs).toMMap
        (e.toMMap (H.prefixCanonical hd y.1))) =
        B (wordMap H (d + 1) (L.eval e)
          (H.prefixCanonical hd y.1))
    exact congrArg B hraw

/-- The refinement of B obtained from a transported replay line. -/
def prefixReplayRefinement
    (H : SMTree S)
    {d : Nat} (B : MMap H)
    (R : ReplayBlock H (d + 1)) :
    MMap H :=
  MMap.comp H B R.toMMap

theorem prefixReplayRefinement_mem
    (H : SMTree S)
    {d : Nat} (B : MMap H)
    (R : ReplayBlock H (d + 1)) :
    H.prefixReplayRefinement B R ∈
      (ramseyApproximationSystem H).levelNeighborhood (d + 1) B := by
  apply H.fusionStep_mem_levelNeighborhood
  exact ⟨R.toMMap, R.fixesBelow, rfl⟩

/-- The canonical factor still realizes the old finite approximation after
transport through B. -/
theorem prefixCanonical_realizes
    (H : SMTree S)
    {n d : Nat}
    {a : RamseyApprox H (n + 1)}
    {B : MMap H}
    (hd : (ramseyFinitization H).HasDepth (n := n + 1) a B (d + 1)) :
    ramseyApprox H (n + 1)
      (MMap.comp H B (H.prefixCanonical hd)) = a := by
  let fac : RamseyFiniteFactor H a (ramseyApprox H (d + 1) B) :=
    Classical.choice hd.1
  apply Subtype.ext
  funext y
  change B (H.prefixCanonical hd y.1) = a.1 y
  have hcan :
      H.prefixCanonical hd y.1 = fac.map y.1 := by
    change H.canonicalExtension fac.map n y.1 = fac.map y.1
    exact H.canonicalExtension_agrees fac.map n y.1 y.2
  rw [hcan]
  exact (fac.agrees y).symm

/-- Every transported replay member really is a one-step extension of the
chosen prefix below the replay refinement. -/
theorem prefixReplayApply_mem_oneStep
    (H : SMTree S)
    {n d : Nat}
    {a : RamseyApprox H (n + 1)}
    {B : MMap H}
    (hd : (ramseyFinitization H).HasDepth (n := n + 1) a B (d + 1))
    (R : ReplayBlock H (d + 1))
    (x : LineInput (OneLevelLetter H (d + 1))) :
    H.prefixReplayApply hd R x ∈
      (ramseyApproximationSystem H).oneStepApproximations a
        (H.prefixReplayRefinement B R) := by
  let G : MMap H := localInputMMap H (d + 1) x
  let C : MMap H := H.prefixCanonical hd
  let X : MMap H :=
    MMap.comp H B
      (MMap.comp H R.toMMap (MMap.comp H G C))
  refine ⟨X, ?_, rfl⟩
  constructor
  · refine ⟨MMap.comp H G C, ?_⟩
    intro y
    rfl
  · have hbase := H.prefixCanonical_realizes hd
    apply Subtype.ext
    funext y
    have hCy : LevelTree.lev (C y.1) < d + 1 := by
      exact H.prefixCanonical_bound_prefix hd y.1 y.2
    have hG : G (C y.1) = C y.1 := by
      exact H.localInputMMap_fixesBelow (d + 1) x (C y.1) hCy
    have hR : R.toMMap (C y.1) = C y.1 :=
      R.fixesBelow (C y.1) hCy
    have hbaseVal := congrArg Subtype.val hbase
    change
      (MMap.comp H B C).restrictLe H n = a.1 at hbaseVal
    have hy := congrFun hbaseVal y
    change B (R.toMMap (G (C y.1))) = a.1 y
    rw [hG, hR]
    exact hy

/-- Arbitrary-prefix one-dimensional pigeonhole: inside a depth-(d+1)
neighborhood we find an actual M3 line of one-step shape approximations on
which the given finite colouring is constant. -/
theorem prefixLinePigeonhole
    [Fintype κ]
    (H : SMTree S)
    {n d : Nat}
    (a : RamseyApprox H (n + 1))
    (B : MMap H)
    (hd : (ramseyFinitization H).HasDepth (n := n + 1) a B (d + 1))
    (colour : RamseyApprox H (n + 2) → κ) :
    ∃ R : ReplayBlock H (d + 1),
      H.prefixReplayRefinement B R ∈
        (ramseyApproximationSystem H).levelNeighborhood (d + 1) B ∧
      (∀ x : LineInput (OneLevelLetter H (d + 1)),
        H.prefixReplayApply hd R x ∈
          (ramseyApproximationSystem H).oneStepApproximations a
            (H.prefixReplayRefinement B R)) ∧
      (∀ x : LineInput (OneLevelLetter H (d + 1)),
        colour (H.prefixReplayApply hd R x) =
          colour (H.prefixReplayApply hd R LineInput.base)) := by
  obtain ⟨R, hmono⟩ :=
    (H.prefixReplaySystem hd).oneDimensionalPigeonhole_finite colour
  refine ⟨R, H.prefixReplayRefinement_mem B R, ?_, hmono⟩
  intro x
  exact H.prefixReplayApply_mem_oneStep hd R x

end SMTree
end SuccessorTree

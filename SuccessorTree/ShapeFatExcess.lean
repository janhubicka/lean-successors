import SuccessorTree.ShapeFatLine
import SuccessorTree.ShapeFirstSplit
import Mathlib.Tactic

/-!
# Excess induction on a fat block sequence

A nontrivial one-moving coordinate at cut c_i splits into its first local
letter and a tail fixing below c_i+1.  The tail transports across the
canonical i-th block to a coordinate at cut c_{i+1}.  Suffix decomposition
then expresses the original evaluation as one algebraic line, with excess
reduced by one.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Re-canonicalising a canonical block one source level later changes
nothing. -/
theorem FatBlockSeq.blockMap_canonical_next
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) :
    H.canonicalExtension (U.blockMap H i) (U.cut i + 1) =
      U.blockMap H i := by
  symm
  apply H.canonicalExtension_unique
    (U.blockMap H i) (U.blockMap H i) (U.cut i + 1)
  · intro x hx
    rfl
  · intro ell hell
    apply H.canonicalExtension_tail_mem_levelRange
      (U.seed i) (U.cut i) ell
    calc
      H.levelMap (U.seed i).map (U.cut i) =
          U.cut (i + 1) - 1 := U.seed_top i
      _ ≤ U.cut (i + 1) := by
        have hcut := U.cut_strict (Nat.lt_succ_self i)
        omega
      _ = H.levelMap (U.blockMap H i).map (U.cut i + 1) := by
        symm
        exact U.blockMap_level_next H i
      _ ≤ ell := hell

/-- Transport a tail coordinate across one canonical fat block. -/
theorem FatBlockSeq.exists_transport_after_block
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat)
    (s : MMap H)
    (hs : s.FixesBelow H (U.cut i + 1)) :
    ∃ t : MMap H,
      t.FixesBelow H (U.cut (i + 1)) ∧
      H.levelMap t.map (U.cut (i + 1)) =
        U.cut (i + 1) +
          (H.levelMap s.map (U.cut i + 1) - (U.cut i + 1)) ∧
      ∀ x : T, LevelTree.lev x ≤ U.cut i + 1 →
        U.blockMap H i (s x) = t (U.blockMap H i x) := by
  obtain ⟨t, htfix, htlev, htcomm⟩ :=
    H.exists_transport_across_canonical
      (U.blockMap H i) s (U.cut i + 1) hs
  refine ⟨t, ?_, ?_, ?_⟩
  · have hnext := U.blockMap_level_next H i
    simpa [hnext] using htfix
  · have hnext := U.blockMap_level_next H i
    simpa [hnext] using htlev
  · intro x hx
    have hcanon := U.blockMap_canonical_next H i
    have h := htcomm x hx
    rw [hcanon] at h
    exact h

/-- Excess of a one-moving coordinate above its frozen cut. -/
def AM.excess
    (H : SMTree S) {c : Nat}
    (r : AM H c 1) : Nat :=
  r.topLevel H - c

/-- Chosen transported tail map at the next cut. -/
noncomputable def FatBlockSeq.transportTailMap
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat)
    (s : MMap H)
    (hs : s.FixesBelow H (U.cut i + 1)) : MMap H :=
  Classical.choose (U.exists_transport_after_block H i s hs)

theorem FatBlockSeq.transportTailMap_spec
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat)
    (s : MMap H)
    (hs : s.FixesBelow H (U.cut i + 1)) :
    let t := U.transportTailMap H i s hs
    t.FixesBelow H (U.cut (i + 1)) ∧
      H.levelMap t.map (U.cut (i + 1)) =
        U.cut (i + 1) +
          (H.levelMap s.map (U.cut i + 1) - (U.cut i + 1)) ∧
      ∀ x : T, LevelTree.lev x ≤ U.cut i + 1 →
        U.blockMap H i (s x) = t (U.blockMap H i x) :=
  Classical.choose_spec (U.exists_transport_after_block H i s hs)

/-- The transported tail packaged as a one-moving coordinate at the next cut. -/
noncomputable def FatBlockSeq.transportTailAM
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat)
    (s : MMap H)
    (hs : s.FixesBelow H (U.cut i + 1)) :
    AM H (U.cut (i + 1)) 1 :=
  (U.transportTailMap H i s hs).toAM H (U.cut (i + 1)) 1
    (U.transportTailMap_spec H i s hs).1

theorem FatBlockSeq.transportTailAM_topLevel
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat)
    (s : MMap H)
    (hs : s.FixesBelow H (U.cut i + 1)) :
    (U.transportTailAM H i s hs).topLevel H =
      U.cut (i + 1) +
        (H.levelMap s.map (U.cut i + 1) - (U.cut i + 1)) := by
  rw [FatBlockSeq.transportTailAM, MMap.toAM_one_topLevel H]
  exact (U.transportTailMap_spec H i s hs).2.1

/-- Transporting the tail from a first-move split reduces excess by one. -/
theorem FatBlockSeq.transportFirstTail_excess
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat)
    (r : AM H (U.cut i) 1)
    (hmove : U.cut i < r.topLevel H) :
    (U.transportTailAM H i
      (H.firstMoveSplit r hmove).tail
      (H.firstMoveSplit r hmove).tail_fixes).excess H =
      r.excess H - 1 := by
  unfold AM.excess
  rw [U.transportTailAM_topLevel H i
    (H.firstMoveSplit r hmove).tail
    (H.firstMoveSplit r hmove).tail_fixes]
  rw [H.firstMoveSplit_tail_excess r hmove]
  omega


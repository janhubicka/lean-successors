import SuccessorTree.ShapeFatFusion
import Mathlib.Tactic

/-!
# Suffix limits of fat block sequences

For the direct shape-Ramsey proof we need the tail map carried by the blocks
starting at position i.  Its first block is u_i, and the total tail maps
satisfy exactly

  F_i = F_{i+1} o u_i^+.

This is the algebraic identity used in the excess induction.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Drop the first i blocks. -/
noncomputable def FatBlockSeq.tail
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) :
    FatBlockSeq H (U.cut i) where
  cut := fun j => U.cut (i + j)
  cut_zero := by simp
  cut_strict := by
    intro a b hab
    exact U.cut_strict (Nat.add_lt_add_left hab i)
  block := fun j => by
    simpa [Nat.add_assoc] using U.block (i + j)

@[simp] theorem FatBlockSeq.tail_cut
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i j : Nat) :
    (U.tail H i).cut j = U.cut (i + j) := rfl

theorem FatBlockSeq.tail_blockMap_zero
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) :
    (U.tail H i).blockMap H 0 = U.blockMap H i := by
  apply MMap.ext_apply
  intro x
  rfl

/-- The same original block appears at shifted indices in adjacent suffixes. -/
theorem FatBlockSeq.tail_blockMap_succ
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i k : Nat) :
    (U.tail H i).blockMap H (k + 1) =
      (U.tail H (i + 1)).blockMap H k := by
  apply MMap.ext_apply
  intro x
  simp [FatBlockSeq.blockMap, FatBlockSeq.tail,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Cumulative maps of a suffix are the corresponding segment compositions. -/
theorem FatBlockSeq.tail_cumulative_succ
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) :
    ∀ k : Nat,
      (U.tail H i).cumulative H (k + 1) =
        MMap.comp H
          ((U.tail H (i + 1)).cumulative H k)
          (U.blockMap H i) := by
  intro k
  induction k with
  | zero =>
      rw [FatBlockSeq.cumulative_succ,
        FatBlockSeq.cumulative_zero,
        U.tail_blockMap_zero H i]
      apply MMap.ext_apply
      intro x
      rfl
  | succ k ih =>
      rw [FatBlockSeq.cumulative_succ]
      rw [U.tail_blockMap_succ H i k]
      rw [ih]
      rw [FatBlockSeq.cumulative_succ]
      apply MMap.ext_apply
      intro x
      rfl

/-- The suffix limit agrees with the appropriate cumulative stage on a node
whose source level is k steps above the suffix base. -/
theorem FatBlockSeq.tail_limit_eq_cumulative
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i k : Nat)
    (x : T)
    (hx : LevelTree.lev x = U.cut i + k) :
    (U.tail H i).limit H x =
      (U.tail H i).cumulative H (k + 1) x := by
  unfold FatBlockSeq.limit
  rw [ShapeMap.fusionLimit_apply]
  unfold FatBlockSeq.fusionStage
  rw [hx]
  have hidx : U.cut i + k + 1 - U.cut i = k + 1 := by omega
  rw [hidx]

/-- Exact suffix decomposition. -/
theorem FatBlockSeq.tail_limit_decompose
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) :
    (U.tail H i).limit H =
      MMap.comp H
        ((U.tail H (i + 1)).limit H)
        (U.blockMap H i) := by
  apply MMap.ext_apply
  intro x
  by_cases hxlow : LevelTree.lev x < U.cut i
  · have hleft := (U.tail H i).limit_fixesBelow H x hxlow
    have hblock := U.blockMap_fixesBelow H i x hxlow
    have hnext :
        (U.tail H (i + 1)).limit H x = x := by
      apply (U.tail H (i + 1)).limit_fixesBelow H
      exact lt_trans hxlow (U.cut_strict (Nat.lt_succ_self i))
    change (U.tail H i).limit H x =
      (U.tail H (i + 1)).limit H (U.blockMap H i x)
    rw [hleft, hblock, hnext]
  · have hxge : U.cut i ≤ LevelTree.lev x := Nat.le_of_not_gt hxlow
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hxge
    have hx : LevelTree.lev x = U.cut i + k := hk
    cases k with
    | zero =>
        rw [U.tail_limit_eq_cumulative H i 0 x (by simpa using hx)]
        rw [U.tail_cumulative_succ H i 0]
        change
          (MMap.id H) (U.blockMap H i x) =
            (U.tail H (i + 1)).limit H (U.blockMap H i x)
        rw [MMap.id_apply]
        symm
        apply (U.tail H (i + 1)).limit_fixesBelow H
        have hlev :
            LevelTree.lev (U.blockMap H i x) =
              U.cut (i + 1) - 1 := by
          calc
            LevelTree.lev (U.blockMap H i x) =
                H.levelMap (U.blockMap H i).map (LevelTree.lev x) :=
              (H.levelMap_eq (U.blockMap H i).map (a := x)).symm
            _ = H.levelMap (U.blockMap H i).map (U.cut i) := by
              exact congrArg (H.levelMap (U.blockMap H i).map) hx
            _ = U.cut (i + 1) - 1 := U.blockMap_level_cut H i
        rw [hlev]
        change U.cut (i + 1) - 1 < U.cut (i + 1)
        have hcut := U.cut_strict (Nat.lt_succ_self i)
        omega
    | succ k =>
        have hx' : LevelTree.lev x = U.cut i + (k + 1) := by
          simpa using hx
        rw [U.tail_limit_eq_cumulative H i (k + 1) x hx']
        rw [U.tail_cumulative_succ H i (k + 1)]
        change
          (U.tail H (i + 1)).cumulative H (k + 1)
              (U.blockMap H i x) =
            (U.tail H (i + 1)).limit H (U.blockMap H i x)
        symm
        apply U.tail_limit_eq_cumulative H (i + 1) k
        calc
          LevelTree.lev (U.blockMap H i x) =
              H.levelMap (U.blockMap H i).map (LevelTree.lev x) :=
            (H.levelMap_eq (U.blockMap H i).map (a := x)).symm
          _ = H.levelMap (U.blockMap H i).map
                (U.cut i + (k + 1)) := by rw [hx']
          _ =
              H.levelMap
                (H.canonicalExtension
                  ((U.block i).1.representative H) (U.cut i)).map
                (U.cut i + (k + 1)) := by rfl
          _ =
              H.levelMap ((U.block i).1.representative H).map (U.cut i) +
                (k + 1) := by
            rw [H.canonicalExtension_level_tail
              ((U.block i).1.representative H) (U.cut i) (k + 1)]
          _ = (U.cut (i + 1) - 1) + (k + 1) := by
            have htop := (U.block i).2
            unfold AM.topLevel at htop
            rw [htop]
          _ = U.cut (i + 1) + k := by
            have hcut : U.cut i < U.cut (i + 1) :=
              U.cut_strict (Nat.lt_succ_self i)
            omega

end SMTree
end SuccessorTree

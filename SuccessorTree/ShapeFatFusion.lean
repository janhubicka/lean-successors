import SuccessorTree.ShapeWordFactor
import SuccessorTree.ShapeTransportAlphabet
import Mathlib.Tactic

/-!
# Minimal fat block sequences for the direct shape Ramsey theorem

This file contains only the block-sequence structure needed for the finite
shape-preserving Ramsey theorem. It does not introduce the fat-subtree
topology or Todorcevic neighborhoods.

A block from cut c_i to c_{i+1} is a one-moving approximation whose terminal
image level is c_{i+1}-1. Its canonical extension therefore sends the next
source level to c_{i+1}. Successive canonical block maps can be composed and
fused by M1.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Infinite sequence of one-moving blocks with strictly increasing cuts. -/
structure FatBlockSeq (H : SMTree S) (n : Nat) where
  cut : Nat → Nat
  cut_zero : cut 0 = n
  cut_strict : StrictMono cut
  block : ∀ i : Nat, AMExact H (cut i) (cut (i + 1) - 1)

/-- The canonical total map represented by one fat block. -/
noncomputable def FatBlockSeq.blockMap
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) : MMap H :=
  H.canonicalExtension (U.block i).1.representative H (U.cut i)

theorem FatBlockSeq.blockMap_fixesBelow
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) :
    (U.blockMap H i).FixesBelow H (U.cut i) := by
  intro x hx
  rw [FatBlockSeq.blockMap]
  rw [H.canonicalExtension_agrees
    ((U.block i).1.representative H) (U.cut i) x (Nat.le_of_lt hx)]
  exact (U.block i).1.representative_fixesBelow H x hx

/-- A block map sends its source cut to one below the next cut. -/
theorem FatBlockSeq.blockMap_level_cut
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) :
    H.levelMap (U.blockMap H i).map (U.cut i) =
      U.cut (i + 1) - 1 := by
  rw [FatBlockSeq.blockMap, H.canonicalExtension_level_at_prefix]
  exact (U.block i).2

/-- The canonical tail of a block hits the next cut on the next source level. -/
theorem FatBlockSeq.blockMap_level_next
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) :
    H.levelMap (U.blockMap H i).map (U.cut i + 1) =
      U.cut (i + 1) := by
  have hcut : U.cut i < U.cut (i + 1) :=
    U.cut_strict (Nat.lt_succ_self i)
  calc
    H.levelMap (U.blockMap H i).map (U.cut i + 1) =
        H.levelMap (U.blockMap H i).map (U.cut i) + 1 := by
      exact H.canonicalExtension_level_succ
        ((U.block i).1.representative H) (U.cut i) (U.cut i) le_rfl
    _ = (U.cut (i + 1) - 1) + 1 := by
      rw [U.blockMap_level_cut H i]
    _ = U.cut (i + 1) := by omega

/-- Cumulative composition of the first i fat blocks. -/
noncomputable def FatBlockSeq.cumulative
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) : Nat → MMap H
  | 0 => MMap.id H
  | i + 1 => MMap.comp H (U.blockMap H i) (U.cumulative H i)

@[simp] theorem FatBlockSeq.cumulative_zero
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) :
    U.cumulative H 0 = MMap.id H := rfl

@[simp] theorem FatBlockSeq.cumulative_succ
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) :
    U.cumulative H (i + 1) =
      MMap.comp H (U.blockMap H i) (U.cumulative H i) := rfl


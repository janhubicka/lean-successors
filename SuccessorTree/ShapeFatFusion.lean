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

/-- The terminal target level of a finite one-moving approximation built
from a total M-map is the terminal level of that total map. -/
theorem MMap.toAM_one_topLevel
    (H : SMTree S) (F : MMap H) (n : Nat)
    (hfix : F.FixesBelow H n) :
    (F.toAM H n 1 hfix).topLevel H = H.levelMap F.map n := by
  let a : AM H n 1 := F.toAM H n 1 hfix
  have htop := a.representative_top H
  have hval := congrArg Subtype.val htop
  change (a.representative H).restrictLe H n = F.restrictLe H n at hval
  obtain ⟨x, hx⟩ := H.level_nonempty n
  have hpoint := congrFun hval ⟨x, by simpa [hx]⟩
  unfold AM.topLevel
  calc
    H.levelMap (a.representative H).map n =
        LevelTree.lev (a.representative H x) := by
      simpa [hx] using H.levelMap_eq (a.representative H).map (a := x)
    _ = LevelTree.lev (F x) := congrArg LevelTree.lev hpoint
    _ = H.levelMap F.map n := by
      simpa [hx] using (H.levelMap_eq F.map (a := x)).symm

/-- Infinite sequence of one-moving blocks with strictly increasing cuts.

We store total M-map representatives rather than dependent finite subtypes.
This makes suffix reindexing literal; the finite exact block is derived only
when a colouring needs it. -/
structure FatBlockSeq (H : SMTree S) (n : Nat) where
  cut : Nat → Nat
  cut_zero : cut 0 = n
  cut_strict : StrictMono cut
  seed : Nat → MMap H
  seed_fixes : ∀ i : Nat, (seed i).FixesBelow H (cut i)
  seed_top :
    ∀ i : Nat, H.levelMap (seed i).map (cut i) = cut (i + 1) - 1

/-- The finite one-moving block carried by a seed. -/
noncomputable def FatBlockSeq.block
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) :
    AMExact H (U.cut i) (U.cut (i + 1) - 1) := by
  refine ⟨(U.seed i).toAM H (U.cut i) 1 (U.seed_fixes i), ?_⟩
  rw [MMap.toAM_one_topLevel H]
  exact U.seed_top i

/-- The canonical total map represented by one fat block. -/
noncomputable def FatBlockSeq.blockMap
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) : MMap H :=
  H.canonicalExtension (U.seed i) (U.cut i)

theorem FatBlockSeq.blockMap_fixesBelow
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) :
    (U.blockMap H i).FixesBelow H (U.cut i) := by
  intro x hx
  rw [FatBlockSeq.blockMap]
  rw [H.canonicalExtension_agrees
    (U.seed i) (U.cut i) x (Nat.le_of_lt hx)]
  exact U.seed_fixes i x hx

/-- A block map sends its source cut to one below the next cut. -/
theorem FatBlockSeq.blockMap_level_cut
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) :
    H.levelMap (U.blockMap H i).map (U.cut i) =
      U.cut (i + 1) - 1 := by
  rw [FatBlockSeq.blockMap, H.canonicalExtension_level_at_prefix]
  exact U.seed_top i

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
      simpa [FatBlockSeq.blockMap] using
        H.canonicalExtension_level_succ
          (U.seed i) (U.cut i) (U.cut i) le_rfl
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


/-- After i blocks, the cumulative map has a full consecutive tail beginning
at source level n+i and target cut c_i. -/
theorem FatBlockSeq.cumulative_level_tail
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) :
    ∀ i j : Nat,
      H.levelMap (U.cumulative H i).map (n + i + j) =
        U.cut i + j := by
  intro i
  induction i with
  | zero =>
      intro j
      obtain ⟨x, hx⟩ := H.level_nonempty (n + 0 + j)
      calc
        H.levelMap (U.cumulative H 0).map (n + 0 + j) =
            LevelTree.lev ((U.cumulative H 0) x) := by
          simpa [hx] using H.levelMap_eq (U.cumulative H 0).map (a := x)
        _ = LevelTree.lev x := rfl
        _ = n + j := by omega
        _ = U.cut 0 + j := by rw [U.cut_zero]
  | succ i ih =>
      intro j
      change
        H.levelMap
          (MMap.comp H (U.blockMap H i) (U.cumulative H i)).map
          (n + (i + 1) + j) =
            U.cut (i + 1) + j
      rw [H.levelMap_comp
        (U.blockMap H i) (U.cumulative H i)
        (n + (i + 1) + j)]
      have harg :
          n + (i + 1) + j = n + i + (j + 1) := by omega
      have hinner :
          H.levelMap (U.cumulative H i).map (n + (i + 1) + j) =
            U.cut i + (j + 1) := by
        rw [harg]
        exact ih (j + 1)
      rw [hinner]
      change
        H.levelMap
            (H.canonicalExtension
              (U.seed i) (U.cut i)).map
            (U.cut i + (j + 1)) =
          U.cut (i + 1) + j
      rw [H.canonicalExtension_level_tail
        (U.seed i) (U.cut i) (j + 1)]
      have htop := U.seed_top i
      rw [htop]
      have hcut : U.cut i < U.cut (i + 1) :=
        U.cut_strict (Nat.lt_succ_self i)
      omega

/-- Adding block i does not change nodes strictly below source level n+i. -/
theorem FatBlockSeq.cumulative_succ_agrees
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat)
    (x : T) (hx : LevelTree.lev x < n + i) :
    U.cumulative H (i + 1) x = U.cumulative H i x := by
  change U.blockMap H i (U.cumulative H i x) =
    U.cumulative H i x
  apply U.blockMap_fixesBelow H i
  calc
    LevelTree.lev (U.cumulative H i x) =
        H.levelMap (U.cumulative H i).map (LevelTree.lev x) :=
      (H.levelMap_eq (U.cumulative H i).map (a := x)).symm
    _ < H.levelMap (U.cumulative H i).map (n + i) :=
      H.levelMap_strictMono (U.cumulative H i).map hx
    _ = U.cut i := by
      simpa using U.cumulative_level_tail H i 0

/-- Reindex cumulative block maps by absolute source level so that ordinary
M1 fusion applies. -/
noncomputable def FatBlockSeq.fusionStage
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) (i : Nat) : MMap H :=
  U.cumulative H (i + 1 - n)

/-- The reindexed cumulative maps form an M1 fusion sequence. -/
theorem FatBlockSeq.fusionStage_stable
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) :
    ShapeMap.FusionStable (fun i => (U.fusionStage H i).map) := by
  intro i x hx
  by_cases hlow : i + 1 < n
  · have h0 : i + 1 - n = 0 := by omega
    have h1 : i + 2 - n = 0 := by omega
    change U.cumulative H (i + 1 - n) x =
      U.cumulative H (i + 2 - n) x
    rw [h0, h1]
  · have hn : n ≤ i + 1 := Nat.le_of_not_gt hlow
    let k := i + 1 - n
    have hik : i + 1 = n + k := by
      dsimp [k]
      omega
    have hk1 : i + 2 - n = k + 1 := by
      dsimp [k]
      omega
    change U.cumulative H (i + 1 - n) x =
      U.cumulative H (i + 2 - n) x
    rw [show i + 1 - n = k by rfl, hk1]
    exact (U.cumulative_succ_agrees H k x (by
      rw [← hik]
      omega)).symm

/-- The M1 limit carried by a fat block sequence. -/
noncomputable def FatBlockSeq.limit
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) : MMap H where
  map :=
    ShapeMap.fusionLimit
      (fun i => (U.fusionStage H i).map)
      (U.fusionStage_stable H)
  mem :=
    H.fusion_mem
      (fun i => (U.fusionStage H i).map)
      (fun i => (U.fusionStage H i).mem)
      (U.fusionStage_stable H)

/-- The fat limit fixes the frozen source prefix. -/
theorem FatBlockSeq.limit_fixesBelow
    (H : SMTree S) {n : Nat}
    (U : FatBlockSeq H n) :
    (U.limit H).FixesBelow H n := by
  intro x hx
  change U.fusionStage H (LevelTree.lev x) x = x
  have h0 : LevelTree.lev x + 1 - n = 0 := by omega
  change U.cumulative H (LevelTree.lev x + 1 - n) x = x
  rw [h0]
  rfl

end SMTree
end SuccessorTree

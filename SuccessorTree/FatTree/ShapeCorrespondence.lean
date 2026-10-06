import SuccessorTree.FatTree.FiniteRamsey
import SuccessorTree.ShapeSplit

/-!
# Shape maps carried by fat trees

The associated map of a fat tree is the pointwise fusion of the canonical
row extensions.  This is the formal counterpart of the map F_U in the
manuscript.  Only this direction of the correspondence is developed here;
the relative finite widening needed for the Ellentuck proof is added below.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace MMap

theorem levelMap_comp
    (H : SMTree S) (F G : MMap H) (n : Nat) :
    H.levelMap (MMap.comp H F G).map n =
      H.levelMap F.map (H.levelMap G.map n) := by
  obtain ⟨x, hx⟩ := H.level_nonempty n
  calc
    H.levelMap (MMap.comp H F G).map n =
        LevelTree.lev (F (G x)) := by
      simpa [hx] using
        H.levelMap_eq (MMap.comp H F G).map (a := x)
    _ = H.levelMap F.map (LevelTree.lev (G x)) := by
      exact (H.levelMap_eq F.map (a := G x)).symm
    _ = H.levelMap F.map (H.levelMap G.map n) := by
      have hG := H.levelMap_eq G.map (a := x)
      rw [hx] at hG
      rw [hG]

theorem levelMap_id (H : SMTree S) (n : Nat) :
    H.levelMap (MMap.id H).map n = n := by
  obtain ⟨x, hx⟩ := H.level_nonempty n
  calc
    H.levelMap (MMap.id H).map n =
        LevelTree.lev ((MMap.id H) x) := by
      simpa [hx] using H.levelMap_eq (MMap.id H).map (a := x)
    _ = LevelTree.lev x := rfl
    _ = n := hx

end MMap

namespace FatTree

variable (H : SMTree S)

/-- Composition of the first i canonical row extensions. -/
noncomputable def partialMap (U : FatTree H) : Nat → MMap H
  | 0 => MMap.id H
  | i + 1 => MMap.comp H (U.rowExtension H i) (partialMap U i)

@[simp] theorem partialMap_zero (U : FatTree H) :
    partialMap H U 0 = MMap.id H := rfl

@[simp] theorem partialMap_succ (U : FatTree H) (i : Nat) :
    partialMap H U (i + 1) =
      MMap.comp H (U.rowExtension H i) (partialMap H U i) := rfl

/-- After i rows, the canonical tail begins at cut i. -/
theorem partialMap_level_tail (U : FatTree H) :
    ∀ i k : Nat,
      H.levelMap (partialMap H U i).map (i + k) =
        U.cut i + k := by
  intro i
  induction i with
  | zero =>
      intro k
      simp [partialMap, MMap.levelMap_id, U.cut_zero]
  | succ i ih =>
      intro k
      rw [partialMap_succ, MMap.levelMap_comp]
      have hprev :
          H.levelMap (partialMap H U i).map (i + 1 + k) =
            U.cut i + (k + 1) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)
      rw [hprev]
      unfold rowExtension
      rw [H.canonicalExtension_level_tail
        ((U.row i).representative H) (U.cut i) (k + 1)]
      change
        (U.row i).rowEndLevel H + (k + 1) =
          U.cut (i + 1) + k
      rw [← U.row_cut i]
      omega

/-- The first i+1 rows send source level i to the last level of row i. -/
theorem partialMap_level_last (U : FatTree H) (i : Nat) :
    H.levelMap (partialMap H U (i + 1)).map i =
      U.cut (i + 1) - 1 := by
  rw [partialMap_succ, MMap.levelMap_comp]
  have hprev :
      H.levelMap (partialMap H U i).map i = U.cut i := by
    simpa using partialMap_level_tail H U i 0
  rw [hprev]
  exact (U.rowExtension_level_at_cut H i).trans (by
    rw [← U.row_cut i]
    omega)

/-- The partial products form the fusion sequence used in the manuscript. -/
theorem partialMap_fusionStable (U : FatTree H) :
    ShapeMap.FusionStable
      (fun i => (partialMap H U (i + 1)).map) := by
  intro i x hx
  change partialMap H U (i + 1) x =
    partialMap H U (i + 2) x
  rw [partialMap_succ]
  change partialMap H U (i + 1) x =
    U.rowExtension H (i + 1) (partialMap H U (i + 1) x)
  symm
  have hlev :
      LevelTree.lev (partialMap H U (i + 1) x) < U.cut (i + 1) := by
    calc
      LevelTree.lev (partialMap H U (i + 1) x) =
          H.levelMap (partialMap H U (i + 1)).map (LevelTree.lev x) :=
        (H.levelMap_eq (partialMap H U (i + 1)).map (a := x)).symm
      _ ≤ H.levelMap (partialMap H U (i + 1)).map i :=
        (H.levelMap_strictMono (partialMap H U (i + 1)).map).monotone hx
      _ = U.cut (i + 1) - 1 :=
        partialMap_level_last H U i
      _ < U.cut (i + 1) := by
        have hpos : 0 < U.cut (i + 1) := by
          have h := U.cut_strictMono H (Nat.zero_lt_succ i)
          simpa [U.cut_zero] using h
        omega
  rw [U.rowExtension_agrees H (i + 1)
    (partialMap H U (i + 1) x) (Nat.le_of_lt hlev)]
  exact (U.row (i + 1)).representative_fixesBelow H
    (partialMap H U (i + 1) x) hlev

/-- The shape-preserving map canonically carried by an infinite fat tree. -/
noncomputable def associatedMap (U : FatTree H) : MMap H := by
  let F : Nat → ShapeMap S :=
    fun i => (partialMap H U (i + 1)).map
  have hs : ShapeMap.FusionStable F :=
    partialMap_fusionStable H U
  exact {
    map := ShapeMap.fusionLimit F hs
    mem := H.fusion_mem F (fun i => (partialMap H U (i + 1)).mem) hs
  }

theorem associatedMap_apply (U : FatTree H) (x : T) :
    associatedMap H U x =
      partialMap H U (LevelTree.lev x + 1) x := by
  rfl

/-- The associated map has exactly the level function stated in the paper. -/
theorem associatedMap_level (U : FatTree H) (i : Nat) :
    H.levelMap (associatedMap H U).map i =
      U.cut (i + 1) - 1 := by
  obtain ⟨x, hx⟩ := H.level_nonempty i
  calc
    H.levelMap (associatedMap H U).map i =
        LevelTree.lev (associatedMap H U x) := by
      simpa [hx] using H.levelMap_eq (associatedMap H U).map (a := x)
    _ = LevelTree.lev (partialMap H U (i + 1) x) := by
      rw [associatedMap_apply, hx]
    _ = H.levelMap (partialMap H U (i + 1)).map i := by
      simpa [hx] using
        (H.levelMap_eq (partialMap H U (i + 1)).map (a := x)).symm
    _ = U.cut (i + 1) - 1 := partialMap_level_last H U i

end FatTree

end SMTree
end SuccessorTree

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

theorem fixesBelow_zero (H : SMTree S) (F : MMap H) :
    F.FixesBelow H 0 := by
  intro x hx
  omega

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

/-- The canonical extension of the associated map through source level i
is exactly the product of the first i+1 fat-tree rows. -/
theorem canonicalExtension_associatedMap
    (U : FatTree H) (i : Nat) :
    H.canonicalExtension (associatedMap H U) i =
      partialMap H U (i + 1) := by
  apply H.canonicalExtension_unique (associatedMap H U)
    (partialMap H U (i + 1)) i
  · intro x hx
    rw [associatedMap_apply H U x]
    have hs := partialMap_fusionStable H U
    have hstage :=
      ShapeMap.fusion_stable_of_le
        (fun j => (partialMap H U (j + 1)).map) hs x hx
    exact hstage.symm
  · intro ell hell
    have hbase :
        H.levelMap (associatedMap H U).map i =
          U.cut (i + 1) - 1 := by
      exact associatedMap_level H U i
    rw [hbase] at hell
    by_cases heq : ell = U.cut (i + 1) - 1
    · rw [heq, ← H.range_levelMap]
      refine ⟨i, ?_⟩
      exact partialMap_level_last H U i
    · have hcut : U.cut (i + 1) ≤ ell := by
        have hpos : 0 < U.cut (i + 1) := by
          have h := U.cut_strictMono H (Nat.zero_lt_succ i)
          simpa [U.cut_zero] using h
        omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hcut
      rw [← H.range_levelMap]
      refine ⟨i + 1 + k, ?_⟩
      simpa [hk] using partialMap_level_tail H U (i + 1) k

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


namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- The cuts of the canonical fat-tree widening of a shape map. -/
noncomputable def shapeCut (K : MMap H) : Nat → Nat
  | 0 => 0
  | i + 1 => H.levelMap K.map i + 1

@[simp] theorem shapeCut_zero (K : MMap H) :
    shapeCut H K 0 = 0 := rfl

@[simp] theorem shapeCut_succ (K : MMap H) (i : Nat) :
    shapeCut H K (i + 1) = H.levelMap K.map i + 1 := rfl

/-- The factor which adds source level i+1 after the canonical prefix
through source level i. -/
noncomputable def shapeNextFactor (K : MMap H) (i : Nat) : MMap H :=
  Classical.choose (H.exists_factor_through_canonical_succ K i)

theorem shapeNextFactor_spec (K : MMap H) (i : Nat) :
    (shapeNextFactor H K i).FixesBelow H (H.levelMap K.map i + 1) ∧
    H.levelMap (shapeNextFactor H K i).map
        (H.levelMap K.map i + 1) =
      H.levelMap K.map (i + 1) ∧
    ∀ x : T, LevelTree.lev x ≤ i + 1 →
      shapeNextFactor H K i (H.canonicalExtension K i x) = K x :=
  Classical.choose_spec (H.exists_factor_through_canonical_succ K i)

/-- Reading the final level of a one-row word produced from a total map
recovers the level of that total map at the source cut. -/
theorem rowEndLevel_toAM
    (F : MMap H) (n : Nat) (hF : F.FixesBelow H n) :
    ((F.toAM H n 1 hF).rowEndLevel H) =
      H.levelMap F.map n := by
  obtain ⟨x, hx⟩ := H.level_nonempty n
  have htop := AM.representative_top H (F.toAM H n 1 hF)
  have hval := congrArg Subtype.val htop
  change
    ((F.toAM H n 1 hF).representative H).restrictLe H n =
      F.restrictLe H n at hval
  have hpoint := congrFun hval ⟨x, by simpa [hx]⟩
  unfold AM.rowEndLevel
  calc
    H.levelMap ((F.toAM H n 1 hF).representative H).map n =
        LevelTree.lev ((F.toAM H n 1 hF).representative H x) := by
      simpa [hx] using
        H.levelMap_eq ((F.toAM H n 1 hF).representative H).map (a := x)
    _ = LevelTree.lev (F x) := congrArg LevelTree.lev hpoint
    _ = H.levelMap F.map n := by
      simpa [hx] using (H.levelMap_eq F.map (a := x)).symm

/-- The i-th row in the canonical widening of K. -/
noncomputable def shapeRow (K : MMap H) :
    (i : Nat) → AM H (shapeCut H K i) 1
  | 0 =>
      K.toAM H 0 1 (MMap.fixesBelow_zero H K)
  | i + 1 =>
      let Q := shapeNextFactor H K i
      Q.toAM H (H.levelMap K.map i + 1) 1
        (shapeNextFactor_spec H K i).1

/-- Canonical widening of a total shape map to a fat tree. -/
noncomputable def ofShapeMap (K : MMap H) : FatTree H where
  cut := shapeCut H K
  cut_zero := rfl
  row := shapeRow H K
  row_cut := by
    intro i
    cases i with
    | zero =>
        change
          ((K.toAM H 0 1 (MMap.fixesBelow_zero H K)).rowEndLevel H) + 1 =
            H.levelMap K.map 0 + 1
        rw [rowEndLevel_toAM H K 0 (MMap.fixesBelow_zero H K)]
    | succ i =>
        let Q := shapeNextFactor H K i
        have hQfix :
            Q.FixesBelow H (H.levelMap K.map i + 1) :=
          (shapeNextFactor_spec H K i).1
        change
          ((Q.toAM H (H.levelMap K.map i + 1) 1 hQfix).rowEndLevel H) + 1 =
            H.levelMap K.map (i + 1) + 1
        rw [rowEndLevel_toAM H Q (H.levelMap K.map i + 1) hQfix]
        exact congrArg (fun z => z + 1)
          (shapeNextFactor_spec H K i).2.1

@[simp] theorem ofShapeMap_cut (K : MMap H) (i : Nat) :
    (ofShapeMap H K).cut i = shapeCut H K i := rfl

/-- The row extension of a row obtained from F.toAM agrees with F through
the source cut. -/
theorem rowExtension_toAM_agrees
    (F : MMap H) (n : Nat) (hF : F.FixesBelow H n)
    (x : T) (hx : LevelTree.lev x ≤ n) :
    H.canonicalExtension ((F.toAM H n 1 hF).representative H) n x =
      F x := by
  rw [H.canonicalExtension_agrees _ n x hx]
  have htop := AM.representative_top H (F.toAM H n 1 hF)
  have hval := congrArg Subtype.val htop
  change
    ((F.toAM H n 1 hF).representative H).restrictLe H n =
      F.restrictLe H n at hval
  exact congrFun hval ⟨x, hx⟩

/-- The first i+1 rows of the canonical widening are precisely the canonical
extension of K through source level i. -/
theorem ofShapeMap_partialMap_canonical (K : MMap H) :
    ∀ i : Nat,
      partialMap H (ofShapeMap H K) (i + 1) =
        H.canonicalExtension K i := by
  intro i
  induction i with
  | zero =>
      rw [partialMap_succ, partialMap_zero]
      apply H.canonicalExtension_unique K
        ((ofShapeMap H K).rowExtension H 0) 0
      · intro x hx
        change
          H.canonicalExtension
              (((K.toAM H 0 1 (MMap.fixesBelow_zero H K)).representative H)) 0 x =
            K x
        exact rowExtension_toAM_agrees H K 0 (MMap.fixesBelow_zero H K) x hx
      · intro ell hell
        change ell ∈
          (H.canonicalExtension
            ((K.toAM H 0 1 (MMap.fixesBelow_zero H K)).representative H) 0).map.levelRange
        apply H.canonicalExtension_tail_mem_levelRange
        have hrow :=
          rowEndLevel_toAM H K 0 (MMap.fixesBelow_zero H K)
        simpa [AM.rowEndLevel] using hrow.trans_le hell
  | succ i ih =>
      rw [partialMap_succ, ih]
      let Q := shapeNextFactor H K i
      let c := H.levelMap K.map i + 1
      have hQfix : Q.FixesBelow H c :=
        (shapeNextFactor_spec H K i).1
      have hQlev :
          H.levelMap Q.map c = H.levelMap K.map (i + 1) :=
        (shapeNextFactor_spec H K i).2.1
      have hQK :
          ∀ x : T, LevelTree.lev x ≤ i + 1 →
            Q (H.canonicalExtension K i x) = K x :=
        (shapeNextFactor_spec H K i).2.2
      apply H.canonicalExtension_unique K
        (MMap.comp H
          ((ofShapeMap H K).rowExtension H (i + 1))
          (H.canonicalExtension K i)) (i + 1)
      · intro x hx
        change
          H.canonicalExtension
              ((Q.toAM H c 1 hQfix).representative H) c
              (H.canonicalExtension K i x) = K x
        have hinner :
            LevelTree.lev (H.canonicalExtension K i x) ≤ c := by
          calc
            LevelTree.lev (H.canonicalExtension K i x) =
                H.levelMap (H.canonicalExtension K i).map
                  (LevelTree.lev x) :=
              (H.levelMap_eq (H.canonicalExtension K i).map (a := x)).symm
            _ ≤ H.levelMap (H.canonicalExtension K i).map (i + 1) :=
              (H.levelMap_strictMono
                (H.canonicalExtension K i).map).monotone hx
            _ = c := by
              dsimp [c]
              rw [H.canonicalExtension_level_succ K i i le_rfl,
                H.canonicalExtension_level_at_prefix K i]
        rw [rowExtension_toAM_agrees H Q c hQfix _ hinner]
        exact hQK x hx
      · intro ell hell
        rw [← H.range_levelMap]
        let t := ell - H.levelMap K.map (i + 1)
        let j := i + 1 + t
        refine ⟨j, ?_⟩
        rw [MMap.levelMap_comp]
        have hinner :
            H.levelMap (H.canonicalExtension K i).map j =
              c + t := by
          dsimp [j, c]
          simpa [Nat.add_assoc] using
            H.canonicalExtension_level_tail K i (1 + t)
        rw [hinner]
        change
          H.levelMap
              (H.canonicalExtension
                ((Q.toAM H c 1 hQfix).representative H) c).map
              (c + t) = ell
        rw [H.canonicalExtension_level_tail
          ((Q.toAM H c 1 hQfix).representative H) c t]
        have hrepQ :
            H.levelMap ((Q.toAM H c 1 hQfix).representative H).map c =
              H.levelMap Q.map c := by
          simpa [AM.rowEndLevel] using
            rowEndLevel_toAM H Q c hQfix
        rw [hrepQ, hQlev]
        dsimp [t]
        omega

/-- The widening construction is a right inverse to the associated-map
construction. -/
theorem associatedMap_ofShapeMap (K : MMap H) :
    associatedMap H (ofShapeMap H K) = K := by
  apply MMap.ext_apply
  intro x
  let i := LevelTree.lev x
  calc
    associatedMap H (ofShapeMap H K) x =
        partialMap H (ofShapeMap H K) (i + 1) x := by
      rw [associatedMap_apply]
    _ = H.canonicalExtension K i x := by
      rw [ofShapeMap_partialMap_canonical H K i]
    _ = K x := H.canonicalExtension_agrees K i x le_rfl

end FatTree

end SMTree
end SuccessorTree

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- Composition of a consecutive interval of fat-tree row extensions. -/
noncomputable def intervalMap (U : FatTree H) : Nat → Nat → MMap H
  | _, 0 => MMap.id H
  | i, steps + 1 =>
      MMap.comp H (intervalMap U (i + 1) steps) (U.rowExtension H i)

@[simp] theorem intervalMap_zero (U : FatTree H) (i : Nat) :
    intervalMap H U i 0 = MMap.id H := rfl

@[simp] theorem intervalMap_succ (U : FatTree H) (i steps : Nat) :
    intervalMap H U i (steps + 1) =
      MMap.comp H (intervalMap H U (i + 1) steps) (U.rowExtension H i) := rfl

/-- After crossing a finite interval of rows, the canonical tail remains
consecutive. -/
theorem intervalMap_level_tail (U : FatTree H) :
    ∀ (i steps k : Nat),
      H.levelMap (intervalMap H U i steps).map
          (U.cut i + steps + k) =
        U.cut (i + steps) + k := by
  intro i steps
  induction steps generalizing i with
  | zero =>
      intro k
      simp [intervalMap, MMap.levelMap_id]
  | succ steps ih =>
      intro k
      rw [intervalMap_succ, MMap.levelMap_comp]
      have hrow :
          H.levelMap (U.rowExtension H i).map
              (U.cut i + (steps + 1) + k) =
            U.cut (i + 1) + steps + k := by
        unfold rowExtension
        calc
          H.levelMap
              (H.canonicalExtension ((U.row i).representative H) (U.cut i)).map
              (U.cut i + (steps + 1) + k) =
              (U.row i).rowEndLevel H + (steps + 1 + k) := by
            simpa [AM.rowEndLevel, Nat.add_assoc] using
              H.canonicalExtension_level_tail
                ((U.row i).representative H) (U.cut i) (steps + 1 + k)
          _ = U.cut (i + 1) + steps + k := by
            rw [← U.row_cut i]
            omega
      rw [hrow]
      have hih := ih (i := i + 1) k
      have hind : i + 1 + steps = i + (steps + 1) := by omega
      rw [hind] at hih
      exact hih

/-- An interval product fixes everything below its initial cut. -/
theorem intervalMap_fixesBelow (U : FatTree H) :
    ∀ (i steps : Nat),
      (intervalMap H U i steps).FixesBelow H (U.cut i) := by
  intro i steps
  induction steps generalizing i with
  | zero =>
      exact MMap.id_fixesBelow H (U.cut i)
  | succ steps ih =>
      have htail :
          (intervalMap H U (i + 1) steps).FixesBelow H (U.cut (i + 1)) :=
        ih (i := i + 1)
      have htail' :
          (intervalMap H U (i + 1) steps).FixesBelow H (U.cut i) := by
        intro x hx
        exact htail x (lt_trans hx (U.cut_lt_succ H i))
      exact MMap.comp_fixesBelow H
        (intervalMap H U (i + 1) steps) (U.rowExtension H i)
        (U.cut i) htail' (U.rowExtension_fixesBelow H i)

/-- A path of the right length is sent by the interval product to an endpoint
of the corresponding fat-tree lift. -/
theorem intervalMap_mem_liftSteps_of_le
    (U : FatTree H) :
    ∀ (i steps : Nat) {x z : T},
      LevelTree.lev x = U.cut i →
      LevelTree.lev z = U.cut i + steps →
      x ≤ z →
      intervalMap H U i steps z ∈
        U.liftSteps H i steps ({x} : Set T) := by
  intro i steps
  induction steps generalizing i with
  | zero =>
      intro x z hx hz hxz
      have hzx : z = x := by
        exact (LevelTree.same_level_of_le hxz (hx.trans hz.symm)).symm
      subst z
      simp [intervalMap]
  | succ steps ih =>
      intro x z hx hz hxz
      have hcut : U.cut i + 1 ≤ LevelTree.lev z := by
        rw [hz]
        omega
      let y := LevelTree.ancestor z (U.cut i + 1) hcut
      have hyz : y ≤ z :=
        LevelTree.ancestor_le z (U.cut i + 1) hcut
      have hy : LevelTree.lev y = U.cut i + 1 :=
        LevelTree.level_ancestor z (U.cut i + 1) hcut
      have hxy : x ≤ y := by
        rcases LevelTree.comparable_below hxz hyz with h | h
        · exact h
        · have hlev := LevelTree.level_le_of_le h
          rw [hx, hy] at hlev
          omega
      have hcov : x ⋖ y :=
        LevelTree.covBy_of_le_level_succ hxy (by rw [hx, hy])
      let x' := U.rowExtension H i y
      let z' := U.rowExtension H i z
      have hx'mem : x' ∈ U.oneLift H i ({x} : Set T) := by
        exact ⟨y, ⟨x, by simp, hcov⟩, rfl⟩
      have hx' :
          LevelTree.lev x' = U.cut (i + 1) := by
        apply U.oneLift_subset_nextLevel H i
          (by
            intro q hq
            have hq : q = x := by simpa using hq
            subst q
            exact hx)
          hx'mem
      have hz' :
          LevelTree.lev z' = U.cut (i + 1) + steps := by
        dsimp [z']
        calc
          LevelTree.lev (U.rowExtension H i z) =
              H.levelMap (U.rowExtension H i).map (LevelTree.lev z) :=
            (H.levelMap_eq (U.rowExtension H i).map (a := z)).symm
          _ = H.levelMap (U.rowExtension H i).map
              (U.cut i + (steps + 1)) := by rw [hz]
          _ = (U.row i).rowEndLevel H + (steps + 1) := by
            unfold rowExtension
            rw [H.canonicalExtension_level_tail]
            rfl
          _ = U.cut (i + 1) + steps := by
            rw [← U.row_cut i]
            omega
      have hx'z' : x' ≤ z' :=
        (U.rowExtension H i).map.map_le_of_le hyz
      have hrec :
          intervalMap H U (i + 1) steps z' ∈
            U.liftSteps H (i + 1) steps ({x'} : Set T) :=
        ih (i := i + 1) hx' hz' hx'z'
      have hsub :
          ({x'} : Set T) ⊆ U.oneLift H i ({x} : Set T) := by
        intro q hq
        have hq : q = x' := by simpa using hq
        subst q
        exact hx'mem
      have hmono :=
        U.liftSteps_mono H (i + 1) steps hsub hrec
      change
        intervalMap H U (i + 1) steps (U.rowExtension H i z) ∈
          U.liftSteps H (i + 1) steps
            (U.oneLift H i ({x} : Set T))
      exact hmono

/-- At the tail level reached after an interval, the interval product sends
an edge to an edge. -/
theorem intervalMap_covBy_tail
    (U : FatTree H) (i steps : Nat)
    {y z : T} (hyz : y ⋖ z)
    (hy : LevelTree.lev y = U.cut i + steps) :
    intervalMap H U i steps y ⋖
      intervalMap H U i steps z := by
  have hz : LevelTree.lev z = U.cut i + steps + 1 := by
    rw [LevelTree.covBy_level_eq hyz, hy]
  have hlt :=
    (intervalMap H U i steps).map.map_lt_of_covBy hyz
  apply LevelTree.covBy_of_le_level_succ hlt.le
  calc
    LevelTree.lev (intervalMap H U i steps z) =
        H.levelMap (intervalMap H U i steps).map
          (LevelTree.lev z) :=
      (H.levelMap_eq (intervalMap H U i steps).map (a := z)).symm
    _ = U.cut (i + steps) + 1 := by
      rw [hz]
      exact intervalMap_level_tail H U i steps 1
    _ = H.levelMap (intervalMap H U i steps).map
          (LevelTree.lev y) + 1 := by
      have h0 := intervalMap_level_tail H U i steps 0
      rw [Nat.add_zero] at h0
      rw [hy]
      exact congrArg (fun q => q + 1) h0.symm
    _ = LevelTree.lev (intervalMap H U i steps y) + 1 := by
      rw [H.levelMap_eq]

end FatTree

end SMTree
end SuccessorTree

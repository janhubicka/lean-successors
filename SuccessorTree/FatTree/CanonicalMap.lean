import SuccessorTree.FatTree.Lift
import SuccessorTree.ShapeFusion
import SuccessorTree.ShapeTransport

/-!
# The canonical shape map of a fat tree

For an infinite fat tree U, the manuscript defines

  F_U = lim_m u_m^+ ... u_0^+.

This file constructs that map directly from M1.  The finite product after r
rows has an affine tail: source level r+k lands on cut(r)+k.  Consequently
adding row r fixes every value coming from source levels < r, so the products
form an M1 fusion sequence.

The resulting map has image level cut(j+1)-1 at source level j, exactly as in
Definition 2.6 of the manuscript.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- Product of the first r canonical row extensions:
u_(r-1)^+ ... u_0^+. -/
noncomputable def prefixProduct (U : FatTree H) : Nat → MMap H
  | 0 => MMap.id H
  | r + 1 => MMap.comp H (U.rowExtension H r) (prefixProduct U r)

@[simp] theorem prefixProduct_zero (U : FatTree H) :
    prefixProduct H U 0 = MMap.id H := rfl

theorem prefixProduct_succ (U : FatTree H) (r : Nat) :
    prefixProduct H U (r + 1) =
      MMap.comp H (U.rowExtension H r) (prefixProduct H U r) := rfl

/-- After the first r rows, the untouched tail of the level map is affine. -/
theorem prefixProduct_level_tail
    (U : FatTree H) :
    ∀ r k : Nat,
      H.levelMap (prefixProduct H U r).map (r + k) = U.cut r + k := by
  intro r
  induction r with
  | zero =>
      intro k
      obtain ⟨x, hx⟩ := H.level_nonempty k
      calc
        H.levelMap (prefixProduct H U 0).map (0 + k) =
            LevelTree.lev ((MMap.id H) x) := by
          simpa [prefixProduct, hx] using
            H.levelMap_eq (MMap.id H).map (a := x)
        _ = k := by simpa using hx
        _ = U.cut 0 + k := by rw [U.cut_zero]; omega
  | succ r ih =>
      intro k
      calc
        H.levelMap (prefixProduct H U (r + 1)).map ((r + 1) + k) =
            H.levelMap (U.rowExtension H r).map
              (H.levelMap (prefixProduct H U r).map ((r + 1) + k)) := by
          rw [prefixProduct_succ, H.levelMap_comp]
        _ = H.levelMap (U.rowExtension H r).map (U.cut r + (k + 1)) := by
          rw [show (r + 1) + k = r + (k + 1) by omega, ih (k + 1)]
        _ = (U.row r).rowEndLevel H + (k + 1) := by
          unfold FatTree.rowExtension
          rw [H.canonicalExtension_level_tail]
        _ = U.cut (r + 1) + k := by
          have hrow := U.row_cut r
          omega

/-- Values coming from source levels before r lie strictly below cut r. -/
theorem prefixProduct_level_lt_cut
    (U : FatTree H) {r j : Nat} (hj : j < r) :
    H.levelMap (prefixProduct H U r).map j < U.cut r := by
  have hmono :=
    H.levelMap_strictMono (prefixProduct H U r).map hj
  have htop := prefixProduct_level_tail H U r 0
  simpa using hmono.trans_eq (by simpa using htop)

/-- Adding the next row cannot change a value coming from an already frozen
source level. -/
theorem prefixProduct_stable
    (U : FatTree H) :
    MMap.FusionStable H (fun i => prefixProduct H U (i + 1)) := by
  intro i x hx
  have hlev :
      LevelTree.lev (prefixProduct H U (i + 1) x) < U.cut (i + 1) := by
    calc
      LevelTree.lev (prefixProduct H U (i + 1) x) =
          H.levelMap (prefixProduct H U (i + 1)).map (LevelTree.lev x) :=
        (H.levelMap_eq (prefixProduct H U (i + 1)).map (a := x)).symm
      _ < U.cut (i + 1) :=
        prefixProduct_level_lt_cut H U (by omega)
  change
    prefixProduct H U (i + 1) x =
      prefixProduct H U (i + 2) x
  rw [show i + 2 = (i + 1) + 1 by omega, prefixProduct_succ]
  change
    prefixProduct H U (i + 1) x =
      U.rowExtension H (i + 1) (prefixProduct H U (i + 1) x)
  symm
  exact U.rowExtension_fixesBelow H (i + 1)
    (prefixProduct H U (i + 1) x) hlev

/-- The manuscript's canonical map F_U. -/
noncomputable def canonicalMap (U : FatTree H) : MMap H :=
  MMap.fusionLimit H
    (fun i => prefixProduct H U (i + 1))
    (prefixProduct_stable H U)

@[simp] theorem canonicalMap_apply (U : FatTree H) (x : T) :
    canonicalMap H U x =
      prefixProduct H U (LevelTree.lev x + 1) x := rfl

/-- The canonical map after j+1 rows is already determined at source level j. -/
theorem canonicalMap_level
    (U : FatTree H) (j : Nat) :
    H.levelMap (canonicalMap H U).map j = (U.row j).rowEndLevel H := by
  obtain ⟨x, hx⟩ := H.level_nonempty j
  have hprod :
      H.levelMap (prefixProduct H U j).map j = U.cut j := by
    simpa using prefixProduct_level_tail H U j 0
  have hprodX :
      LevelTree.lev (prefixProduct H U j x) = U.cut j := by
    calc
      LevelTree.lev (prefixProduct H U j x) =
          H.levelMap (prefixProduct H U j).map (LevelTree.lev x) :=
        (H.levelMap_eq (prefixProduct H U j).map (a := x)).symm
      _ = U.cut j := by simpa [hx] using hprod
  calc
    H.levelMap (canonicalMap H U).map j =
        LevelTree.lev (canonicalMap H U x) := by
      simpa [hx] using H.levelMap_eq (canonicalMap H U).map (a := x)
    _ = LevelTree.lev
        (U.rowExtension H j (prefixProduct H U j x)) := by
      rw [canonicalMap_apply, hx]
      change
        LevelTree.lev (prefixProduct H U (j + 1) x) =
          LevelTree.lev (U.rowExtension H j (prefixProduct H U j x))
      rfl
    _ = H.levelMap (U.rowExtension H j).map (U.cut j) := by
      rw [← H.levelMap_eq (U.rowExtension H j).map
        (a := prefixProduct H U j x), hprodX]
    _ = (U.row j).rowEndLevel H :=
      U.rowExtension_level_at_cut H j

/-- Equivalent cut formula for the level map of F_U. -/
theorem canonicalMap_level_succ_cut
    (U : FatTree H) (j : Nat) :
    H.levelMap (canonicalMap H U).map j + 1 = U.cut (j + 1) := by
  rw [canonicalMap_level H U j]
  exact U.row_cut j

/-- The j-th source level of F_U lands immediately below the (j+1)-st fat
cut. -/
theorem canonicalMap_level_lt_cut
    (U : FatTree H) (j : Nat) :
    H.levelMap (canonicalMap H U).map j < U.cut (j + 1) := by
  have h := canonicalMap_level_succ_cut H U j
  omega

/-- The first n row products depend only on the first n rows of the fat
tree. -/
theorem prefixProduct_eq_of_initialSegment
    {U V : FatTree H} :
    ∀ n : Nat,
      U.initialSegment H n = V.initialSegment H n →
        prefixProduct H U n = prefixProduct H V n := by
  intro n
  induction n with
  | zero =>
      intro _
      rfl
  | succ n ih =>
      intro hseg
      have hprev :
          U.initialSegment H n = V.initialSegment H n :=
        (a1_three H hseg).2 n (by omega)
      have hprod : prefixProduct H U n = prefixProduct H V n :=
        ih hprev
      let i : Fin (n + 1) := Fin.last n
      have hrowSeg :
          (U.initialSegment H (n + 1)).rowExtension H i =
            (V.initialSegment H (n + 1)).rowExtension H i := by
        rw [hseg]
      have hrow :
          U.rowExtension H n = V.rowExtension H n := by
        simpa [i] using hrowSeg
      rw [prefixProduct_succ, prefixProduct_succ, hprod, hrow]

/-- Equal n-row fat prefixes induce equal n-th finite approximations of their
canonical shape maps. -/
theorem canonicalMap_ramseyApprox_eq_of_initialSegment
    {U V : FatTree H} {n : Nat}
    (hseg : U.initialSegment H n = V.initialSegment H n) :
    ramseyApprox H n (canonicalMap H U) =
      ramseyApprox H n (canonicalMap H V) := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      have hprod :
          prefixProduct H U (n + 1) =
            prefixProduct H V (n + 1) :=
        prefixProduct_eq_of_initialSegment H (n + 1) hseg
      apply Subtype.ext
      funext x
      have hU :
          canonicalMap H U x.1 =
            prefixProduct H U (n + 1) x.1 := by
        exact MMap.fusionLimit_eq_stage H
          (fun i => prefixProduct H U (i + 1))
          (prefixProduct_stable H U) x.2
      have hV :
          canonicalMap H V x.1 =
            prefixProduct H V (n + 1) x.1 := by
        exact MMap.fusionLimit_eq_stage H
          (fun i => prefixProduct H V (i + 1))
          (prefixProduct_stable H V) x.2
      rw [hU, hV, hprod]

/-- Finite projection y ↦ F_y, defined invariantly by completing the finite
fat tree and taking the corresponding finite approximation of its canonical
map. -/
noncomputable def exactCanonicalApprox
    {n : Nat} (x : ExactApprox H n) :
    (ramseyApproximationSystem H).Approx n :=
  ramseyApprox H n (canonicalMap H (completeExact H x))

/-- The finite projection of the actual n-th prefix of U is precisely the
n-th finite approximation of F_U. -/
theorem exactCanonicalApprox_exactApprox
    (U : FatTree H) (n : Nat) :
    exactCanonicalApprox H (exactApprox H n U) =
      ramseyApprox H n (canonicalMap H U) := by
  apply canonicalMap_ramseyApprox_eq_of_initialSegment H
  have hcomplete :=
    exactApprox_completeExact H (exactApprox H n U)
  exact congrArg Subtype.val hcomplete

end FatTree
end SMTree
end SuccessorTree

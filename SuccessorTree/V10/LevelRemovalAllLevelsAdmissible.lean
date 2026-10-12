import SuccessorTree.V10.LevelRemovalBoundaryAdmissible
import Mathlib.Tactic

/-!
# Intrinsic deletion is admissible at EVERY source level above an image gap

The local M2 checks already prove guarded admissibility of the intrinsically
deleted complete record at the boundary a and at any upper z above one
genuine successor of a. The image gap and its last missing coordinate
depend only on the source LEVEL, not the chosen component or node.

For an arbitrary source x at or above the boundary level, choose the
actual predecessor chain inside x. At the boundary apply the checked
boundary lemma. Above it, the predecessor at the gap level has an actual
next successor on the branch to x; apply the checked upper lemma.
The output record is fixed in advance by F(x), so this construction
does not choose a new target based on a witness.

This establishes uniform Kpt MEMBERSHIP, not yet the ShapeMap laws
(injectivity, level preservation, weak successors), nor M2/B3 factorization.
-/

namespace SuccessorTree.V10

/-- A strict gap between the images of two consecutive source levels
has the same size in every component of the Kpt forest. -/
theorem gap_of_equal_source_levels
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ q a : AdmissibleKptNode family)
    (hq : LevelTree.lev q = LevelTree.lev q₀)
    (ha : LevelTree.lev a = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀)) :
    LevelTree.lev (F q) + 1 < LevelTree.lev (F a) := by
  have hqF := F.level_eq_of_level_eq hq
  have haF := F.level_eq_of_level_eq ha
  omega

/-- Let q₀ and a₀ denote consecutive source levels, with a genuine
gap between their image levels. Put m = lev(F a₀)-1. For EVERY node x
at or above the level of a₀, the complete raw type obtained by
deleting exactly m from F(x) is admissible.

No successor, finite representation or free cut is chosen in the
value: all choices occur only in the proof of its admissibility. -/
theorem admissible_deleted_image_at_all_upper_source_levels
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : AdmissibleKptNode family)
    (hx : LevelTree.lev a₀ ≤ LevelTree.lev x) :
    let m := LevelTree.lev (F a₀) - 1
    ∃ hm : m < (F x).1.1,
      IsAdmissibleRawType family
        (⟨(F x).1.1 - 1,
          (F x).1.2.deleteOrdinary m hm⟩ :
            RawPartialTypeNode db du dd) := by
  let n := LevelTree.lev a₀
  let m := LevelTree.lev (F a₀) - 1
  have hnPos : 0 < n := by
    dsimp [n]
    omega
  by_cases hAt : LevelTree.lev x = n
  · let q := LevelTree.ancestor x (n - 1) (by omega)
    have hqLevel : LevelTree.lev q = n - 1 :=
      LevelTree.level_ancestor x (n - 1) (by omega)
    have hPrev : LevelTree.lev q + 1 = LevelTree.lev x := by
      dsimp [q] at hqLevel
      omega
    have hqEq : LevelTree.lev q = LevelTree.lev q₀ := by
      dsimp [n] at hqLevel
      omega
    have hxEq : LevelTree.lev x = LevelTree.lev a₀ := by
      dsimp [n] at hAt
      exact hAt
    have hGapX : LevelTree.lev (F q) + 1 < LevelTree.lev (F x) :=
      gap_of_equal_source_levels family F q₀ a₀ q x hqEq hxEq hgap
    have hExist := boundary_deleted_image_type_admissible
      family F q x hPrev hGapX
    have hFLevel : LevelTree.lev (F x) = LevelTree.lev (F a₀) :=
      F.level_eq_of_level_eq hxEq
    dsimp at hExist
    simpa only [hFLevel] using hExist
  · have hAbove : n < LevelTree.lev x := by
      dsimp [n] at hx
      omega
    let a := LevelTree.ancestor x n (Nat.le_of_lt hAbove)
    have haLevel : LevelTree.lev a = n :=
      LevelTree.level_ancestor x n (Nat.le_of_lt hAbove)
    have haLe : a ≤ x :=
      LevelTree.ancestor_le x n (Nat.le_of_lt hAbove)
    have haLt : a < x := by
      refine lt_of_le_of_ne haLe ?_
      intro heq
      have he := congrArg LevelTree.lev heq
      omega
    obtain ⟨b,hab,hbx⟩ := LevelTree.exists_covBy_between haLt
    obtain ⟨p,c,hSucc⟩ := (admissibleKptSTree family).s3 hab
    let q := LevelTree.ancestor a (n-1) (by omega)
    have hqLevel : LevelTree.lev q = n-1 :=
      LevelTree.level_ancestor a (n-1) (by omega)
    have hPrev : LevelTree.lev q + 1 = LevelTree.lev a := by
      dsimp [n] at haLevel
      omega
    have hqEq : LevelTree.lev q = LevelTree.lev q₀ := by
      dsimp [n] at hqLevel
      omega
    have haEq : LevelTree.lev a = LevelTree.lev a₀ := by
      exact haLevel
    have hGapA : LevelTree.lev (F q) + 1 < LevelTree.lev (F a) :=
      gap_of_equal_source_levels family F q₀ a₀ q a hqEq haEq hgap
    have hExist := upper_deleted_image_type_admissible
      family F q a b x p c hPrev hGapA hSucc hbx
    have hFLevel : LevelTree.lev (F a) = LevelTree.lev (F a₀) :=
      F.level_eq_of_level_eq haEq
    dsimp at hExist
    simpa only [hFLevel] using hExist

end SuccessorTree.V10

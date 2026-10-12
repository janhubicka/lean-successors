import SuccessorTree.V10.LevelRemovalUniformOrder
import SuccessorTree.V10.LevelRemovalBoundaryWeakSucc
import Mathlib.Tactic

/-!
# Genuine weak successors below and across the first M2 deletion gap

For the intrinsic Kpt deletion function D constructed from a strict
gap in F, every source successor whose base lies below the first
affected level is weakly preserved. There are only two cases:

* both source endpoints lie below the boundary: D agrees exactly
  with F on base, target and parameter list;
* the edge crosses from level n-1 to level n: D fixes the base and
  every parameter, and the genuine weak image successor supplied by
  F lies below the coordinate-deleted upper target.

The crossing case is WEAK: it neither identifies the successor with
D(b) nor assumes a successor-preservation axiom for D. The proof uses
the already checked raw cross-gap prefix theorem, not an E-age test.
-/

namespace SuccessorTree.V10

private theorem map_eq_of_pointwise_on_list
    {α β : Type*} (p : List α) (f g : α → β)
    (h : ∀ x ∈ p, f x = g x) :
    p.map f = p.map g := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
      have hx : f x = g x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = g y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons, hx]
      rw [ih hxs]

/-- Every successor parameter of an edge whose base is below the
source gap boundary is fixed by the intrinsic deletion function,
relative to F. The empty list is treated without special cases. -/
theorem uniformGapDeletedKpt_low_parameter_list
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ a b : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (p : List (AdmissibleKptNode family))
    (c : AdmissibleKptSigma family)
    (hSucc : (admissibleKptSTree family).succ a p c = some b)
    (hALow : LevelTree.lev a < LevelTree.lev a₀) :
    p.map (uniformGapDeletedKpt family F q₀ a₀ hprev hgap) =
      p.map F := by
  apply map_eq_of_pointwise_on_list
  intro x hx
  have hxLow := (admissibleKptSTree family).parameter_level_lt hSucc hx
  exact uniformGapDeletedKpt_below family F q₀ a₀ hprev hgap x
    (by omega)

/-- The genuine weak image successor on the crossing edge remains
below the intrinsic deleted upper image. The base and parameters
have not changed, so the same actual old image successor witnesses
weak successor preservation for D at that edge. -/
theorem uniformGapDeletedKpt_crossing_weak_succ
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ a b : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (p : List (AdmissibleKptNode family))
    (c : AdmissibleKptSigma family)
    (hSucc : (admissibleKptSTree family).succ a p c = some b)
    (hBAt : LevelTree.lev b = LevelTree.lev a₀) :
    ∃ d : AdmissibleKptNode family,
      (admissibleKptSTree family).succ
        (uniformGapDeletedKpt family F q₀ a₀ hprev hgap a)
        (p.map (uniformGapDeletedKpt family F q₀ a₀ hprev hgap)) c =
          some d ∧
      d ≤ uniformGapDeletedKpt family F q₀ a₀ hprev hgap b := by
  have hCov : a ⋖ b :=
    (admissibleKptSTree family).covBy_of_succ_eq_some hSucc
  have hBL : LevelTree.lev b = LevelTree.lev a + 1 :=
    LevelTree.covBy_level_eq hCov
  have hALow : LevelTree.lev a < LevelTree.lev a₀ := by omega
  have hA :
      uniformGapDeletedKpt family F q₀ a₀ hprev hgap a = F a :=
    uniformGapDeletedKpt_below family F q₀ a₀ hprev hgap a hALow
  have hp :
      p.map (uniformGapDeletedKpt family F q₀ a₀ hprev hgap) =
        p.map F :=
    uniformGapDeletedKpt_low_parameter_list
      family F q₀ a₀ a b hprev hgap p c hSucc hALow
  obtain ⟨d,hMapped,hm,hBelow⟩ :=
    weak_image_successor_below_deleted_boundary family F q₀ a₀
      a b p c hprev hgap hSucc hBAt
  have hbHigh : LevelTree.lev a₀ ≤ LevelTree.lev b := by omega
  obtain ⟨hm',hRaw⟩ :=
    uniformGapDeletedKpt_above_raw
      family F q₀ a₀ hprev hgap b hbHigh
  have hDbelow :
      d ≤ uniformGapDeletedKpt family F q₀ a₀ hprev hgap b := by
    change d.1 ≤
      (uniformGapDeletedKpt family F q₀ a₀ hprev hgap b).1
    rw [hRaw]
    exact hBelow
  refine ⟨d,?_,hDbelow⟩
  simpa only [hA, hp] using hMapped

/-- All source successors with base strictly below the first
affected level satisfy the ACTUAL weak successor property for
the intrinsic deletion function, including the crossing edge.
Only successors based at or above the boundary remain open. -/
theorem uniformGapDeletedKpt_low_weak_succ
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ a b : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (p : List (AdmissibleKptNode family))
    (c : AdmissibleKptSigma family)
    (hSucc : (admissibleKptSTree family).succ a p c = some b)
    (hALow : LevelTree.lev a < LevelTree.lev a₀) :
    ∃ d : AdmissibleKptNode family,
      (admissibleKptSTree family).succ
        (uniformGapDeletedKpt family F q₀ a₀ hprev hgap a)
        (p.map (uniformGapDeletedKpt family F q₀ a₀ hprev hgap)) c =
          some d ∧
      d ≤ uniformGapDeletedKpt family F q₀ a₀ hprev hgap b := by
  have hCov : a ⋖ b :=
    (admissibleKptSTree family).covBy_of_succ_eq_some hSucc
  have hBL : LevelTree.lev b = LevelTree.lev a + 1 :=
    LevelTree.covBy_level_eq hCov
  by_cases hbLow : LevelTree.lev b < LevelTree.lev a₀
  · have hA := uniformGapDeletedKpt_below family F q₀ a₀
      hprev hgap a hALow
    have hB := uniformGapDeletedKpt_below family F q₀ a₀
      hprev hgap b hbLow
    have hp := uniformGapDeletedKpt_low_parameter_list
      family F q₀ a₀ a b hprev hgap p c hSucc hALow
    obtain ⟨d,hMapped,hBelow⟩ := F.weak_succ' hSucc
    refine ⟨d,?_,?_⟩
    · simpa only [hA,hp] using hMapped
    · simpa only [hB] using hBelow
  · have hBAt : LevelTree.lev b = LevelTree.lev a₀ := by omega
    exact uniformGapDeletedKpt_crossing_weak_succ
      family F q₀ a₀ a b hprev hgap p c hSucc hBAt

end SuccessorTree.V10

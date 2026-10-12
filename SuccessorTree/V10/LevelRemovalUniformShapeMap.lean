import SuccessorTree.V10.LevelRemovalUniformHighWeakSucc
import SuccessorTree.WeakSuccessorInjectivity
import SuccessorTree.V10.ConcreteKptM1
import Mathlib.Tactic

/-!
# The intrinsic M2 deletion candidate is an actual shape-preserving map

Once its upper weak-successor law is checked, the intrinsic
piecewise coordinate-deletion function has all four shape-map fields.
The strict level map and root extension were proved independently.
Injectivity is not assumed: it follows from the reusable general
S-tree theorem that strict level order, root extension and genuine
weak successors force injectivity.

This provides the first global shape-preserving deletion factor
F₁ of the M2 argument. It does NOT yet supply the one-level F₂ or
the corrected finite L-only B3 age-necessity/factorization theorem,
and it does not assert the original-language Kpt adapter.
-/

namespace SuccessorTree.V10

/-- Assemble a genuine ShapeMap from the checked intrinsic
coordinate-deletion construction. No M2 axiom or injectivity
hypothesis is added to the model. -/
noncomputable def uniformGapDeletedShapeMap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀)) :
    SuccessorTree.ShapeMap (admissibleKptSTree family) := by
  let D : AdmissibleKptNode family → AdmissibleKptNode family :=
    uniformGapDeletedKpt family F q₀ a₀ hprev hgap
  have hLevel :
      ∀ {x y : AdmissibleKptNode family},
        LevelTree.lev x = LevelTree.lev y →
        LevelTree.lev (D x) = LevelTree.lev (D y) := by
    intro x y hxy
    exact uniformGapDeletedKpt_level_eq family F q₀ a₀
      hprev hgap hxy
  have hStrict :
      ∀ {x y : AdmissibleKptNode family},
        LevelTree.lev x < LevelTree.lev y →
        LevelTree.lev (D x) < LevelTree.lev (D y) := by
    intro x y hxy
    exact uniformGapDeletedKpt_level_strictMono family F q₀ a₀
      hprev hgap hxy
  have hWeak :
      ∀ {a b : AdmissibleKptNode family}
        {p : List (AdmissibleKptNode family)}
        {c : AdmissibleKptSigma family},
        (admissibleKptSTree family).succ a p c = some b →
        ∃ d : AdmissibleKptNode family,
          (admissibleKptSTree family).succ (D a) (p.map D) c =
            some d ∧ d ≤ D b := by
    intro a b p c hSucc
    exact uniformGapDeletedKpt_weak_succ
      family F q₀ a₀ hprev hgap hSucc
  have hRoot :
      ∀ {a : AdmissibleKptNode family},
        LevelTree.lev a = 0 → a ≤ D a := by
    intro a ha
    exact uniformGapDeletedKpt_root_le family F q₀ a₀
      hprev hgap a ha
  have hInjective : Function.Injective D :=
    SuccessorTree.injective_of_level_order_and_weak_successors
      (admissibleKptSTree family) D hLevel hStrict hWeak hRoot
  exact
    { toFun := D
      injective' := hInjective
      level_preserving' := hLevel
      weak_succ' := hWeak
      root_le' := hRoot }

/-- The first global deletion factor belongs to the paper's
root-preserving Kpt monoid whenever F does. Its level-zero
effect is exactly F's; it is not a new monoid axiom. -/
theorem uniformGapDeletedShapeMap_mem_KptM
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hFM : F ∈ KptM family)
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀)) :
    uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap ∈
      KptM family := by
  intro x hx
  have hLow : LevelTree.lev x < LevelTree.lev a₀ := by
    omega
  change LevelTree.lev
    (uniformGapDeletedKpt family F q₀ a₀ hprev hgap x) = 0
  rw [uniformGapDeletedKpt_below family F q₀ a₀
    hprev hgap x hLow]
  exact hFM x hx

/-- The global map has the intended strict lowered-image level
function, inherited from the intrinsic construction. The map is
already a genuine ShapeMap, not just an arbitrary total function. -/
theorem uniformGapDeletedShapeMap_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : AdmissibleKptNode family) :
    LevelTree.lev
      (uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x) =
      if LevelTree.lev x < LevelTree.lev a₀ then
        LevelTree.lev (F x) else LevelTree.lev (F x) - 1 := by
  change LevelTree.lev
    (uniformGapDeletedKpt family F q₀ a₀ hprev hgap x) = _
  exact uniformGapDeletedKpt_level family F q₀ a₀
    hprev hgap x


/-- Deleting the intrinsic gap leaves all lower source images literally
unchanged. This is the first equality needed by a later M2 factorization,
and is stronger than preservation of their image levels. -/
theorem uniformGapDeletedShapeMap_below
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : AdmissibleKptNode family)
    (hLow : LevelTree.lev x < LevelTree.lev a₀) :
    uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x = F x := by
  change uniformGapDeletedKpt family F q₀ a₀ hprev hgap x = F x
  exact uniformGapDeletedKpt_below family F q₀ a₀ hprev hgap x hLow

/-- The original map omits the chosen target gap m, while the
intrinsic global deletion factor meets m. This certifies a genuine
range improvement, not the still-open complementary insertion factor. -/
theorem uniformGapDeletedShapeMap_fills_gap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀)) :
    F.Skips (LevelTree.lev (F a₀) - 1) ∧
      LevelTree.lev (F a₀) - 1 ∈
        (uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap).levelRange := by
  have hFSkip : F.Skips (LevelTree.lev (F a₀) - 1) := by
    intro hRange
    obtain ⟨x,hx⟩ := hRange
    by_cases hLow : LevelTree.lev x < LevelTree.lev a₀
    · have hXQ : LevelTree.lev x ≤ LevelTree.lev q₀ := by omega
      have hBound := shapeMap_level_le_of_level_le family F hXQ
      omega
    · have hAX : LevelTree.lev a₀ ≤ LevelTree.lev x :=
        Nat.le_of_not_gt hLow
      have hBound := shapeMap_level_le_of_level_le family F hAX
      omega
  refine ⟨hFSkip, ?_⟩
  refine ⟨a₀, ?_⟩
  simpa using
    (uniformGapDeletedShapeMap_level family F q₀ a₀ hprev hgap a₀)

end SuccessorTree.V10

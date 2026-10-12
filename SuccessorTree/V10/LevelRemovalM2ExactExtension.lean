import SuccessorTree.V10.LevelRemovalSkipsOnly
import SuccessorTree.V10.LevelRemovalM2Criterion
import Mathlib.Tactic

/-!
# M2 as extension of an exact boundary insertion graph

Once the intrinsic deletion factor D is a genuine ShapeMap, the
remaining assertion is precisely that the partial map
  D(x) |-> F(x),  lev(x) = n,
extends to a Kpt shape map skipping only m = lev(F(a₀))-1.

This is a strictly weaker hypothesis than the existence of corrected
B3 prescribed data. An arbitrary one-gap ShapeMap automatically fixes
all images F(x) from source levels below n; the exact agreement
condition is therefore necessary only on source level n itself.

Neither theorem assumes the SMTree M2 axiom, or a lifting of finite
L-only age witnesses into E-partial structures.
-/

namespace SuccessorTree.V10

/-- For the **specific intrinsic deletion first factor**, agreement
with an arbitrary one-gap map through the boundary is equivalent to
agreement just at the boundary. Unlike the earlier prescribed-B3
criterion, no finite insertion data are required. -/
theorem uniformGapDeletedShapeMap_boundary_extension_iff
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀)) :
    (∃ G : SuccessorTree.ShapeMap (admissibleKptSTree family),
      G ∈ KptM family ∧
      G.SkipsOnly (LevelTree.lev (F a₀) - 1) ∧
      ∀ x : AdmissibleKptNode family,
        LevelTree.lev x ≤ LevelTree.lev a₀ →
        G (uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x) =
          F x) ↔
    (∃ G : SuccessorTree.ShapeMap (admissibleKptSTree family),
      G ∈ KptM family ∧
      G.SkipsOnly (LevelTree.lev (F a₀) - 1) ∧
      ∀ x : AdmissibleKptNode family,
        LevelTree.lev x = LevelTree.lev a₀ →
        G (uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x) =
          F x) := by
  constructor
  · rintro ⟨G,hGM,hSkip,hAll⟩
    exact ⟨G,hGM,hSkip,fun x hx => hAll x (Nat.le_of_eq hx)⟩
  · rintro ⟨G,hGM,hSkip,hBoundary⟩
    refine ⟨G,hGM,hSkip,?_⟩
    intro x hx
    rcases lt_or_eq_of_le hx with hLow | hEq
    · rw [uniformGapDeletedShapeMap_below family F q₀ a₀
        hprev hgap x hLow]
      have hXQ : LevelTree.lev x ≤ LevelTree.lev q₀ := by omega
      have hFBound := shapeMap_level_le_of_level_le family F hXQ
      have hFBelow :
          LevelTree.lev (F x) < LevelTree.lev (F a₀) - 1 := by
        omega
      exact kptShapeMap_fixed_below_skip family G
        (LevelTree.lev (F a₀) - 1) hSkip (F x) hFBelow
    · exact hBoundary x hEq

/-- The actual M2 two-map conclusion follows from an arbitrary
one-gap extension of the intrinsic boundary restoration data,
with NO corrected B3 premise. Thus the remaining proof burden is
to construct the extension, not to reprove its lower-level equality. -/
theorem uniformGapDeletedShapeMap_factorization_of_boundary_extension
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hFM : F ∈ KptM family)
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (G : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hGM : G ∈ KptM family)
    (hSkip : G.SkipsOnly (LevelTree.lev (F a₀) - 1))
    (hBoundary : ∀ x : AdmissibleKptNode family,
      LevelTree.lev x = LevelTree.lev a₀ →
      G (uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x) =
        F x) :
    ∃ F1 F2 : SuccessorTree.ShapeMap (admissibleKptSTree family),
      F1 ∈ KptM family ∧
      F2 ∈ KptM family ∧
      F2.SkipsOnly (LevelTree.lev (F a₀) - 1) ∧
      ∀ x : AdmissibleKptNode family,
        LevelTree.lev x ≤ LevelTree.lev a₀ →
        F2 (F1 x) = F x := by
  have hAll :=
    (uniformGapDeletedShapeMap_boundary_extension_iff
      family F q₀ a₀ hprev hgap).2
      ⟨G,hGM,hSkip,hBoundary⟩
  obtain ⟨G',hGM',hSkip',hAgree⟩ := hAll
  exact ⟨uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap,
    G',uniformGapDeletedShapeMap_mem_KptM family F hFM q₀ a₀
      hprev hgap,hGM',hSkip',hAgree⟩

end SuccessorTree.V10

import SuccessorTree.V10.M2BoundaryPrescribedB2
import SuccessorTree.V10.M2CompatibleFactorization
import Mathlib.Tactic

/-!
# M2 factorization from the one actual boundary CompatibleB3 test

The first intrinsic deletion factor D, its injectivity, B1, and B2
are established from F. This module checks that the constructed
boundary PrescribedBoringData contains all deleted boundary images
and agrees literally with F on each corresponding target. Therefore
the already proved prescribed one-gap extension theorem gives the
complete two-map M2 factorization with ONLY the finite L-age
CompatibleB3 assumption about these actual boundary data.

This does not assert that CompatibleB3 holds: that is the remaining
source-label-extraction and forbidden-age proof. No M2 axiom is used.
-/

namespace SuccessorTree.V10

/-- Every output in the entire actual boundary prescription is
admissible because it is literally the F-image of one admissible
source node, not an arbitrary formal L+ extension. -/
theorem m2Boundary_prescribed_targets_admissible
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀)) :
    ∀ S, S ∈ (m2Boundary_prescribedData family F q₀ a₀ hprev hgap).source →
      IsAdmissibleRawType family
        (⟨(LevelTree.lev (F a₀)-1)+1,
          (m2Boundary_prescribedData family F q₀ a₀ hprev hgap).target S⟩ :
          RawPartialTypeNode db du dd) := by
  intro S hS
  change S ∈ Set.range
    (m2Boundary_sourceType family F q₀ a₀ hprev hgap) at hS
  obtain ⟨x,rfl⟩ := hS
  rw [m2Boundary_prescribed_target family F q₀ a₀ hprev hgap x]
  rw [←m2Boundary_target_raw family F q₀ a₀ hprev hgap x]
  exact (F x.1).2

/-- On the exact first affected source level, both the old deleted
boundary inputs and the original F-targets are represented with full
raw-node equality in the genuine B1/B2 prescription. -/
theorem m2Boundary_prescribed_covers_all
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀)) :
    ∀ x : AdmissibleKptNode family,
      LevelTree.lev x = LevelTree.lev a₀ →
      ∃ (S : PartialTypeWithE (LevelTree.lev (F a₀)-1) db du dd)
        (hS : S ∈ (m2Boundary_prescribedData family F q₀ a₀ hprev hgap).source)
        (hAd : IsAdmissibleRawType family
          (⟨LevelTree.lev (F a₀)-1,S⟩ :
            RawPartialTypeNode db du dd)),
        uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x =
          (⟨⟨LevelTree.lev (F a₀)-1,S⟩,hAd⟩ :
            AdmissibleKptNode family) ∧
        (F x).1 =
          (⟨(LevelTree.lev (F a₀)-1)+1,
            (m2Boundary_prescribedData family F q₀ a₀ hprev hgap).target S⟩ :
            RawPartialTypeNode db du dd) := by
  intro x hx
  let i : M2BoundaryIndex family a₀ := ⟨x,hx⟩
  let S := m2Boundary_sourceType family F q₀ a₀ hprev hgap i
  have hS : S ∈ (m2Boundary_prescribedData family F q₀ a₀ hprev hgap).source :=
    m2Boundary_prescribed_source family F q₀ a₀ hprev hgap i
  have hAd : IsAdmissibleRawType family
      (⟨LevelTree.lev (F a₀)-1,S⟩ : RawPartialTypeNode db du dd) := by
    rw [←m2Boundary_source_raw family F q₀ a₀ hprev hgap i]
    exact (uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x).2
  refine ⟨S,hS,hAd,?_,?_⟩
  · apply Subtype.ext
    exact m2Boundary_source_raw family F q₀ a₀ hprev hgap i
  · rw [m2Boundary_prescribed_target family F q₀ a₀ hprev hgap i]
    exact m2Boundary_target_raw family F q₀ a₀ hprev hgap i

/-- The actual first-gap M2 factorization, with its ONLY remaining
mathematical hypothesis spelled out: the corrected finite L-age
CompatibleB3 condition for the genuine boundary prescription.
No additional abstract extension map or prepackaged source labels
are assumptions. -/
theorem m2_factorization_of_actual_boundary_compatibleB3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hFM : F ∈ KptM family)
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (hB3 :
      (m2Boundary_prescribedData family F q₀ a₀ hprev hgap).CompatibleB3 family) :
    ∃ F1 F2 : SuccessorTree.ShapeMap (admissibleKptSTree family),
      F1 ∈ KptM family ∧
      F2 ∈ KptM family ∧
      F2.SkipsOnly (LevelTree.lev (F a₀)-1) ∧
      ∀ x : AdmissibleKptNode family,
        LevelTree.lev x ≤ LevelTree.lev a₀ →
        F2 (F1 x) = F x := by
  have hPos : 0 < LevelTree.lev (F a₀)-1 := by
    omega
  exact uniformGapDeletedShapeMap_factorization_of_compatibleB3
    family F hFM q₀ a₀ hprev hgap
    (m2Boundary_prescribedData family F q₀ a₀ hprev hgap)
    hB3
    (m2Boundary_prescribed_targets_admissible family F q₀ a₀ hprev hgap)
    hPos
    (m2Boundary_prescribed_covers_all family F q₀ a₀ hprev hgap)

end SuccessorTree.V10

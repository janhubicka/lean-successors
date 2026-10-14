import SuccessorTree.V10.M2BoundaryFinalCriterion
import Mathlib.Tactic

/-!
# Genuine source labels from arbitrary upper finite L-age B3 vertices

The boundary source family is the entire image of the actual
deletion map D on its first affected original level. Thus EVERY
upper L-type allowed by CompatibleB3 literally comes from a
particular genuine original Kpt source node. We do not need to
postulate an E-structure on the arbitrary L-age witness, or
postulate an abstract family of admissible source types.

This is the first selection half of the remaining corrected B3
proof. Recovering mutual source compatibility and the low/low
retained records from this actual indexing follows separately.
-/

namespace SuccessorTree.V10

/-- Every upper vertex in a finite compatible L-age test has one
ACTUAL original source boundary node as its label. Its deleted type
is compatible with the chosen base source type, and its complete
target ordinary L-type (including the gap coordinate) is literally
the L reduct of F applied to that source node. -/
theorem m2Boundary_upper_vertex_has_source_index
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (S0 : PartialTypeWithE (LevelTree.lev (F a₀)-1) db du dd)
    (W : AgeTestModel db du dd)
    (hUpper : UpperTypesPrescribed W (LevelTree.lev (F a₀)-1)
      ((m2Boundary_prescribedData family F q₀ a₀ hprev hgap).CompatibleUpperLType S0))
    (w : Nat)
    (hw : w ∈ W.carrier)
    (hmw : LevelTree.lev (F a₀)-1 < w) :
    ∃ i : M2BoundaryIndex family a₀,
      SameOrdinaryAtCut
        (m2Boundary_sourceType family F q₀ a₀ hprev hgap i) S0 ∧
      RelationalPrefixType.ofAgeModel W
        ((LevelTree.lev (F a₀)-1)+1) w =
        (m2Boundary_targetType family F q₀ a₀ hprev hgap i).lReduct := by
  obtain ⟨S,hS,hComp,hType⟩ := hUpper w hw hmw
  change S ∈ Set.range
    (m2Boundary_sourceType family F q₀ a₀ hprev hgap) at hS
  obtain ⟨i,hi⟩ := hS
  subst S
  refine ⟨i,hComp,?_⟩
  rw [m2Boundary_prescribed_target family F q₀ a₀ hprev hgap i] at hType
  exact hType

/-- The anchor of any compatible B3 test is also one actual source
boundary node, with exact complete source and target types. -/
theorem m2Boundary_base_has_source_index
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (S0 : PartialTypeWithE (LevelTree.lev (F a₀)-1) db du dd)
    (hS0 : S0 ∈
      (m2Boundary_prescribedData family F q₀ a₀ hprev hgap).source) :
    ∃ i0 : M2BoundaryIndex family a₀,
      m2Boundary_sourceType family F q₀ a₀ hprev hgap i0 = S0 ∧
      (m2Boundary_prescribedData family F q₀ a₀ hprev hgap).target S0 =
        m2Boundary_targetType family F q₀ a₀ hprev hgap i0 := by
  change S0 ∈ Set.range
    (m2Boundary_sourceType family F q₀ a₀ hprev hgap) at hS0
  obtain ⟨i0,hi0⟩ := hS0
  subst S0
  exact ⟨i0,rfl,m2Boundary_prescribed_target
    family F q₀ a₀ hprev hgap i0⟩

end SuccessorTree.V10

import SuccessorTree.V10.AdmissibleSigmaSTree
import SuccessorTree.Monoid
import Mathlib.Tactic

/-!
# M1 for the Kpt monoid fixing level zero

Section 6.3.2 takes M to consist of *all* shape-preserving maps
on Kpt whose level map satisfies \widetilde F(0)=0.
The restriction is meaningful even if the tree has several roots:
because a shape map is level-preserving, it is equivalent to fixing
every root pointwise.

This module proves the complete M1 closure of that exact family:
identity, composition and pointwise fusion limits. These are proved
using the existing generic ShapeMap constructions and the concrete
admissible-Sigma S-tree. No additional monoid axiom is assumed.

In particular, this does NOT produce an SMTree instance:
M2 (removing a skipped level) and M3 (duplication of a successor
transition at a later level) are still separate obligations.
-/

namespace SuccessorTree.V10

/-- The paper's restriction \widetilde F(0)=0, in a formulation
that does not assume a pre-existing total level function. -/
def RootFixingKpt
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : ShapeMap (admissibleKptSTree family)) : Prop :=
  ∀ a : AdmissibleKptNode family,
    LevelTree.lev a = 0 → LevelTree.lev (F a) = 0

/-- Fixing the zeroth level is equivalent to fixing all roots
pointwise, since shape-preserving maps have the root-extension
property and the level-zero ancestors are unique. -/
theorem rootFixingKpt_iff_root_fixed
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : ShapeMap (admissibleKptSTree family)) :
    RootFixingKpt family F ↔
      ∀ a : AdmissibleKptNode family,
        LevelTree.lev a = 0 → F a = a := by
  constructor
  · intro h a ha
    have hle : a ≤ F a := F.root_le' ha
    have hlevels : LevelTree.lev a = LevelTree.lev (F a) :=
      ha.trans (h a ha).symm
    exact LevelTree.same_level_of_le hle hlevels
  · intro h a ha
    rw [h a ha]
    exact ha

/-- The distinguished family M in Section 6.3.2; it contains
no arbitrary extra shape maps. -/
def rootFixingKptMonoid
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    Set (ShapeMap (admissibleKptSTree family)) :=
  {F | RootFixingKpt family F}

/-- M1, identity: all roots remain fixed. -/
theorem rootFixingKpt_id_mem
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    ShapeMap.id (admissibleKptSTree family) ∈
      rootFixingKptMonoid family := by
  intro a ha
  change LevelTree.lev a = 0
  exact ha

/-- M1, composition: a composition of two maps fixing
level zero also fixes level zero. -/
theorem rootFixingKpt_comp_mem
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F G : ShapeMap (admissibleKptSTree family))
    (hF : F ∈ rootFixingKptMonoid family)
    (hG : G ∈ rootFixingKptMonoid family) :
    F.comp G ∈ rootFixingKptMonoid family := by
  intro a ha
  change LevelTree.lev (F (G a)) = 0
  exact hF (G a) (hG a ha)

/-- M1, fusion: if all members of a stabilized sequence fix level
zero, its canonical pointwise fusion limit fixes level zero too.
Only the zeroth stage is needed on the zeroth source level. -/
theorem rootFixingKpt_fusion_mem
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : Nat → ShapeMap (admissibleKptSTree family))
    (hF : ∀ i, F i ∈ rootFixingKptMonoid family)
    (hstable : ShapeMap.FusionStable F) :
    ShapeMap.fusionLimit F hstable ∈
      rootFixingKptMonoid family := by
  intro a ha
  change LevelTree.lev ((ShapeMap.fusionLimit F hstable) a) = 0
  rw [ShapeMap.fusionLimit_apply, ha]
  exact hF 0 a ha

/-- All three M1 clauses packaged without inventing an SMTree
instance, which would require additional M2 and M3 witnesses. -/
theorem rootFixingKpt_M1
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    (ShapeMap.id (admissibleKptSTree family) ∈
      rootFixingKptMonoid family) ∧
    (∀ (F G : ShapeMap (admissibleKptSTree family)),
      F ∈ rootFixingKptMonoid family →
      G ∈ rootFixingKptMonoid family →
      F.comp G ∈ rootFixingKptMonoid family) ∧
    (∀ (F : Nat → ShapeMap (admissibleKptSTree family))
      (hF : ∀ i, F i ∈ rootFixingKptMonoid family)
      (hstable : ShapeMap.FusionStable F),
      ShapeMap.fusionLimit F hstable ∈
        rootFixingKptMonoid family) := by
  refine ⟨rootFixingKpt_id_mem family, ?_, ?_⟩
  · intro F G hF hG
    exact rootFixingKpt_comp_mem family F G hF hG
  · intro F hF hstable
    exact rootFixingKpt_fusion_mem family F hF hstable

end SuccessorTree.V10

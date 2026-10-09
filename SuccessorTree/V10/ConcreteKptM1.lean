import SuccessorTree.V10.AdmissibleSigmaSTree
import SuccessorTree.Monoid
import Mathlib.Tactic

/-!
# The M1 component of the Kpt shape-preserving monoid

In Section 6.3.2 the manuscript chooses M to be all shape-preserving
endomorphisms F of the partial-type tree with level map F̃(0)=0.
Since every level-zero node is sent to a common level, this can
equivalently be expressed as preservation of level zero for ALL
level-zero nodes.

We prove the identity, composition, and fusion-limit clauses of
(M1), using the actual admissible-Sigma S-tree, without assuming
M2 or M3. The root-extension axiom for a shape map makes these
maps literally fix each root, giving the manuscript's (E1).
The level-zero condition is preserved by fusion because the
value on roots is already frozen at the zeroth stage.

This does not establish Proposition 6.39: the paper-specific
level-removal, boring-extension, and duplication arguments
for M2/M3 remain to be formalized.
-/

namespace SuccessorTree.V10

open SuccessorTree

/-- The monoid in Section 6.3.2, formulated without a total
level-map function: preserve level zero on every root. -/
def KptM
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    Set (ShapeMap (admissibleKptSTree family)) :=
  {F | ∀ a : AdmissibleKptNode family,
    LevelTree.lev a = 0 → LevelTree.lev (F a) = 0}

/-- The identity belongs to the concrete Kpt shape family. -/
theorem kptM_id_mem
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    ShapeMap.id (admissibleKptSTree family) ∈ KptM family := by
  intro a ha
  simpa only [ShapeMap.id_apply] using ha

/-- The level-zero condition survives composition: no new
geometric or forbidden-age hypothesis is required. -/
theorem kptM_comp_mem
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {F G : ShapeMap (admissibleKptSTree family)}
    (hF : F ∈ KptM family) (hG : G ∈ KptM family) :
    F.comp G ∈ KptM family := by
  intro a ha
  exact hF (G a) (hG a ha)

/-- The level-zero condition survives a pointwise fusion limit
because the value on a root is already fixed at stage zero. -/
theorem kptM_fusion_mem
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : Nat → ShapeMap (admissibleKptSTree family))
    (hmem : ∀ i, F i ∈ KptM family)
    (hstable : ShapeMap.FusionStable F) :
    ShapeMap.fusionLimit F hstable ∈ KptM family := by
  intro a ha
  have h0 := hmem 0 a ha
  simpa only [ShapeMap.fusionLimit_apply, ha] using h0

/-- The explicit M1 closure triple for the concrete Kpt monoid,
with no proof step outsourced to the SMTree axioms. -/
theorem kptM1
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    ShapeMap.id (admissibleKptSTree family) ∈ KptM family ∧
    (∀ {F G : ShapeMap (admissibleKptSTree family)},
      F ∈ KptM family → G ∈ KptM family →
      F.comp G ∈ KptM family) ∧
    (∀ (F : Nat → ShapeMap (admissibleKptSTree family))
      (hmem : ∀ i, F i ∈ KptM family)
      (hstable : ShapeMap.FusionStable F),
      ShapeMap.fusionLimit F hstable ∈ KptM family) :=
by
  refine ⟨kptM_id_mem family, ?_, ?_⟩
  · intro F G hF hG
    exact kptM_comp_mem family hF hG
  · intro F hmem hstable
    exact kptM_fusion_mem family F hmem hstable

/-- A Kpt shape map whose zeroth image level is zero literally
fixes the level-zero node. The target root cannot change to a
different root because shape maps extend every source root. -/
theorem kptM_fixes_roots
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {F : ShapeMap (admissibleKptSTree family)}
    (hF : F ∈ KptM family)
    (a : AdmissibleKptNode family)
    (ha : LevelTree.lev a = 0) :
    F a = a := by
  have hle : a ≤ F a := F.root_le' ha
  have hlevel : LevelTree.lev a = LevelTree.lev (F a) :=
    ha.trans (hF a ha).symm
  exact (LevelTree.same_level_of_le hle hlevel).symm

end SuccessorTree.V10

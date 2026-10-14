import SuccessorTree.V10.M2FullAxiom
import SuccessorTree.V10.M3LiteralDuplication
import SuccessorTree.V10.ConcreteKptM1
import Mathlib.Tactic

/-!
# The complete normalized Kpt (S,M)-tree

This module combines the independently proved S-tree structure,
M1 monoid closure, literal M2 one-gap factorization, and literal
M3 duplication into the actual generic successor-tree interface.

No SMTree axiom is used as a premise. In particular M2 is
obtained from the arbitrary finite L-only CompatibleB3 non-edge
proof, not provided as a constructor assumption.

This is the normalized finite unary/directed-binary/diagonal
presentation. The general manuscript signature and nullary
convention remain separate editorial/formalization tasks.
-/

namespace SuccessorTree.V10

/-- The actual admissible partial-type S-tree and the monoid of
root-level-preserving shape maps satisfy all three manuscript
axioms M1, M2 and M3, in the normalized Boolean-record setting. -/
noncomputable def normalizedKptSMTree
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    SuccessorTree.SMTree (admissibleKptSTree family) where
  M := KptM family
  id_mem := kptM_id_mem family
  comp_mem := by
    intro F G hF hG
    exact kptM_comp_mem family hF hG
  fusion_mem := by
    intro F hmem hstable
    exact kptM_fusion_mem family F hmem hstable
  m2 := kptM2 family
  m3 := by
    intro n ell hn
    obtain ⟨Φ,hΦ,hSkip,hAll⟩ :=
      m3OneGapShapeMap_literalM3 family n ell hn
    refine ⟨Φ,hΦ,hSkip,?_⟩
    intro a b p c s ha hb hStep hBelow
    exact hAll a b s p c ha hb hStep hBelow

end SuccessorTree.V10

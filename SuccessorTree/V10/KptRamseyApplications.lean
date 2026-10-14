import SuccessorTree.V10.KptCompleteSMTree
import SuccessorTree.ShapeFiniteRamsey
import SuccessorTree.ShapeEllentuckRamsey
import SuccessorTree.ShapeFiniteCorollaries

/-!
# Ramsey applications for the actual normalized admissible Kpt tree

The complete normalized Kpt `SMTree` is now proved directly from its
finite L-age model, including M2 by the simultaneous non-edge padding
argument. This module applies the GENERAL successor-tree Ramsey theorem
to that CONCRETE instance. In particular the resulting statements are
not conditional on an abstract `SMTree` hypothesis supplied by a caller.

Two independent routes to finite-dimensional homogeneity are stated:
direct successor fusion and fat-tree Ellentuck. The bounded and
exact-terminal finite corollaries follow from the same concrete instance.

Scope: finite unary, directed binary and diagonal Boolean tables,
a normalized forbidden family with allowed neutral singleton, and the
existing Kpt admissibility predicate. The adapter to arbitrary finite
relational languages, with relations of arity greater than two and
fixed nullary interpretations, is NOT established here.
-/

namespace SuccessorTree.V10

universe w

/-- The shape Ramsey theorem for the *actual* forbidden-free finite
partial-type Kpt class; M1--M3 are proved rather than hypotheses. -/
theorem normalizedKpt_shapeRamsey
    {db du dd : Nat} {κ : Type w} [Fintype κ]
    (family : List (NormalizedForbidden db du dd))
    (n k : Nat)
    (colour : SuccessorTree.SMTree.AM (normalizedKptSMTree family) n k → κ) :
    ∃ W : SuccessorTree.SMTree.ShapeSubspace (normalizedKptSMTree family) n,
      ∀ a b : SuccessorTree.SMTree.AM (normalizedKptSMTree family) n k,
        colour ((normalizedKptSMTree family).shapeActK n k W a) =
          colour ((normalizedKptSMTree family).shapeActK n k W b) := by
  exact (normalizedKptSMTree family).shapePreservingRamsey n k colour

/-- An independent derivation of exactly the same concrete Kpt Ramsey
statement using the checked fat-tree Ellentuck proof route. -/
theorem normalizedKpt_shapeRamsey_viaFatEllentuck
    {db du dd : Nat} {κ : Type w} [Fintype κ]
    (family : List (NormalizedForbidden db du dd))
    (n k : Nat)
    (colour : SuccessorTree.SMTree.AM (normalizedKptSMTree family) n k → κ) :
    ∃ W : SuccessorTree.SMTree.ShapeSubspace (normalizedKptSMTree family) n,
      ∀ a b : SuccessorTree.SMTree.AM (normalizedKptSMTree family) n k,
        colour ((normalizedKptSMTree family).shapeActK n k W a) =
          colour ((normalizedKptSMTree family).shapeActK n k W b) := by
  exact (normalizedKptSMTree family).shapePreservingRamsey_viaFatEllentuck
    n k colour

/-- Concrete bounded-terminal Ramsey theorem for the normalized Kpt
class, obtained from the already checked abstract finite corollary. -/
theorem normalizedKpt_shapeRamsey_bounded
    {db du dd : Nat} {κ : Type w}
    [Fintype κ] [Nonempty κ]
    (family : List (NormalizedForbidden db du dd))
    (n k m : Nat) (hk : 0 < k) (hm : 0 < m) :
    ∃ N : Nat,
      SuccessorTree.SMTree.BoundedRamseyAt
        (normalizedKptSMTree family) κ n k m N hm hk := by
  exact SuccessorTree.SMTree.shapeRamsey_bounded
    (κ := κ) (normalizedKptSMTree family) n k m hk hm

/-- Concrete exact-terminal Ramsey theorem, including the special
terminal-zero boundary case handled by the generic theorem. -/
theorem normalizedKpt_shapeRamsey_exact
    {db du dd : Nat} {κ : Type w}
    [Fintype κ] [Nonempty κ]
    (family : List (NormalizedForbidden db du dd))
    (n k m : Nat) (hk : 0 < k) (hm : 0 < m) :
    ∃ N : Nat,
      SuccessorTree.SMTree.ExactRamseyAt
        (normalizedKptSMTree family) κ n k m N hm hk := by
  exact SuccessorTree.SMTree.shapeRamsey_exact
    (κ := κ) (normalizedKptSMTree family) n k m hk hm

end SuccessorTree.V10

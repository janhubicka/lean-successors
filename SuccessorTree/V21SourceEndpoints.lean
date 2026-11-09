import SuccessorTree.V10.TypeRespectingRamsey
import SuccessorTree.FreeAncestralSMTree
import SuccessorTree.HomogeneousSuccessorCodes

/-!
# Exact v21 manuscript source endpoints

The type-respecting definitions appearing in the new v21 application section
are represented by the intrinsic full profile maps of the V10 library.
These examples check the two named paper endpoints with precisely their
exported types, without adding compatibility wrappers or fresh axioms.

The Appendix A free ancestral instance uses the existing full shape monoid.
`HomogeneousSuccessorCodes` validates the local insertion-stability
hypothesis used in the proposed generalisation, but its implication to a
full monoid theorem has not yet been formalised in this module.
-/

namespace SuccessorTree.V21

open SuccessorTree.V10

variable {db du dd : Nat}

/-- The intrinsic finite type-respecting maps extend to monoid elements. -/
example {family : List (NormalizedForbidden db du dd)}
    (A : FiniteTypeBase family) (h : TypeRespectingEmbedding A) :
    ∃ F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family),
      ∀ u : TypeProfile A, F u.1 = h.1 u :=
  TypeRespectingEmbedding.exists_extension A h

/-- The v21 type-respecting Ramsey theorem, under the normalized hypotheses. -/
example {κ : Type*} [Fintype κ]
    (family : List (NormalizedForbidden db du dd))
    (A : FiniteTypeBase family)
    (colour : TypeRespectingEmbedding A → κ) :
    ∃ F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family),
      ∀ f g : TypeRespectingEmbedding A,
        colour (TypeRespectingEmbedding.act A F f) =
          colour (TypeRespectingEmbedding.act A F g) :=
  normalizedKpt_typeRespectingRamsey family A colour

end SuccessorTree.V21

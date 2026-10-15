import SuccessorTree.V10.GPlusNeutralCapType
import SuccessorTree.ShapeOrderReflection
import SuccessorTree.Envelope
import Mathlib.Tactic

/-!
# V10 Definition 6.43: lift genuine Kpt envelope coverage to G+

For a genuine strict representing pair P=(S,T), the manuscript
identifies the G+ vertex v(S,T). If an actual Kpt ShapeMap F has
BOTH S and T in its range, then their unique shape preimages s,t
are again strictly comparable: shape maps REFLECT the prefix order.

Consequently Q=(s,t) is another genuine admissible representing pair
and F(Q)=P. The previously checked representative-independence
equation identifies its image vertex with the actual induced G+ action.
Thus v(S,T) belongs to the range of the real induced G+ image map.

The general envelope proposition is then immediate: if a genuine
Kpt envelope covers both nodes of each represented pair, its induced
G+ map covers all their G+ vertices. This connects the already
formalized Algorithm 5.4 envelope range property with Definition
6.43 without assuming any new action or representation interface.

The separate next step must supply the actual AlgorithmRun's
envelope property for the precise finite seed set and verify
its approximation-domain and height hypotheses. The numerical
bound by itself does not do this.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

namespace GPlusRepresentingPair

/-- A representing pair with both actual admissible Kpt nodes in
the range of a genuine ShapeMap is itself the exact image of
another genuine strict representing pair. No inverse ShapeMap is
postulated; the preimages exist by range membership and their
order is reflected by the checked ShapeOrderReflection theorem. -/
theorem lifts_from_shapeMap_range
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (P : GPlusRepresentingPair family)
    (hLower : P.lower ∈ Set.range F)
    (hUpper : P.upper ∈ Set.range F) :
    ∃ Q : GPlusRepresentingPair family, Q.image F = P := by
  rcases hLower with ⟨s,hs⟩
  rcases hUpper with ⟨t,ht⟩
  have hImageLt : F s < F t := by
    simpa only [hs,ht] using P.lower_lt_upper
  have hLe : s ≤ t := F.reflects_le hImageLt.le
  have hNe : s ≠ t := by
    intro h
    subst t
    exact (lt_irrefl (F s)) hImageLt
  let Q : GPlusRepresentingPair family :=
    ⟨s,t,lt_of_le_of_ne hLe hNe⟩
  have hPair : Q.image F = P := by
    cases P with
    | mk lower upper hlt =>
      cases hs
      cases ht
      rfl
  exact ⟨Q,hPair⟩

/-- The represented G+ vertex, not just its two Kpt nodes, lies
in the range of the actual induced G+ action. -/
theorem vertex_mem_gPlus_image_range
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (P : GPlusRepresentingPair family)
    (hLower : P.lower ∈ Set.range F)
    (hUpper : P.upper ∈ Set.range F) :
    P.vertex ∈ Set.range (gPlusShapeImage F) := by
  obtain ⟨Q,hQ⟩ := P.lifts_from_shapeMap_range F hLower hUpper
  refine ⟨Q.vertex, ?_⟩
  calc
    gPlusShapeImage F Q.vertex = (Q.image F).vertex :=
      (Q.image_vertex_eq_canonicalShapeImage F).symm
    _ = P.vertex := congrArg GPlusRepresentingPair.vertex hQ

end GPlusRepresentingPair

/-- EXACT structural transfer of an envelope in the real Kpt
forest to coverage of any G+ vertex represented by a pair whose
two Kpt nodes were among the original envelope seeds.

This is a theorem with a genuine IsEnvelope premise, NOT a new
axiom that the numerical AlgorithmRun satisfies it. -/
theorem gPlus_vertex_mem_image_of_Kpt_envelope
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (X : Set (AdmissibleKptNode family))
    (hEnvelope : SuccessorTree.SMTree.Envelope.IsEnvelope F X)
    (P : GPlusRepresentingPair family)
    (hLower : P.lower ∈ X)
    (hUpper : P.upper ∈ X) :
    P.vertex ∈ Set.range (gPlusShapeImage F) :=
  P.vertex_mem_gPlus_image_range F
    (hEnvelope hLower) (hEnvelope hUpper)

/-- A whole finite set of represented vertices is covered, provided
its genuine representing-pair endpoints are all in the Kpt envelope. -/
theorem gPlus_vertices_covered_by_Kpt_envelope
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (X : Set (AdmissibleKptNode family))
    (hEnvelope : SuccessorTree.SMTree.Envelope.IsEnvelope F X)
    (P : Finset (GPlusRepresentingPair family))
    (hEndpoints : ∀ Q, Q ∈ P → Q.lower ∈ X ∧ Q.upper ∈ X) :
    ∀ Q, Q ∈ P → Q.vertex ∈ Set.range (gPlusShapeImage F) := by
  intro Q hQ
  exact gPlus_vertex_mem_image_of_Kpt_envelope
    F X hEnvelope Q (hEndpoints Q hQ).1 (hEndpoints Q hQ).2

end SuccessorTree.V10

import SuccessorTree.V10.GPlusBoundedPalette
import SuccessorTree.V10.GPlusEnvelopePairLift
import SuccessorTree.V10.KptRamseyApplications
import SuccessorTree.EnvelopeHeight
import Mathlib.Tactic

/-!
# Theorem 6.26: the real finite source palette of a Kpt envelope

The complete Algorithm 5.4 invariant (under the explicit Section 5 E1
one-level pullback hypothesis) produces a finite source prefix of
height m=R.selectedLevels.card covering every Kpt seed of X.

If two endpoints of a genuine G+ representing pair lie in X, they
have source preimages inside this prefix. ShapeMap order reflection
makes the preimages a genuine strict Kpt pair. The source pair's
upper level is <m, so its G+ vertex belongs to the ACTUAL finite
bounded-pair representation palette, not merely to a set of
numerically short finite G+ codes.

This argument extends pointwise to ANY q-tuple of G+ seed vertices:
one bounded finite-palette tuple maps exactly to the original tuple.
It is the missing geometric finite-palette bridge used before
pulling back the final finite-colour Ramsey theorem.

The result retains the explicit Section 5 E1 property and exact
initial-height bound; it does not silently assert E1 for the
normalized Kpt monoid. The separate coloured embedding transfer
of Theorem 6.26 still needs its precise finite-approximation domain.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- Any genuine Kpt prefix envelope with length m lifts both
endpoints of a represented G+ vertex to a REAL source pair with
upper source level <m. -/
theorem boundedGPlusPair_lift_of_prefixEnvelope
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (m : Nat)
    (X : Set (AdmissibleKptNode family))
    (hPrefix : SuccessorTree.SMTree.Envelope.IsPrefixEnvelope F m X)
    (P : GPlusRepresentingPair family)
    (hLower : P.lower ∈ X) (hUpper : P.upper ∈ X) :
    ∃ Q : BoundedGPlusRepresentingPair family m,
      (Q.val.image F).vertex = P.vertex := by
  obtain ⟨s,hsBound,hs⟩ := hPrefix hLower
  obtain ⟨t,htBound,ht⟩ := hPrefix hUpper
  have hFlt : F s < F t := by
    simpa only [hs,ht] using P.lower_lt_upper
  have hst : s < t := by
    have hstLe : s ≤ t := F.reflects_le hFlt.le
    exact lt_of_le_of_ne hstLe (by
      intro heq
      subst t
      exact (lt_irrefl (F s)) hFlt)
  let Q : GPlusRepresentingPair family := ⟨s,t,hst⟩
  have hEq : Q.image F = P := by
    rcases P with ⟨pLower,pUpper,hP⟩
    cases hs
    cases ht
    rfl
  refine ⟨⟨Q,by exact Nat.le_of_lt htBound⟩, ?_⟩
  exact congrArg GPlusRepresentingPair.vertex hEq

/-- The ACTUAL Algorithm 5.4 output has a genuine bounded source
representative for each of its initial Kpt seed pairs, where the
bound is the actual number of selected levels, not an abstract m. -/
theorem numericKptAlgorithmRun_bounded_GPlus_pair
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family)) (ell : Nat)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X ell)
    (hE1 : SuccessorTree.SMTree.Envelope.OneLevelPullback
      (normalizedKptSMTree family))
    (hBound : X ⊆ SuccessorTree.SMTree.Envelope.levelLe
      (T := AdmissibleKptNode family) ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell)
    (P : GPlusRepresentingPair family)
    (hLower : P.lower ∈ X) (hUpper : P.upper ∈ X) :
    ∃ Q : BoundedGPlusRepresentingPair family R.selectedLevels.card,
      (Q.val.image (R.F 0).map).vertex = P.vertex := by
  obtain ⟨m, hPrefix, hCard, _hMin⟩ :=
    R.minimal_output_height hE1 hBound hTop
  obtain ⟨Q,hQ⟩ :=
    boundedGPlusPair_lift_of_prefixEnvelope family
      (R.F 0).map m X hPrefix P hLower hUpper
  have hQBound : LevelTree.lev Q.val.upper ≤ R.selectedLevels.card := by
    rw [hCard]
    exact Q.property
  exact ⟨⟨Q.val,hQBound⟩,hQ⟩

/-- The source G+ vertex of that pair lies in the LITERAL finite
bounded-representation palette. The actual total ShapeMap sends it
to the desired target seed vertex. -/
theorem numericKptAlgorithmRun_GPlus_seed_in_finite_palette
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family)) (ell : Nat)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X ell)
    (hE1 : SuccessorTree.SMTree.Envelope.OneLevelPullback
      (normalizedKptSMTree family))
    (hBound : X ⊆ SuccessorTree.SMTree.Envelope.levelLe
      (T := AdmissibleKptNode family) ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell)
    (P : GPlusRepresentingPair family)
    (hLower : P.lower ∈ X) (hUpper : P.upper ∈ X) :
    ∃ A : FiniteGPlusVertex family,
      A ∈ boundedRepresentableGPlusVertices family R.selectedLevels.card ∧
      gPlusShapeImage (R.F 0).map A = P.vertex := by
  obtain ⟨Q,hQ⟩ := numericKptAlgorithmRun_bounded_GPlus_pair
    family X ell R hE1 hBound hTop P hLower hUpper
  refine ⟨Q.val.vertex, ?_, ?_⟩
  · change Q.val.vertex ∈ Set.range
      (fun W : BoundedGPlusRepresentingPair family R.selectedLevels.card =>
        W.val.vertex)
    exact ⟨Q,rfl⟩
  · calc
      gPlusShapeImage (R.F 0).map Q.val.vertex =
          (Q.val.image (R.F 0).map).vertex :=
        (Q.val.image_vertex_eq_canonicalShapeImage (R.F 0).map).symm
      _ = P.vertex := hQ

/-- A q-tuple of ACTUALLY represented G+ seed vertices is the
pointwise image of one tuple from the genuine FINITE bounded
representation palette. No injectivity or ordering assumption is
needed at this coarse palette stage. -/
theorem numericKptAlgorithmRun_GPlus_seed_tuple_from_finite_palette
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family)) (ell : Nat)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X ell)
    (hE1 : SuccessorTree.SMTree.Envelope.OneLevelPullback
      (normalizedKptSMTree family))
    (hBound : X ⊆ SuccessorTree.SMTree.Envelope.levelLe
      (T := AdmissibleKptNode family) ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell)
    (q : Nat)
    (targets : Fin q → FiniteGPlusVertex family)
    (hPairs : ∀ i : Fin q, ∃ P : GPlusRepresentingPair family,
      P.vertex = targets i ∧ P.lower ∈ X ∧ P.upper ∈ X) :
    ∃ sources : Fin q → FiniteGPlusVertex family,
      sources ∈ boundedGPlusTuplePalette family R.selectedLevels.card q ∧
      ∀ i : Fin q, gPlusShapeImage (R.F 0).map (sources i) =
        targets i := by
  classical
  have hChoose (i : Fin q) :
      ∃ Q : BoundedGPlusRepresentingPair family R.selectedLevels.card,
        gPlusShapeImage (R.F 0).map Q.val.vertex = targets i := by
    obtain ⟨P,hVertex,hLow,hUp⟩ := hPairs i
    obtain ⟨Q,hLift⟩ :=
      numericKptAlgorithmRun_bounded_GPlus_pair
        family X ell R hE1 hBound hTop P hLow hUp
    refine ⟨Q, ?_⟩
    calc
      gPlusShapeImage (R.F 0).map Q.val.vertex =
          (Q.val.image (R.F 0).map).vertex :=
        (Q.val.image_vertex_eq_canonicalShapeImage (R.F 0).map).symm
      _ = P.vertex := hLift
      _ = targets i := hVertex
  choose Q hQ using hChoose
  refine ⟨fun i => (Q i).val.vertex, ?_, ?_⟩
  · change (fun i => (Q i).val.vertex) ∈ Set.range
      (fun f : Fin q →
        BoundedGPlusRepresentingPair family R.selectedLevels.card =>
          fun i => (f i).val.vertex)
    exact ⟨Q,rfl⟩
  · exact hQ

end SuccessorTree.V10

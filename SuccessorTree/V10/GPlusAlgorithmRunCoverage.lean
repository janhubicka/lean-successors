import SuccessorTree.V10.GPlusEnvelopePairLift
import SuccessorTree.V10.KptRamseyApplications
import SuccessorTree.EnvelopeRunExistence
import Mathlib.Tactic

/-!
# V10 Definition 6.43: actual Algorithm 5.4 output covers represented G+

The previously checked envelope-range transfer shows that a genuine
Kpt ShapeMap F which covers BOTH endpoints of a strict representing
pair P also covers the actual G+ vertex v(P) through gPlusShapeImage F.

Here the map is no longer a postulated or arbitrarily supplied
envelope: it is the recorded output (R.F 0).map of an ACTUAL
Algorithm 5.4 run on the already verified normalized Kpt SM-tree.

The generic proof of Lemma 5.8 gives the precise stage invariant.
Under its existing E1 (one-level pullback) and initial seed-height
hypotheses, that invariant says R.F 0 covers the Kpt closure of
the actual seed set. Hence every pair with both endpoints in that
closure is covered, and so is every finite set of such represented
G+ vertices. The separate canonicalAlgorithmRun theorem removes
any existence assumption about Algorithm 5.4.

Importantly, this module does NOT claim that the concrete numerical
H+ envelope run has already been seeded with the desired endpoint
set, nor that its approximation has the necessary domain. Those
are the still-outstanding manuscript-specific links.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- The ACTUAL output of Algorithm 5.4, not an abstract assumed
envelope, covers a represented G+ vertex whose two Kpt endpoints
belong to the verified final stage closure. -/
theorem numericKptAlgorithmRun_covers_GPlus_pair
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (ell : Nat)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X ell)
    (hE1 : SuccessorTree.SMTree.Envelope.OneLevelPullback
      (normalizedKptSMTree family))
    (hBound : X ⊆
      SuccessorTree.SMTree.Envelope.levelLe
        (T := AdmissibleKptNode family) ell)
    (P : GPlusRepresentingPair family)
    (hLower : P.lower ∈ SuccessorTree.SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I 0) X)
    (hUpper : P.upper ∈ SuccessorTree.SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I 0) X) :
    P.vertex ∈ Set.range (gPlusShapeImage (R.F 0).map) := by
  have hInv := R.fullInvariant hE1 hBound 0 (Nat.zero_le ell)
  exact P.vertex_mem_gPlus_image_range (R.F 0).map
    (hInv.1.1 hLower) (hInv.1.1 hUpper)

/-- In particular, no closure membership proof is needed when
the actual original Algorithm 5.4 seed set already contains both
endpoints of the representing pair. -/
theorem numericKptAlgorithmRun_covers_GPlus_seed_pair
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (ell : Nat)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X ell)
    (hE1 : SuccessorTree.SMTree.Envelope.OneLevelPullback
      (normalizedKptSMTree family))
    (hBound : X ⊆
      SuccessorTree.SMTree.Envelope.levelLe
        (T := AdmissibleKptNode family) ell)
    (P : GPlusRepresentingPair family)
    (hLower : P.lower ∈ X) (hUpper : P.upper ∈ X) :
    P.vertex ∈ Set.range (gPlusShapeImage (R.F 0).map) := by
  apply numericKptAlgorithmRun_covers_GPlus_pair
    family X ell R hE1 hBound P
  · exact SuccessorTree.SMTree.Envelope.subset_closure
      (admissibleKptSTree family) (R.I 0) X hLower
  · exact SuccessorTree.SMTree.Envelope.subset_closure
      (admissibleKptSTree family) (R.I 0) X hUpper

/-- A finite family of genuinely represented G+ vertices is covered
by the actual algorithm output, provided each endpoint of each
representing pair occurs in the final Kpt closure. -/
theorem numericKptAlgorithmRun_covers_GPlus_pairs
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (ell : Nat)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X ell)
    (hE1 : SuccessorTree.SMTree.Envelope.OneLevelPullback
      (normalizedKptSMTree family))
    (hBound : X ⊆
      SuccessorTree.SMTree.Envelope.levelLe
        (T := AdmissibleKptNode family) ell)
    (P : Finset (GPlusRepresentingPair family))
    (hEndpoints : ∀ Q, Q ∈ P →
      Q.lower ∈ SuccessorTree.SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I 0) X ∧
      Q.upper ∈ SuccessorTree.SMTree.Envelope.closure
        (admissibleKptSTree family) (R.I 0) X) :
    ∀ Q, Q ∈ P →
      Q.vertex ∈ Set.range (gPlusShapeImage (R.F 0).map) := by
  intro Q hQ
  exact numericKptAlgorithmRun_covers_GPlus_pair
    family X ell R hE1 hBound Q
    (hEndpoints Q hQ).1 (hEndpoints Q hQ).2

/-- Algorithm 5.4 has an ACTUAL canonically constructed run, so no
separate existence premise for the envelope run is necessary.
Its output image covers every represented G+ seed pair under the
precise existing one-level pullback and initial-height hypotheses. -/
theorem canonicalNumericKptAlgorithmRun_covers_GPlus_seed_pair
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (ell : Nat)
    (hE1 : SuccessorTree.SMTree.Envelope.OneLevelPullback
      (normalizedKptSMTree family))
    (hBound : X ⊆
      SuccessorTree.SMTree.Envelope.levelLe
        (T := AdmissibleKptNode family) ell)
    (P : GPlusRepresentingPair family)
    (hLower : P.lower ∈ X) (hUpper : P.upper ∈ X) :
    let R := SuccessorTree.SMTree.Envelope.canonicalAlgorithmRun
      (normalizedKptSMTree family) X ell
    P.vertex ∈ Set.range (gPlusShapeImage (R.F 0).map) := by
  exact numericKptAlgorithmRun_covers_GPlus_seed_pair
    family X ell
    (SuccessorTree.SMTree.Envelope.canonicalAlgorithmRun
      (normalizedKptSMTree family) X ell)
    hE1 hBound P hLower hUpper

end SuccessorTree.V10

import SuccessorTree.V10.GPlusHTopSeedPairs
import SuccessorTree.V10.GPlusAlgorithmRunCoverage
import SuccessorTree.V10.HTopAlgorithmSeedHeight
import Mathlib.Tactic

/-!
# V10 Definition 6.43: the real numerical HTop Algorithm 5.4 covers G+

The literal HTop seed construction supplies both endpoints of the
genuine Kpt pair representing each selected top-generation G+ prefix.
The exact numerical root free level bounds every seed. Under the
existing Section 5 E1 condition, the checked full invariant for an
actual AlgorithmRun therefore yields coverage of each represented
G+ prefix by the real shape-map output.

The canonicalAlgorithmRun version constructs the run rather than
postulating its existence.

This is an exact geometric envelope-coverage theorem for the selected
numerical HTop G+ prefixes. It is conditional ONLY on the previously
isolated OneLevelPullback E1 property of the concrete SM-tree, the
actual HTop seed strictness/finite age hypotheses, and the original
algorithm inputs. It does not add E on an L-only age witness.

The remaining obligations for Theorem 6.26 are to establish the E1
property at the intended manuscript scope, bound the finite output
approximation by the checked sharp interesting-level budget, and
assemble the finite-colouring Ramsey transfer.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- Every selected numerical HTop G+ prefix is represented by a pair
of ACTUAL Algorithm 5.4 seeds and belongs to the image of its final
shape map. Neither the run nor the representing pair is abstractly
assumed to be an envelope: the conclusion uses the actual run R.F 0. -/
theorem numericHTopRun_covers_selected_GPlus_prefix
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat)
    (hAvoidH : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N))
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (hStrict : ∀ i : Nat, i ∈ blocks →
      hPosition k i k + 1 ≤ (finiteNumericH K k N).freeLevel c.val)
    (hE1 : SuccessorTree.SMTree.Envelope.OneLevelPullback
      (normalizedKptSMTree family))
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (numericHTopGenerationSeeds family K k N
        hAvoidH c blocks hWithin : Set (AdmissibleKptNode family))
      ((finiteNumericH K k N).freeLevel c.val))
    (i : Nat) (hi : i ∈ blocks) :
    ∃ (hSize : hPosition k i k + 1 ≤ (finiteNumericH K k N).size)
      (P : GPlusRepresentingPair family),
      P.vertex.val =
        FinitePartialCode.ofEnumerated
          ((finiteNumericH K k N).initialSegment
            (hPosition k i k + 1) hSize) ∧
      P.vertex ∈ Set.range (gPlusShapeImage (R.F 0).map) := by
  obtain ⟨hSize, P, hLower, hUpper, hCode⟩ :=
    numericHTopSeed_represents_GPlus_prefix
      family K k N hAvoidH c blocks hWithin hStrict i hi
  have hBound :
      (numericHTopGenerationSeeds family K k N
          hAvoidH c blocks hWithin :
        Set (AdmissibleKptNode family)) ⊆
        SuccessorTree.SMTree.Envelope.levelLe
          (T := AdmissibleKptNode family)
          ((finiteNumericH K k N).freeLevel c.val) :=
    numericHTopGenerationSeeds_bounded_by_root_freeLevel
      family K k N hAvoidH c blocks hWithin
  have hLowerSet :
      P.lower ∈ (numericHTopGenerationSeeds family K k N
        hAvoidH c blocks hWithin : Set (AdmissibleKptNode family)) :=
    Finset.mem_coe.mpr hLower
  have hUpperSet :
      P.upper ∈ (numericHTopGenerationSeeds family K k N
        hAvoidH c blocks hWithin : Set (AdmissibleKptNode family)) :=
    Finset.mem_coe.mpr hUpper
  have hRange :=
    numericKptAlgorithmRun_covers_GPlus_seed_pair
      family
      (numericHTopGenerationSeeds family K k N
        hAvoidH c blocks hWithin : Set (AdmissibleKptNode family))
      ((finiteNumericH K k N).freeLevel c.val)
      R hE1 hBound P hLowerSet hUpperSet
  exact ⟨hSize, P, hCode, hRange⟩

/-- The same coverage for the CANONICAL run of Algorithm 5.4.
The existence of a run is discharged by the already checked
canonicalAlgorithmRun, rather than being an additional premise. -/
theorem canonicalNumericHTopRun_covers_selected_GPlus_prefix
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat)
    (hAvoidH : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N))
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (hStrict : ∀ i : Nat, i ∈ blocks →
      hPosition k i k + 1 ≤ (finiteNumericH K k N).freeLevel c.val)
    (hE1 : SuccessorTree.SMTree.Envelope.OneLevelPullback
      (normalizedKptSMTree family))
    (i : Nat) (hi : i ∈ blocks) :
    let R := SuccessorTree.SMTree.Envelope.canonicalAlgorithmRun
      (normalizedKptSMTree family)
      (numericHTopGenerationSeeds family K k N
        hAvoidH c blocks hWithin : Set (AdmissibleKptNode family))
      ((finiteNumericH K k N).freeLevel c.val)
    ∃ (hSize : hPosition k i k + 1 ≤ (finiteNumericH K k N).size)
      (P : GPlusRepresentingPair family),
      P.vertex.val =
        FinitePartialCode.ofEnumerated
          ((finiteNumericH K k N).initialSegment
            (hPosition k i k + 1) hSize) ∧
      P.vertex ∈ Set.range (gPlusShapeImage (R.F 0).map) := by
  exact numericHTopRun_covers_selected_GPlus_prefix
    family K k N hAvoidH c blocks hWithin hStrict hE1
    (SuccessorTree.SMTree.Envelope.canonicalAlgorithmRun
      (normalizedKptSMTree family)
      (numericHTopGenerationSeeds family K k N
        hAvoidH c blocks hWithin : Set (AdmissibleKptNode family))
      ((finiteNumericH K k N).freeLevel c.val))
    i hi

end SuccessorTree.V10

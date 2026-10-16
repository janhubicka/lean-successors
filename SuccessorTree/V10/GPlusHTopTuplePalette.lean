import SuccessorTree.V10.GPlusHTopSeedPairs
import SuccessorTree.V10.HTopAlgorithmSeedHeight
import SuccessorTree.V10.GPlusActualSeedTupleColourBound
import Mathlib.Tactic

/-!
# Finite G+ palette for all genuine HTop prefix tuples

The already checked HTop seed theorem constructs, for each selected
top-generation block, a genuine strict Kpt representing pair whose
two endpoints belong to the same Algorithm 5.4 seed family. Its
represented G+ vertex equals the complete induced finite L+ code
of the corresponding numerical H+ initial segment.

Here those pointwise witnesses are assembled *simultaneously* for
every tuple of selected HTop prefix codes. The actual root of the
HTop seed family provides the top-height witness required by
Algorithm 5.4; its numerical free cut supplies the seed-height
bound. The verified concrete Section 5 E1 theorem is used through
the real-run finite-palette theorem, with no separate hypothesis.

This covers all tuples drawn from the specified top-generation
initial-prefix codes, including q=0. It is NOT yet the statement that
every induced copy of A in the universal G+ has this form, nor the
final uniform embedding K→H+→G+ of Theorem 6.26.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- All q-tuples of vertices whose complete finite L+ code is a
selected numerical HTop prefix. The witnesses include the actual
finite carrier bound; no arbitrary off-carrier E bits are admitted. -/
def numericHTopPrefixTuples
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat) (blocks : Finset Nat) (q : Nat) :
    Set (Fin q → FiniteGPlusVertex family) :=
  {t | ∀ i : Fin q,
    ∃ j : Nat, j ∈ blocks ∧
      ∃ hSize : hPosition k j k + 1 ≤ (finiteNumericH K k N).size,
        (t i).val =
          FinitePartialCode.ofEnumerated
            ((finiteNumericH K k N).initialSegment
              (hPosition k j k + 1) hSize)}

/-- All tuples of selected top-generation prefix codes are covered
by the *actual* finite AM approximation of the same HTop AlgorithmRun.
No per-tuple representing-pair or abstract E1 premise remains. -/
theorem numericHTopRun_prefixTuples_finiteApprox_cover
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat)
    (hAvoidH : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N))
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ j : Nat, j ∈ blocks →
      hPosition k j k ≤ (finiteNumericH K k N).freeLevel c.val)
    (hStrict : ∀ j : Nat, j ∈ blocks →
      hPosition k j k + 1 ≤ (finiteNumericH K k N).freeLevel c.val)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (numericHTopGenerationSeeds family K k N
        hAvoidH c blocks hWithin : Set (AdmissibleKptNode family))
      ((finiteNumericH K k N).freeLevel c.val))
    (q : Nat) :
    FiniteGPlusPaletteCovers family R.selectedLevels.card q
      (numericHTopPrefixTuples family K k N blocks q) := by
  classical
  let X : Set (AdmissibleKptNode family) :=
    numericHTopGenerationSeeds family K k N hAvoidH c blocks hWithin
  let ell : Nat := (finiteNumericH K k N).freeLevel c.val
  have hBound :
      X ⊆ SuccessorTree.SMTree.Envelope.levelLe
        (T := AdmissibleKptNode family) ell :=
    numericHTopGenerationSeeds_bounded_by_root_freeLevel
      family K k N hAvoidH c blocks hWithin
  have hTop : ∃ z ∈ X, LevelTree.lev z = ell := by
    let U : AdmissibleKptNode family :=
      (finiteNumericH K k N).kptOriginal family hAvoidH c
    refine ⟨U, ?_, ?_⟩
    · change U ∈ (numericHTopGenerationSeeds family K k N
        hAvoidH c blocks hWithin : Set (AdmissibleKptNode family))
      apply Finset.mem_coe.mpr
      unfold numericHTopGenerationSeeds
      exact Finset.mem_insert_self _ _
    · rfl
  have hPairs :
      ∀ t, t ∈ numericHTopPrefixTuples family K k N blocks q →
        ∀ i : Fin q,
          ∃ P : GPlusRepresentingPair family,
            P.vertex = t i ∧ P.lower ∈ X ∧ P.upper ∈ X := by
    intro t ht i
    obtain ⟨j, hj, hSize, hCode⟩ := ht i
    obtain ⟨hSize', P, hLower, hUpper, hPCode⟩ :=
      numericHTopSeed_represents_GPlus_prefix
        family K k N hAvoidH c blocks hWithin hStrict j hj
    have hSizeEq : hSize' = hSize := Subsingleton.elim _ _
    subst hSize'
    have hEqCode : P.vertex.val = (t i).val :=
      hPCode.trans hCode.symm
    refine ⟨P, Subtype.ext hEqCode, ?_, ?_⟩
    · exact Finset.mem_coe.mpr hLower
    · exact Finset.mem_coe.mpr hUpper
  exact numericKptAlgorithmRun_seed_tuples_finiteApprox_cover
    family X ell R hBound hTop q
    (numericHTopPrefixTuples family K k N blocks q) hPairs

/-- The actual numerical HTop run, not an arbitrary bounded palette
assumption, gives one finite-colour bound simultaneously for every
selected-prefix q-tuple. The palette has the verified selected-level
height of this very run. -/
theorem numericHTopRun_prefixTuples_finiteColour_bound
    {κ : Type*} [Fintype κ]
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat)
    (hAvoidH : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N))
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ j : Nat, j ∈ blocks →
      hPosition k j k ≤ (finiteNumericH K k N).freeLevel c.val)
    (hStrict : ∀ j : Nat, j ∈ blocks →
      hPosition k j k + 1 ≤ (finiteNumericH K k N).freeLevel c.val)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (numericHTopGenerationSeeds family K k N
        hAvoidH c blocks hWithin : Set (AdmissibleKptNode family))
      ((finiteNumericH K k N).freeLevel c.val))
    (q : Nat)
    (χ : (Fin q → FiniteGPlusVertex family) → κ) :
    ∃ (W : SuccessorTree.SMTree.ShapeSubspace
          (normalizedKptSMTree family) 0)
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family R.selectedLevels.card q) ∧
      ∀ t, t ∈ numericHTopPrefixTuples family K k N blocks q →
        χ (fun i : Fin q => gPlusShapeImage W.1.map (t i)) ∈ colours := by
  exact normalizedKpt_GPlus_finite_colour_bound_of_cover
    family R.selectedLevels.card q
    (numericHTopPrefixTuples family K k N blocks q) χ
    (numericHTopRun_prefixTuples_finiteApprox_cover
      family K k N hAvoidH c blocks hWithin hStrict R q)

end SuccessorTree.V10

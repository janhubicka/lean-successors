import SuccessorTree.V10.GPlusHTopUniformPalette
import SuccessorTree.V10.HTopRootStrictPrefix
import SuccessorTree.EnvelopeRunExistence

/-!
# Explicit top-root H+ construction and a uniform finite G+ colour bound

A finite family of top-generation block coordinates i<j has one
literal numerical H+ top root at coordinate hPosition k j k.
The actual E free cut of that root contains the first coordinate
*after* each selected block prefix, so these prefixes have real Kpt
representing pairs with both endpoints in one seed family.

Combining the checked sharp numeric H+ envelope bound with the
finite source G+ palette then gives a uniform colour bound for every
tuple of the selected top prefixes. No arbitrary root c, free-cut
slack, admissibility-of-H witness or AlgorithmRun is assumed by the
caller: all are constructed from K, k, j and the finite block set.

This is an integration step, not the unqualified Theorem 6.26:
one still must embed the original ordered K into the appropriate
universal G+ and identify *all* induced A-copies, not only tuples of
initial HTop prefix codes.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- For any prescribed FINITE set of earlier numerical top blocks,
construct the genuine next top root and canonical Algorithm 5.4 run.
Their selected-prefix tuples admit the explicit uniform numerical
bound B=2(blocks.card+1+M)+R(M)+1 with no E1 hypothesis. -/
theorem numericHTop_priorBlocks_uniform_tuple_colour_bound
    {κ : Type*} [Fintype κ]
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k j : Nat) (hk : 0 < k) (hj : 0 < j)
    (blocks : Finset Nat)
    (hEarlier : ∀ i : Nat, i ∈ blocks → i < j)
    (hFamilyBound : ∀ bad, bad ∈ family →
      bad.patternCard ≤ k+1)
    (q : Nat)
    (χ : (Fin q → FiniteGPlusVertex family) → κ) :
    let N := hPosition k j k + 1
    let M := descendingCumulativeBudget
      (ageSignatureCapacity
        (fun i : Fin family.length => (family.get i).patternCard))
      blocks.card (k-1)
    let B := 2*(blocks.card+1+M) +
      ageSignatureCapacity
        (fun i : Fin family.length => (family.get i).patternCard) M + 1
    ∃ (W : SuccessorTree.SMTree.ShapeSubspace
          (normalizedKptSMTree family) 0)
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family B q) ∧
      ∀ t, t ∈ numericHTopPrefixTuples family K k N blocks q →
        χ (fun i : Fin q => gPlusShapeImage W.1.map (t i)) ∈ colours := by
  classical
  let N : Nat := hPosition k j k + 1
  obtain ⟨c, _hc, hStrict⟩ :=
    finiteNumericH_top_root_for_earlier_blocks_strict
      K k j hk hj blocks hEarlier
  have hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤
        (finiteNumericH K k N).freeLevel c.val := by
    intro i hi
    have hs : hPosition k i k + 1 ≤
        (finiteNumericH K k N).freeLevel c.val := by
      simpa only [N] using (hStrict i hi)
    omega
  let hAvoidH : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N) :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  let X : Set (AdmissibleKptNode family) :=
    numericHTopGenerationSeeds family K k N
      hAvoidH c blocks hWithin
  let H := normalizedKptSMTree family
  let R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      H X ((finiteNumericH K k N).freeLevel c.val) :=
    SuccessorTree.SMTree.Envelope.canonicalAlgorithmRun
      H X ((finiteNumericH K k N).freeLevel c.val)
  exact numericH_actualRun_topPrefix_tuples_uniform_colour_bound
    family K hCarrier hAvoidK k N hk
    c blocks hWithin hStrict R hFamilyBound q χ

end SuccessorTree.V10

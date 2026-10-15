import SuccessorTree.V10.HBackwardNumericalInduction
import SuccessorTree.V10.HActualGenerationEventBound
import SuccessorTree.V10.HHigherPoolCumulativeBound
import Mathlib.Tactic

/-!
# V10 Proposition 6.44: discharge the backward recursion for the ACTUAL run

The numerical induction in HBackwardNumericalInduction was stated
with exact top and lower-level cardinal hypotheses. Here they
are obtained from the already checked concrete finite H and
Algorithm 5.4, without introducing an abstract family of
interesting levels or assuming an I3 signature.

At top generation k the chosen q seed prefixes account for all
selected real levels, hence s_k<=q. At each 0<r<k, the actual
I1/I2/I3 event partition gives

  s_r <= H_r + R(H_r),

and the literal higher-original address argument gives

  H_r <= 1+sum_{r<m<=k}s_m.

Monotonicity of the finite-family signature polynomial supplies
the exact lower-generation hypothesis. Consequently

  1 + sum_{k-j<=m<=k}s_m
    <= descendingCumulativeBudget R q j     (j<k),

where the single initial root is counted only once.
This is the manuscript's full induction over real generations,
up to the final substitution of its bound in the global closure
count (and the conventional empty-A case).
-/

namespace SuccessorTree.V10

/-- The exact backward cumulative bound for ACTUAL selected
Algorithm 5.4 real-generation levels in finite numerical H. -/
theorem numericH_actualRun_descending_generation_bound
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat) (hk : 0 < k)
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (numericHTopGenerationSeeds family K k N
        (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
        c blocks hWithin)
      ((finiteNumericH K k N).freeLevel c.val))
    (hFamilyBound : ∀ bad, bad ∈ family →
      bad.patternCard ≤ k+1) :
    ∀ j : Nat, j < k →
      1 + ∑ m ∈ Finset.Icc (k-j) k,
        (numericHSelectedRealGenerationLevels
          family K k N c
          (numericHTopGenerationSeeds family K k N
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
            c blocks hWithin : Set (AdmissibleKptNode family))
          R m).card
      ≤ descendingCumulativeBudget
          (ageSignatureCapacity
            (fun i : Fin family.length => (family.get i).patternCard))
          blocks.card j := by
  classical
  let hAvoid :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  let X : Set (AdmissibleKptNode family) :=
    numericHTopGenerationSeeds family K k N hAvoid c blocks hWithin
  let sizes : Fin family.length → Nat :=
    fun i => (family.get i).patternCard
  let s : Nat → Nat := fun m =>
    (numericHSelectedRealGenerationLevels family K k N c X R m).card
  have hTop :
      s k ≤ blocks.card := by
    have hCount :=
      numericHTopSeeds_actualRun_top_generation_card_le_blocks
        family K hCarrier hAvoidK k N hk
        c blocks hWithin R hFamilyBound
    have hEq :
        numericHSelectedRealGenerationLevels family K k N c X R k =
          topSelectedRealPositions k
            ((finiteNumericH K k N).freeLevel c.val) (R.I 0) := by
      classical
      ext ell
      simp [numericHSelectedRealGenerationLevels,
        topSelectedRealPositions]
    simpa only [s, hEq] using hCount
  have hLower : ∀ r : Nat, 0 < r → r < k →
      let M := 1 + ∑ m ∈ Finset.Icc (r+1) k, s m
      s r ≤ M + ageSignatureCapacity sizes M := by
    intro r hr hrk
    let V : Finset (Fin N) :=
      hStageOriginals K k N ({c} : Finset (Fin N)) (R.I 0)
    let H : Finset (Fin N) := hGenerationHighOriginals k r V
    let M : Nat := 1 + ∑ m ∈ Finset.Icc (r+1) k, s m
    have hS :
        s r ≤ H.card + ageSignatureCapacity sizes H.card := by
      exact numericH_algorithmRun_generation_event_bound
        family K hCarrier hAvoidK k N hk
        c blocks hWithin r hr hrk R hFamilyBound
    have hH : H.card ≤ M := by
      exact numericHHighOriginals_card_le_higherSelectedLevels
        family K k N c X R r
    have hR :
        ageSignatureCapacity sizes H.card ≤
          ageSignatureCapacity sizes M :=
      ageSignatureCapacity_mono sizes hH
    calc
      s r ≤ H.card + ageSignatureCapacity sizes H.card := hS
      _ ≤ M + ageSignatureCapacity sizes M :=
        Nat.add_le_add hH hR
  exact descending_real_generation_signature_bound
    sizes blocks.card k hk s hTop hLower

end SuccessorTree.V10
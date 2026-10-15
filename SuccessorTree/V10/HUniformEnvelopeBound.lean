import SuccessorTree.V10.HActualRunDescendingBudget
import SuccessorTree.V10.HFinalPoolPositiveGeneration
import SuccessorTree.V10.HFinalEnvelopeBound
import Mathlib.Tactic

/-!
# Proposition 6.44: uniform sharp finite H envelope height

This is the intended end-to-end numerical conclusion of the
circulation proof in successor v10, with no abstract stage
signature or meet-count assumption.

The actual Algorithm 5.4 run has:
1. its selected positive real generations bounded by the exact
   descending cumulative budget;
2. its fixed final original pool V consisting of the one root
   c plus selected genuine positive-generation real addresses;
3. a sharp forest meet closure with <=2(q+1+|V|) levels;
4. the remaining positive I3 levels counted by R(|V|);
5. at most one level zero.

Combining (1) and (2) yields |V|<=M, with
  M=descendingCumulativeBudget R q (k-1).
Monotonicity of the signature capacity then proves

  |I| <= 2(q+1+M)+R(M)+1.

Every source and target age witness in the constituent proof
is the exact L-only witness required by the selected B3 test;
no auxiliary E relation is assumed on it.

The scope remains the normalized finite unary/directed-binary/
diagonal language. For empty A, the manuscript separately
defines a height-zero envelope; this nonempty seed construction
assumes k>0.
-/

namespace SuccessorTree.V10

/-- The literal finite H+ AlgorithmRun selected levels have
the exact uniform v10 Proposition 6.44 bound, in the current
normalized relational signature. -/
theorem numericH_actualRun_uniform_sharp_envelope_bound
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
    let M := descendingCumulativeBudget
      (ageSignatureCapacity
        (fun i : Fin family.length => (family.get i).patternCard))
      blocks.card (k-1)
    (numericHRunFinalSelectedLevels family K k N c
      (numericHTopGenerationSeeds family K k N
        (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
        c blocks hWithin : Set (AdmissibleKptNode family)) R).card
      ≤ 2*(blocks.card+1+M) +
        ageSignatureCapacity
          (fun i : Fin family.length => (family.get i).patternCard) M + 1 := by
  classical
  let sizes : Fin family.length → Nat :=
    fun i => (family.get i).patternCard
  let M : Nat :=
    descendingCumulativeBudget (ageSignatureCapacity sizes)
      blocks.card (k-1)
  let X : Set (AdmissibleKptNode family) :=
    numericHTopGenerationSeeds family K k N
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      c blocks hWithin
  let V : Finset (Fin N) :=
    hStageOriginals K k N ({c} : Finset (Fin N)) (R.I 0)
  have hSelectedBudget :
      1 + ∑ m ∈ Finset.Icc 1 k,
        (numericHSelectedRealGenerationLevels
          family K k N c X R m).card ≤ M := by
    have hRec := numericH_actualRun_descending_generation_bound
      family K hCarrier hAvoidK k N hk
      c blocks hWithin R hFamilyBound
      (k-1) (by omega)
    have hIndex : k-(k-1) = 1 := by omega
    simpa only [hIndex, M, sizes] using hRec
  have hPoolBound : V.card ≤ M := by
    have hV := numericH_stage_originals_card_le_root_plus_selected
      family K k N hk c X R
    exact hV.trans hSelectedBudget
  have hRaw :=
    numericHTopSeeds_finalRun_selected_card_le_sharp
      family K hCarrier hAvoidK k N c blocks hWithin R
  have hMono :
      ageSignatureCapacity sizes V.card ≤
        ageSignatureCapacity sizes M :=
    ageSignatureCapacity_mono sizes hPoolBound
  calc
    (numericHRunFinalSelectedLevels family K k N c X R).card
        ≤ 2*(blocks.card+1+V.card) +
          ageSignatureCapacity sizes V.card + 1 := hRaw
    _ ≤ 2*(blocks.card+1+M) +
          ageSignatureCapacity sizes M + 1 := by omega

end SuccessorTree.V10
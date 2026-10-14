import SuccessorTree.V10.I1I2RealEventCharge
import SuccessorTree.V10.HGenerationHighBudget
import SuccessorTree.EnvelopeRun
import Mathlib.Tactic

/-!
# V10 Proposition 6.44: the I1/I2 level budget in an actual run

For the literal top-generation seed family, every real positive
(I1)/(I2) event at generation g carries a NumericHMeetCharge to
one of two original addresses in the closure's CURRENT stage pool.

The actual AlgorithmRun identity says all selected parameter
levels in that stage also belong to the FINAL selected level set.
Consequently every current-stage original belongs to ONE fixed
finite final pool V. The checked first-neighbour charge associates
each generation-g event with the unique charge of a higher-
generation original in V.

The resulting bound |I1_g union I2_g| <=
  |hGenerationHighOriginals k g V|
is the exact linear M_g contribution in Proposition 6.44.
No independent witness map or injectivity hypothesis is added.
The sharp I3 and descending numerical bounds are separate.
-/

namespace SuccessorTree.V10

/-- An original retained at one stage belongs to the finite
stage pool for any larger selected parameter index set.
Addresses stay literal Fin N vertices, without deduplicating types. -/
theorem numericH_ambientStageOriginal_mem_final
    {db du dd : Nat}
    (K : AgeTestModel db du dd) (k N : Nat)
    (U : Finset (Fin N))
    {I J : Set Nat} (hIJ : I ⊆ J)
    (v : Fin N)
    (hv : v ∈ ambientStagePool (finiteNumericH K k N)
      (U : Set (Fin N)) I) :
    v ∈ hStageOriginals K k N U J := by
  classical
  have hv' :
      v ∈ U ∨
      (v.val ∈ I ∧ 0 < (finiteNumericH K k N).freeLevel v.val) := by
    change v ∈ (U : Set (Fin N)) ∨
      (v.val ∈ I ∧ 0 < (finiteNumericH K k N).freeLevel v.val)
      at hv
    rcases hv with hU | ⟨hi,hFree⟩
    · exact Or.inl (Finset.mem_coe.mp hU)
    · exact Or.inr ⟨hi,hFree⟩
  have hw' :
      v ∈ U ∨
      (v.val ∈ J ∧ 0 < (finiteNumericH K k N).freeLevel v.val) := by
    rcases hv' with hu | ⟨hi,hFree⟩
    · exact Or.inl hu
    · exact Or.inr ⟨hIJ hi,hFree⟩
  simpa only [hStageOriginals, Finset.mem_filter,
    Finset.mem_univ, true_and, Set.mem_ofPred_eq] using hw'

/-- The selected higher levels of a concrete run are all members
of the final selected level set, without needing E1. -/
theorem numericH_algorithmRun_stageLevels_subset_final
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family))
    (top ell : Nat) (hLt : ell < top)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X top) :
    R.I (ell+1) ⊆ R.I 0 := by
  intro j hj
  have hTail := R.I_eq_final_tail_of_run (ell+1) (by omega)
  rw [hTail] at hj
  exact hj.1

/-- Every actual positive real I1 or I2 event of the run is
recorded in the SAME finite charged-level set obtained from
the final pool V, not a freshly enumerated stage pool. -/
theorem numericH_algorithmRun_I1I2_levels_mem_finalCharge
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat) (hk : 0 < k)
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (top ell p g : Nat) (hLt : ell < top)
    (hg : 0 < g) (hgk : g < k)
    (hPosition : ell = hPosition k p g)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (numericHTopGenerationSeeds family K k N
        (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
        c blocks hWithin) top)
    (hEvent :
      (∃ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (ell+1))
          (numericHTopGenerationSeeds family K k N
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
            c blocks hWithin) ∧
        LevelTree.lev z = ell) ∨
      (∃ a : AdmissibleKptNode family,
        a ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (ell+1))
          (numericHTopGenerationSeeds family K k N
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
            c blocks hWithin) ∧
        ∃ b : AdmissibleKptNode family,
          b ∈ SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (ell+1))
            (numericHTopGenerationSeeds family K k N
              (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
              c blocks hWithin) ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = ell)) :
    ell ∈ hPoolChargeLevels K.binary k g
      (hStageOriginals K k N ({c} : Finset (Fin N)) (R.I 0)) := by
  classical
  let U : Finset (Fin N) := {c}
  let V : Finset (Fin N) := hStageOriginals K k N U (R.I 0)
  have hEvent' :
      (∃ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (ell+1))
          (numericHTopGenerationSeeds family K k N
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
            c blocks hWithin) ∧
        LevelTree.lev z = hPosition k p g) ∨
      (∃ a : AdmissibleKptNode family,
        a ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (ell+1))
          (numericHTopGenerationSeeds family K k N
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
            c blocks hWithin) ∧
        ∃ b : AdmissibleKptNode family,
          b ∈ SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (ell+1))
            (numericHTopGenerationSeeds family K k N
              (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
              c blocks hWithin) ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = hPosition k p g) := by
    rw [←hPosition]
    exact hEvent
  obtain ⟨v,w,hv,hw,hCharge⟩ :=
    numericHTopSeeds_real_I1I2_has_charge
      family K hCarrier hAvoidK k N hk c blocks hWithin
      (R.I (ell+1)) p g hg hgk hEvent'
  have hStageSubset : R.I (ell+1) ⊆ R.I 0 :=
    numericH_algorithmRun_stageLevels_subset_final
      family
      (numericHTopGenerationSeeds family K k N
        (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
        c blocks hWithin)
      top ell hLt R
  have hvV : v ∈ V :=
    numericH_ambientStageOriginal_mem_final
      K k N U hStageSubset v hv
  have hwV : w ∈ V :=
    numericH_ambientStageOriginal_mem_final
      K k N U hStageSubset w hw
  have hCharged : hPosition k p g ∈ hPoolChargeLevels K.binary k g V := by
    rcases numericHMeetCharge_higher_original
      K.binary k v.val w.val p g hCharge with hvc | hwc
    · exact hOriginalCharge_level_mem_budget
        K.binary k g V v hvV p hvc
    · exact hOriginalCharge_level_mem_budget
        K.binary k g V w hwV p hwc
  rw [hPosition]
  exact hCharged

/-- Exact linear contribution M_g for ACTUAL AlgorithmRun
selected I1/I2 events at one intermediate real generation.
The finite pool is the final stage pool, shared with the I3
signature bound. -/
theorem numericH_algorithmRun_I1I2_generation_card_le_high_pool
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat) (hk : 0 < k)
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (top g : Nat) (hg : 0 < g) (hgk : g < k)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (numericHTopGenerationSeeds family K k N
        (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
        c blocks hWithin) top)
    (levels : Finset Nat)
    (hLevels : ∀ ell, ell ∈ levels →
      ell < top ∧ ∃ p : Nat, ell = hPosition k p g)
    (hEvent : ∀ ell, ell ∈ levels →
      (∃ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (ell+1))
          (numericHTopGenerationSeeds family K k N
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
            c blocks hWithin) ∧
        LevelTree.lev z = ell) ∨
      (∃ a : AdmissibleKptNode family,
        a ∈ SMTree.Envelope.closure (admissibleKptSTree family)
          (R.I (ell+1))
          (numericHTopGenerationSeeds family K k N
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
            c blocks hWithin) ∧
        ∃ b : AdmissibleKptNode family,
          b ∈ SMTree.Envelope.closure (admissibleKptSTree family)
            (R.I (ell+1))
            (numericHTopGenerationSeeds family K k N
              (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
              c blocks hWithin) ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = ell)) :
    levels.card ≤ (hGenerationHighOriginals k g
      (hStageOriginals K k N ({c} : Finset (Fin N)) (R.I 0))).card := by
  classical
  let V := hStageOriginals K k N ({c} : Finset (Fin N)) (R.I 0)
  have hSub : levels ⊆ hPoolChargeLevels K.binary k g V := by
    intro ell hEll
    obtain ⟨hLt,p,hPos⟩ := hLevels ell hEll
    exact numericH_algorithmRun_I1I2_levels_mem_finalCharge
      family K hCarrier hAvoidK k N hk c blocks hWithin
      top ell p g hLt hg hgk hPos R (hEvent ell hEll)
  exact (Finset.card_le_card hSub).trans
    (hPoolChargeLevels_card_le_generationHigh K.binary k g V)

end SuccessorTree.V10

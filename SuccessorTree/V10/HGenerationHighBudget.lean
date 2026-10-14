import SuccessorTree.V10.HClosureCharge
import Mathlib.Tactic

/-!
# Proposition 6.44: a common higher-original budget for meets and I3

Corollary 6.50 charges every positive-generation nontrivial
closure meet to one member of the current stage's pool of
originals of STRICTLY HIGHER generation. The signature
argument for I3 likewise counts ONLY higher-generation names.

The chargeable set hHigherOriginals is generally smaller than
the set of all higher-generation originals; this module proves
that the meet budget is bounded by the latter's cardinality.
Thus BOTH geometric contributions can use the manuscript's
same number M_r of higher-generation original addresses.

The remaining global induction still needs to classify I1/I2
selected levels as charged meets (except initial/parameter
levels) and to instantiate actual I3 high-labelled signatures.
No theorem here assumes that unselected or lower-generation
origins are themselves higher-generation names.
-/

namespace SuccessorTree.V10

/-- The finite set of genuinely real original addresses of
generation STRICTLY above r, among a fixed finite pool V.
This set is independent of the chosen first-neighbour charge. -/
noncomputable def hGenerationHighOriginals
    {N : Nat} (k r : Nat) (V : Finset (Fin N)) :
    Finset (Fin N) := by
  classical
  exact V.filter (fun v =>
    ∃ i n : Nat, r < n ∧ n ≤ k ∧ v.val = hPosition k i n)

/-- A named original charged to a meet at generation r has a
real numerical coordinate of strictly greater generation. -/
theorem hOriginalCharge_mem_generationHigh
    {db N : Nat}
    (B : Nat → Nat → Fin db → Bool)
    (k r : Nat) (V : Finset (Fin N))
    (v : Fin N) (hv : v ∈ V)
    (p : Nat) (hCharge : HOriginalCharge B k r v.val p) :
    v ∈ hGenerationHighOriginals k r V := by
  classical
  obtain ⟨i,n,hn,hPositionV,hr,_⟩ := hCharge
  simp only [hGenerationHighOriginals, Finset.mem_filter]
  exact ⟨hv,⟨i,n,hr,hn,hPositionV⟩⟩

theorem hHigherOriginals_subset_generationHigh
    {db N : Nat}
    (B : Nat → Nat → Fin db → Bool)
    (k r : Nat) (V : Finset (Fin N)) :
    hHigherOriginals B k r V ⊆ hGenerationHighOriginals k r V := by
  intro v hv
  have hMem : v ∈ V ∧ ∃ p, HOriginalCharge B k r v.val p := by
    simpa only [hHigherOriginals, Finset.mem_filter] using hv
  obtain ⟨hV,p,hP⟩ := hMem
  exact hOriginalCharge_mem_generationHigh B k r V v hV p hP

/-- All first-disagreement meet levels charged to V at
generation r number no more than the HIGHER-generation
names of V; in particular, the chargeability filter need
not appear in the final envelope recurrence. -/
theorem hPoolChargeLevels_card_le_generationHigh
    {db N : Nat}
    (B : Nat → Nat → Fin db → Bool)
    (k r : Nat) (V : Finset (Fin N)) :
    (hPoolChargeLevels B k r V).card ≤
      (hGenerationHighOriginals k r V).card := by
  exact (hPoolChargeLevels_card_le B k r V).trans
    (Finset.card_le_card (hHigherOriginals_subset_generationHigh B k r V))

/-- Enlarging a finite original-name pool never removes a
higher-generation original. -/
theorem hGenerationHighOriginals_mono
    {N : Nat} (k r : Nat)
    {V W : Finset (Fin N)} (hVW : V ⊆ W) :
    hGenerationHighOriginals k r V ⊆
      hGenerationHighOriginals k r W := by
  classical
  intro v hv
  simp only [hGenerationHighOriginals, Finset.mem_filter] at hv ⊢
  exact ⟨hVW hv.1,hv.2⟩

/-- The actual finite stage pool grows monotonically with its
selected level set, keeping the initial seed names U fixed.
This will allow all generation-r stages to share the final
AlgorithmRun higher-name universe. -/
theorem hStageOriginals_mono
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N : Nat) (U : Finset (Fin N))
    {I J : Set Nat} (hIJ : I ⊆ J) :
    hStageOriginals K k N U I ⊆ hStageOriginals K k N U J := by
  classical
  intro v hv
  have hv' :
      v ∈ U ∨ (v.val ∈ I ∧
        0 < (finiteNumericH K k N).freeLevel v.val) := by
    simpa only [hStageOriginals, Finset.mem_filter,
      Finset.mem_univ, true_and, Set.mem_setOf_eq] using hv
  have hw' :
      v ∈ U ∨ (v.val ∈ J ∧
        0 < (finiteNumericH K k N).freeLevel v.val) := by
    rcases hv' with hu | ⟨hi,hPos⟩
    · exact Or.inl hu
    · exact Or.inr ⟨hIJ hi,hPos⟩
  simpa only [hStageOriginals, Finset.mem_filter,
    Finset.mem_univ, true_and, Set.mem_setOf_eq] using hw'

/-- The existing actual closure meet budget now uses exactly
the same fixed higher-generation ORIGINAL NAME set as the
I3 signature budget, without any new geometric assumptions. -/
theorem forbiddenFreeH_closure_meet_budget_high
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (k N : Nat) (hk : 0 < k)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids K)
    (U : Finset (Fin N)) (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family (finiteNumericH K k N)
      (finiteNumericH_avoids_family family K hCarrier k N hAvoid)
      (U : Set (Fin N)))
    (r : Nat) (hr : 0 < r) (hrk : r ≤ k) :
    ∃ D : Finset Nat,
      D.card ≤
        (hGenerationHighOriginals k r (hStageOriginals K k N U I)).card ∧
      ∀ s t : AdmissibleKptNode family,
        s ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X →
        t ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X →
        (∃ c : AdmissibleKptNode family, c ≤ s ∧ c ≤ t) →
        LevelTree.meet s t ≠ s → LevelTree.meet s t ≠ t →
        ∀ p : Nat,
          LevelTree.lev (LevelTree.meet s t) = hPosition k p r →
          LevelTree.lev (LevelTree.meet s t) ∈ D := by
  obtain ⟨D,hD,hCovered⟩ :=
    forbiddenFreeH_closure_meet_budget
      family K hCarrier k N hk hAvoid U I X hX r hr hrk
  refine ⟨D,?_,hCovered⟩
  exact hD.trans
    (Finset.card_le_card
      (hHigherOriginals_subset_generationHigh
        K.binary k r (hStageOriginals K k N U I)))

end SuccessorTree.V10

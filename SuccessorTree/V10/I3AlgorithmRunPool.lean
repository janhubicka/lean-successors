import SuccessorTree.V10.I3AlgorithmInterestingBridge
import SuccessorTree.V10.HClosureCharge
import SuccessorTree.EnvelopeRun
import Mathlib.Tactic

/-!
# V10 Section 6: instantiate the I3 closure pool in Algorithm 5.4's run

The abstract AlgorithmRun is not merely a collection of
independently chosen interesting levels. At a tested level ell
its closure is
  Z_ell = closure S (R.I (ell+1)) X,
and R.I (ell+1) consists exactly of the finally selected levels
strictly above ell.

For the actual numerical H model, ConcreteOriginalPool proves
every Z_ell consists of prefixes of the finite original pool
  V = U union {i in R.I 0 : freeLevel(i)>0}.
This file passes that concrete invariant into the checked
Algorithm-5.4 I3 crossing and signature theorem. It constructs
the finite original-name enumeration rather than assuming one
exists, so every genuine (I3) level in a fixed finite run is
bounded by R(|V|).

The next global induction must bound the HIGHER-generation part
of V (not all of V) via Lemma 6.53 and the numerical recurrence.
-/

namespace SuccessorTree.V10

/-- Every represented closure node at an intermediate run stage
has an original among the FINITE final stage pool, as opposed
to a fresh original name selected independently at each level.
This uses only the actual Kpt parameter closure, run-tail
identity and monotonicity of the selected pool. -/
theorem numericH_algorithmRun_closure_original_in_final_pool
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family (finiteNumericH K k N)
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      (U : Set (Fin N)))
    (top ell : Nat) (hEll : ell < top)
    (R : SMTree.Envelope.AlgorithmRun (normalizedKptSMTree family) X top) :
    ∀ z, z ∈ SMTree.Envelope.closure
       (admissibleKptSTree family) (R.I (ell+1)) X →
      ∃ v : Fin N,
        v ∈ hStageOriginals K k N U (R.I 0) ∧
        z ≤ (finiteNumericH K k N).kptOriginal family
          (finiteNumericH_avoids_family family K hCarrier k N hAvoidK) v := by
  classical
  intro z hz
  let A := finiteNumericH K k N
  have hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  have hPool := admissibleKpt_stage_closure_subset_pool
    family A hAvoidA (U : Set (Fin N))
    (R.I (ell+1)) X hX hz
  obtain ⟨o,⟨v,hv,rfl⟩,hPrefix⟩ := hPool
  have hV : v ∈ hStageOriginals K k N U (R.I 0) := by
    simp only [hStageOriginals, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq]
    rcases hv with hu | ⟨hi,hFree⟩
    · exact Or.inl hu
    · right
      have hTail := R.I_eq_final_tail_of_run (ell+1) (by omega)
      rw [hTail] at hi
      exact ⟨hi.1,hFree⟩
  exact ⟨v,hV,hPrefix⟩

/-- The actual finite run's positive I3 levels have the exact
signature bound by the final maintained original pool V. No
independent global pool-representation premise remains.

Every selected level is interesting by the ALGORITHM itself.
The separately specified I3 classification consists only
of the absence of I1/I2 at the tested cut. -/
theorem numericH_algorithmRun_I3_card_le_finalPoolCapacity
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat)
    (U : Finset (Fin N))
    (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family (finiteNumericH K k N)
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      (U : Set (Fin N)))
    (top : Nat)
    (R : SMTree.Envelope.AlgorithmRun (normalizedKptSMTree family) X top)
    (hTop : ∃ x ∈ X, LevelTree.lev x = top)
    (levels : Finset Nat)
    (hLevels : ∀ ell, ell ∈ levels →
      0 < ell ∧ ell < top ∧ ell < N ∧ ell ∈ R.I 0)
    (hNoI1 : ∀ ell, ell ∈ levels →
      ¬ ∃ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (ell+1)) X ∧
        LevelTree.lev z = ell)
    (hNoI2 : ∀ ell, ell ∈ levels →
      ¬ ∃ a : AdmissibleKptNode family,
        a ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) (R.I (ell+1)) X ∧
        ∃ b : AdmissibleKptNode family,
          b ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) (R.I (ell+1)) X ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = ell) :
    levels.card ≤
      ageSignatureCapacity
        (fun i : Fin family.length => (family.get i).patternCard)
        (hStageOriginals K k N U (R.I 0)).card := by
  classical
  let A := finiteNumericH K k N
  let V := hStageOriginals K k N U (R.I 0)
  let original : Fin V.card → Fin N :=
    fun j => (V.equivFin.symm j).1
  have hSurj : ∀ v : Fin N, v ∈ V →
      ∃ j : Fin V.card, original j = v := by
    intro v hv
    refine ⟨V.equivFin ⟨v,hv⟩,?_⟩
    simp [original]
  let Z : Nat → Set (AdmissibleKptNode family) :=
    fun ell => SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I (ell+1)) X
  have hPool : ∀ ell, ell ∈ levels → ∀ z, z ∈ Z ell →
      ∃ v : Fin V.card, z ≤ A.kptOriginal family
        (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
        (original v) := by
    intro ell hMem z hz
    have hLt : ell < top := (hLevels ell hMem).2.1
    obtain ⟨v,hv,hzv⟩ :=
      numericH_algorithmRun_closure_original_in_final_pool
        family K hCarrier hAvoidK k N U X hX top ell hLt R z hz
    obtain ⟨j,hj⟩ := hSurj v hv
    refine ⟨j,?_⟩
    simpa [A, ←hj] using hzv
  have hInteresting : ∀ ell, ell ∈ levels →
      SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family) (Z ell) ell := by
    intro ell hMem
    have hLt : ell < top := (hLevels ell hMem).2.1
    have hSelected : ell ∈ R.I 0 := (hLevels ell hMem).2.2.2
    have hI :=
      R.finalLevel_interesting_of_run hTop hSelected
    have hNext := R.I_succ_eq_higher_final_of_run ell hLt
    simpa only [Z,hNext] using hI
  apply algorithmI3Levels_card_le_signature_capacity
    family A
    (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
    original Z levels
  · intro ell hMem
    obtain ⟨hPos,_hTop,hCut,_hI⟩ := hLevels ell hMem
    exact ⟨hPos,hCut⟩
  · exact hPool
  · exact hNoI1
  · exact hNoI2
  · exact hInteresting

end SuccessorTree.V10

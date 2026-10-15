import SuccessorTree.V10.HTopI1I2Seeds
import SuccessorTree.V10.I3AlgorithmRunSharp
import SuccessorTree.EnvelopeRun
import Mathlib.Tactic

/-!
# V10 Proposition 6.44: the actual top-generation base a_k = q+1

For the literal seed family Y consisting of one root O+ and its
top-generation prefixes, every actual Algorithm 5.4 level of real
generation k is already the level of one of the prescribed prefixes.

The proof uses the ACTUAL run: every selected level is interesting
for the closure of the previously selected higher levels. An I1/I2
event at a real top coordinate is an initial seed level by the
checked closure normal form and no-strict-top-meet theorem.
If neither I1 nor I2 occurs, the actual closure-selected function
has a failed corrected B3 test. The checked finite L-only
relocation theorem forbids such failure at a top-generation
coordinate. No abstract no-I3 or top-generation hypothesis is
added.

Consequently there are at most q selected real top-generation
levels for q prescribed prefix positions. The additional root
original accounts for the q+1 initial ORIGINAL budget in the
downward numerical induction. The latter cardinal translation
is kept explicit in the final Proposition 6.44 assembly.
-/

namespace SuccessorTree.V10

/-- Every literal seed at real top generation is the prefix for
one member of blocks, not the root (whose free cut is zero or
positive odd). -/
theorem numericHTopSeed_real_level_from_block
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat) (hk : 0 < k)
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N))
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (z : AdmissibleKptNode family)
    (hz : z ∈ numericHTopGenerationSeeds
      family K k N hAvoid c blocks hWithin)
    (p : Nat)
    (hLevel : LevelTree.lev z = hPosition k p k) :
    ∃ i : Nat, i ∈ blocks ∧
      LevelTree.lev z = hPosition k i k := by
  obtain hRoot | ⟨i,hPrefix⟩ :=
    numericHTopGenerationSeeds_cases
      family K k N hAvoid c blocks hWithin z hz
  · have hRootLevel :
        (finiteNumericH K k N).freeLevel c.val =
          hPosition k p k := by
      have hLev :
          LevelTree.lev
            ((finiteNumericH K k N).kptOriginal family hAvoid c) =
              (finiteNumericH K k N).freeLevel c.val := rfl
      rw [hRoot] at hLevel
      exact hLev.symm.trans hLevel
    by_cases hZero : (finiteNumericH K k N).freeLevel c.val = 0
    · rw [hZero] at hRootLevel
      unfold hPosition at hRootLevel
      omega
    · have hPos : 0 < (finiteNumericH K k N).freeLevel c.val := by omega
      exact False.elim
        ((finiteNumericH_positive_freeLevel_ne_realPosition
          K k N c.val p k c.isLt hPos) hRootLevel)
  · refine ⟨i.val,i.property,?_⟩
    rw [hPrefix]
    exact LevelTree.level_ancestor _ _ _

/-- The ACTUAL run's interestingness trichotomy, its source-faithful
one-gap theorem and the no-top-B3 theorem imply that a selected
real top-generation level has an I1/I2 event. -/
theorem numericHTopSeeds_actualRun_top_selected_is_seed_level
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
    (ell p : Nat)
    (hSelected : ell ∈ R.I 0)
    (hReal : ell = hPosition k p k)
    (hFamilyBound : ∀ bad, bad ∈ family →
      bad.patternCard ≤ k+1) :
    ∃ z : AdmissibleKptNode family,
      z ∈ numericHTopGenerationSeeds family K k N
        (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
        c blocks hWithin ∧
      LevelTree.lev z = ell := by
  classical
  let A : EnumeratedPartialStructure db du dd :=
    finiteNumericH K k N
  let hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  let X : Set (AdmissibleKptNode family) :=
    numericHTopGenerationSeeds family K k N hAvoidA c blocks hWithin
  let top : Nat := A.freeLevel c.val
  let U : Finset (Fin N) := {c}
  let V : Finset (Fin N) := hStageOriginals K k N U (R.I 0)
  let original : Fin V.card → Fin N := hOriginalName V
  let Z : Set (AdmissibleKptNode family) :=
    SMTree.Envelope.closure (admissibleKptSTree family)
      (R.I (ell+1)) X
  have hSeedPool : X ⊆ ambientPrefixPool family A hAvoidA
      (U : Set (Fin N)) := by
    simpa [X, A, U] using
      (numericHTopGenerationSeeds_subset_rootPool
        family K k N hAvoidA c blocks hWithin)
  have hTop : ∃ x ∈ X, LevelTree.lev x = top := by
    refine ⟨A.kptOriginal family hAvoidA c,?_,?_⟩
    · change (A.kptOriginal family hAvoidA c) ∈
        numericHTopGenerationSeeds family K k N hAvoidA
          c blocks hWithin
      unfold numericHTopGenerationSeeds
      exact Finset.mem_insert.mpr (Or.inl (by dsimp [A]))
    · rfl
  have hBound := R.I_mem_bounds 0 (Nat.zero_le top) ell hSelected
  have hTopNeReal : top ≠ hPosition k p k := by
    by_cases hZero : top = 0
    · intro h
      rw [hZero] at h
      unfold hPosition at h
      omega
    · have hPos : 0 < (finiteNumericH K k N).freeLevel c.val := by
        dsimp [top,A] at hZero ⊢
        omega
      exact finiteNumericH_positive_freeLevel_ne_realPosition
        K k N c.val p k c.isLt hPos
  have hLt : ell < top := by
    have hNe : ell ≠ top := by
      intro heq
      exact hTopNeReal (heq.symm.trans hReal)
    have hBoundTop : ell ≤ top := (hBound).2
    omega
  have hPos : 0 < ell := by
    rw [hReal]
    unfold hPosition
    omega
  have hN : ell < N := by
    have hc := A.freeLevel_le c.val
    have hcN := c.isLt
    change top ≤ c.val at hc
    omega
  have hInteresting :
      SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family) Z ell := by
    have hI := R.finalLevel_interesting_of_run hTop hSelected
    have hNext := R.I_succ_eq_higher_final_of_run ell hLt
    simpa only [Z,hNext] using hI
  let I1 : Prop := ∃ z : AdmissibleKptNode family,
    z ∈ Z ∧ LevelTree.lev z = ell
  let I2 : Prop := ∃ a : AdmissibleKptNode family, a ∈ Z ∧
    ∃ b : AdmissibleKptNode family, b ∈ Z ∧
      SMTree.Envelope.SameComponent a b ∧
      LevelTree.lev (LevelTree.meet a b) = ell
  by_cases hEvent : I1 ∨ I2
  · have hEventTop :
        (∃ z : AdmissibleKptNode family,
          z ∈ Z ∧ LevelTree.lev z = hPosition k p k) ∨
        (∃ a : AdmissibleKptNode family,
          a ∈ Z ∧ ∃ b : AdmissibleKptNode family,
            b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
            LevelTree.lev (LevelTree.meet a b) = hPosition k p k) := by
      simpa only [I1,I2,←hReal] using hEvent
    obtain ⟨z,hSeed,hLev⟩ :=
      numericHTopSeeds_real_top_I1I2_is_seed_level
        family K hCarrier hAvoidK k N hk c blocks hWithin
        (R.I (ell+1)) p hEventTop
    exact ⟨z,hSeed,by rw [hReal]; exact hLev⟩
  · have hNoI1 : ¬ I1 := fun h => hEvent (Or.inl h)
    have hNoI2 : ¬ I2 := fun h => hEvent (Or.inr h)
    have hFailure :=
      numericH_algorithmRun_I3_stage_failedB3
        family K hCarrier hAvoidK k N U X hSeedPool
        top R hTop ell hPos hLt hN hSelected hNoI1 hNoI2
    have hB3 :=
      numericH_top_generation_selectedB3_holds
        family K hCarrier hAvoidK k N ell p hk hN hReal
        original
        (closureSelectedOriginal family A hAvoidA original Z ell)
        hFamilyBound
    exact False.elim (hFailure hB3)

/-- Each selected real top-generation level of the ACTUAL run
is one of the prescribed top-generation prefix positions. -/
theorem numericHTopSeeds_actualRun_top_level_from_block
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
    (ell p : Nat)
    (hSelected : ell ∈ R.I 0)
    (hReal : ell = hPosition k p k)
    (hFamilyBound : ∀ bad, bad ∈ family →
      bad.patternCard ≤ k+1) :
    ∃ i : Nat, i ∈ blocks ∧ ell = hPosition k i k := by
  obtain ⟨z,hSeed,hLev⟩ :=
    numericHTopSeeds_actualRun_top_selected_is_seed_level
      family K hCarrier hAvoidK k N hk c blocks hWithin
      R ell p hSelected hReal hFamilyBound
  obtain ⟨i,hi,hZLevel⟩ :=
    numericHTopSeed_real_level_from_block
      family K k N hk
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      c blocks hWithin z hSeed p (by rw [hLev]; exact hReal)
  exact ⟨i,hi,hLev.symm.trans hZLevel⟩

/-- The finite top-generation selected levels of one actual run,
with the predicate's finite decidability fixed inside the definition. -/
noncomputable def topSelectedRealPositions
    (k top : Nat) (I : Set Nat) : Finset Nat := by
  classical
  exact (Finset.range (top+1)).filter
    (fun ell => ell ∈ I ∧ ∃ p : Nat, ell = hPosition k p k)

/-- The q top prefixes are the only real top-generation selected
levels. This is the top-level part of the base a_k=q+1; the
extra one accounts for the root original c in the pool V. -/
theorem numericHTopSeeds_actualRun_top_generation_card_le_blocks
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
    (topSelectedRealPositions k
      ((finiteNumericH K k N).freeLevel c.val)
      (R.I 0)).card ≤ blocks.card := by
  classical
  let top : Nat := (finiteNumericH K k N).freeLevel c.val
  let L : Finset Nat :=
    topSelectedRealPositions k top (R.I 0)
  have hSub : L ⊆ blocks.image (fun i => hPosition k i k) := by
    intro ell hEll
    have hMem : ell ∈ R.I 0 ∧
        ∃ p : Nat, ell = hPosition k p k := by
      change ell ∈ (Finset.range (top+1)).filter
        (fun x => x ∈ R.I 0 ∧ ∃ p : Nat, x = hPosition k p k) at hEll
      exact (Finset.mem_filter.mp hEll).2
    obtain ⟨p,hReal⟩ := hMem.2
    obtain ⟨i,hi,hEq⟩ :=
      numericHTopSeeds_actualRun_top_level_from_block
        family K hCarrier hAvoidK k N hk c blocks hWithin
        R ell p hMem.1 hReal hFamilyBound
    exact Finset.mem_image.mpr ⟨i,hi,hEq.symm⟩
  calc
    L.card ≤ (blocks.image (fun i => hPosition k i k)).card :=
      Finset.card_le_card hSub
    _ ≤ blocks.card := Finset.card_image_le

end SuccessorTree.V10
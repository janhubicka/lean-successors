import SuccessorTree.V10.HTopAlgorithmRunBase
import SuccessorTree.V10.I1I2AlgorithmRunBudget
import SuccessorTree.V10.I3AlgorithmRunSharp
import Mathlib.Tactic

/-!
# V10 Proposition 6.44: actual generation-by-generation event partition

At every positive real H-generation r<k, consider the ACTUAL
selected Algorithm 5.4 levels, not an assumed list of failures.
A level has an I1/I2 event in the closure of the selected higher
levels, or it has neither event. The two finite subfamilies cover
all selected generation-r levels.

The first subfamily is bounded by the common actual higher-original
charge budget H_r. For the second, interestingness is guaranteed
by the AlgorithmRun and (I1)/(I2) are both absent, so the checked
actual-run I3 lemma yields the sharp R(H_r) signature bound.
We therefore obtain the geometric numerical input

    |selected generation-r levels| <= |H_r| + R(|H_r|).

The remaining full Proposition 6.44 induction must compare H_r
with the previously counted generations, supply the q+1 top base,
and complete the global forest meet-closure bound. This module
does not replace those steps with numerical assumptions.
-/

namespace SuccessorTree.V10

/-- An actual real H coordinate of positive generation below
the root's E-free level lies STRICTLY below that level: the
root's positive free cut is odd while every real position
is even. Such a coordinate is within the finite H carrier. -/
theorem numericH_real_below_root_freeLevel
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N : Nat) (c : Fin N)
    (ell p r : Nat) (hr : 0 < r)
    (hReal : ell = hPosition k p r)
    (hLe : ell ≤ (finiteNumericH K k N).freeLevel c.val) :
    0 < ell ∧
      ell < (finiteNumericH K k N).freeLevel c.val ∧
      ell < N := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let top : Nat := A.freeLevel c.val
  have hPos : 0 < ell := by
    rw [hReal]
    unfold hPosition
    omega
  have hTopNe : top ≠ hPosition k p r := by
    by_cases hZero : top = 0
    · intro heq
      rw [hZero] at heq
      unfold hPosition at heq
      omega
    · have hTopPos : 0 < A.freeLevel c.val := by
        dsimp [top] at hZero
        omega
      exact finiteNumericH_positive_freeLevel_ne_realPosition
        K k N c.val p r c.isLt hTopPos
  have hLt : ell < top := by
    have hNe : ell ≠ top := by
      intro heq
      exact hTopNe (heq.symm.trans hReal)
    change ell ≤ top at hLe
    omega
  have hTopLe : top ≤ c.val := A.freeLevel_le c.val
  have hN : ell < N := by
    have hcN := c.isLt
    omega
  exact ⟨hPos,hLt,hN⟩

/-- At generation r, the relevant finite set consists precisely
of selected real coordinates of that generation in the actual run. -/
noncomputable def numericHSelectedRealGenerationLevels
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat) (c : Fin N)
    (X : Set (AdmissibleKptNode family))
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X
      ((finiteNumericH K k N).freeLevel c.val))
    (r : Nat) : Finset Nat := by
  classical
  exact (Finset.range ((finiteNumericH K k N).freeLevel c.val + 1)).filter
    (fun ell => ell ∈ R.I 0 ∧
      ∃ p : Nat, ell = hPosition k p r)

/-- Every level in the finite selected real generation set
has the genuine current-stage bounds required by the I1/I2
and I3 theorems, without any independent bound assumption. -/
theorem numericHSelectedRealGenerationLevels_properties
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat) (c : Fin N)
    (X : Set (AdmissibleKptNode family))
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X
      ((finiteNumericH K k N).freeLevel c.val))
    (r : Nat) (hr : 0 < r)
    (ell : Nat)
    (hMem : ell ∈ numericHSelectedRealGenerationLevels
      family K k N c X R r) :
    0 < ell ∧
    ell < (finiteNumericH K k N).freeLevel c.val ∧
    ell < N ∧ ell ∈ R.I 0 ∧
      ∃ p : Nat, ell = hPosition k p r := by
  classical
  have hP : ell ∈ R.I 0 ∧ ∃ p : Nat, ell = hPosition k p r := by
    exact (Finset.mem_filter.mp hMem).2
  obtain ⟨p,hReal⟩ := hP.2
  have hBound : ell ≤ (finiteNumericH K k N).freeLevel c.val := by
    exact (R.I_mem_bounds 0 (Nat.zero_le _) ell hP.1).2
  obtain ⟨hPos,hLt,hN⟩ :=
    numericH_real_below_root_freeLevel K k N c ell p r hr hReal hBound
  exact ⟨hPos,hLt,hN,hP.1,p,hReal⟩

/-- The actual-run event split has the exact geometric per-generation
bound M_r+R(M_r), where M_r is the NUMBER of higher-generation
originals of ONE FIXED final stage pool V. -/
theorem numericH_algorithmRun_generation_event_bound
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat) (hk : 0 < k)
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (r : Nat) (hr : 0 < r) (hrk : r < k)
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (numericHTopGenerationSeeds family K k N
        (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
        c blocks hWithin)
      ((finiteNumericH K k N).freeLevel c.val))
    (hFamilyBound : ∀ bad, bad ∈ family →
      bad.patternCard ≤ k+1) :
    (numericHSelectedRealGenerationLevels
        family K k N c
        (numericHTopGenerationSeeds family K k N
          (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
          c blocks hWithin : Set (AdmissibleKptNode family)) R r).card
      ≤
    (hGenerationHighOriginals k r
      (hStageOriginals K k N ({c} : Finset (Fin N)) (R.I 0))).card +
    ageSignatureCapacity
      (fun i : Fin family.length => (family.get i).patternCard)
      (hGenerationHighOriginals k r
        (hStageOriginals K k N ({c} : Finset (Fin N)) (R.I 0))).card := by
  classical
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  let X : Set (AdmissibleKptNode family) :=
    numericHTopGenerationSeeds family K k N hAvoidA c blocks hWithin
  let U : Finset (Fin N) := {c}
  let top : Nat := A.freeLevel c.val
  let V : Finset (Fin N) := hStageOriginals K k N U (R.I 0)
  let S : Finset Nat :=
    numericHSelectedRealGenerationLevels family K k N c X R r
  let Z : Nat → Set (AdmissibleKptNode family) :=
    fun ell => SMTree.Envelope.closure
      (admissibleKptSTree family) (R.I (ell+1)) X
  let Event : Nat → Prop := fun ell =>
    (∃ z : AdmissibleKptNode family,
      z ∈ Z ell ∧ LevelTree.lev z = ell) ∨
    (∃ a : AdmissibleKptNode family,
      a ∈ Z ell ∧
      ∃ b : AdmissibleKptNode family,
        b ∈ Z ell ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = ell)
  let E : Finset Nat := S.filter Event
  let T : Finset Nat := S.filter (fun ell => ¬ Event ell)
  have hX : X ⊆ ambientPrefixPool family A hAvoidA
      (U : Set (Fin N)) :=
    numericHTopGenerationSeeds_subset_rootPool
      family K k N hAvoidA c blocks hWithin
  have hTop : ∃ x ∈ X, LevelTree.lev x = top := by
    refine ⟨A.kptOriginal family hAvoidA c,?_,?_⟩
    · change A.kptOriginal family hAvoidA c ∈
        numericHTopGenerationSeeds family K k N hAvoidA
          c blocks hWithin
      unfold numericHTopGenerationSeeds
      simp
    · rfl
  have hProps : ∀ ell, ell ∈ S →
      0 < ell ∧ ell < top ∧ ell < N ∧
      ell ∈ R.I 0 ∧ ∃ p : Nat, ell = hPosition k p r := by
    intro ell hMem
    exact numericHSelectedRealGenerationLevels_properties
      family K k N c X R r hr ell hMem
  have hLinear :
      E.card ≤ (hGenerationHighOriginals k r V).card := by
    apply numericH_algorithmRun_I1I2_generation_card_le_high_pool
      family K hCarrier hAvoidK k N hk c blocks hWithin
      top r hr hrk R E
    · intro ell hMem
      obtain ⟨hS,_hEvent⟩ := Finset.mem_filter.mp hMem
      obtain ⟨_hPos,hLt,_hN,_hSel,p,hReal⟩ := hProps ell hS
      exact ⟨hLt,p,hReal⟩
    · intro ell hMem
      exact (Finset.mem_filter.mp hMem).2
  have hSharp :
      T.card ≤ ageSignatureCapacity
        (fun i : Fin family.length => (family.get i).patternCard)
        (hGenerationHighOriginals k r V).card := by
    apply numericH_algorithmRun_I3_generation_card_le_high_pool
      family K hCarrier hAvoidK k N r hrk U X hX top R hTop T
    · intro ell hMem
      obtain ⟨hS,_hNoEvent⟩ := Finset.mem_filter.mp hMem
      exact hProps ell hS
    · intro ell hMem hI1
      exact (Finset.mem_filter.mp hMem).2 (Or.inl hI1)
    · intro ell hMem hI2
      exact (Finset.mem_filter.mp hMem).2 (Or.inr hI2)
    · exact hFamilyBound
  have hCover : S ⊆ E ∪ T := by
    intro ell hMem
    by_cases hEvent : Event ell
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hMem,hEvent⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨hMem,hEvent⟩))
  calc
    S.card ≤ (E ∪ T).card := Finset.card_le_card hCover
    _ ≤ E.card + T.card := Finset.card_union_le E T
    _ ≤ (hGenerationHighOriginals k r V).card +
         ageSignatureCapacity
           (fun i : Fin family.length => (family.get i).patternCard)
           (hGenerationHighOriginals k r V).card :=
      Nat.add_le_add hLinear hSharp

end SuccessorTree.V10
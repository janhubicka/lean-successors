import SuccessorTree.V10.I3SelectedStagePool
import SuccessorTree.V10.I3ActualStageGeneration
import SuccessorTree.V10.I3CrossingAtoms
import Mathlib.Tactic

/-!
# Lemma 6.53: higher generation of the CHOSEN original labels

The manuscript requires gamma(f(j)) > gamma(ell) for the *actual
label* f(j) used in Observation 6.52's finite signature, not
merely for some real H vertex with an equal L-type.  The complete
crossing type and an edge from ell force the chosen original's
numeric H coordinate itself to have the higher generation.

This module strengthens the selected-source finite age failure
argument to preserve the selected names and prove their exact
numerical coordinates and generation.  It retains full induced
L-types and never equips arbitrary finite B3 age witnesses with E.
-/

namespace SuccessorTree.V10

/-- Given the checked lower generation n = r-1, every named upper
original in an actual irreducible I3 forbidden copy is ITSELF a
real numerical H vertex of strictly greater generation.

In particular the chosen original from a fixed Fin M signature
pool is not replaced by an unrelated equivalent type. -/
theorem numericI3_selected_named_originals_have_higher_generation
    {db du dd t M : Nat}
    (K : AgeTestModel db du dd)
    (k N ell r : Nat) (hr : 0 < r) (hrt : r < t)
    (hrk : r ≤ k)
    (W : AgeTestModel db du dd)
    (P : ForbiddenAtomicPattern t db du dd)
    (hIrred : P.Irreducible)
    (e : Fin t → Nat) (hCopy : W.Realizes P e)
    (hLast : e (⟨r-1, by omega⟩ : Fin t) = ell)
    (original : Fin M → Nat)
    (Selected : Fin M → Prop)
    (hUpper : ∀ b : Fin t, r ≤ b.val →
      ∃ v : Fin M, Selected v ∧ ell < original v ∧
        RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (ell+1) (original v))
    (hGeneration : ∃ i : Nat, ell = hPosition k i (r-1)) :
    ∀ b : Fin t, r ≤ b.val →
      ∃ v : Fin M, ∃ j m : Nat,
        Selected v ∧
        original v = hPosition k j m ∧
        r-1 < m ∧ m ≤ k ∧
        RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (ell+1) (original v) := by
  intro b hb
  obtain ⟨v,hSelected,hAfter,hType⟩ := hUpper b hb
  let last : Fin t := ⟨r-1,by omega⟩
  have hne : last ≠ b := by
    intro heq
    have hv := congrArg Fin.val heq
    dsimp [last] at hv
    omega
  have hLink : ∃ bit : Fin db,
      W.binary ell (e b) bit = true ∨
      W.binary (e b) ell bit = true := by
    obtain ⟨bit,hP⟩ := hIrred last b hne
    refine ⟨bit,?_⟩
    rcases hP with hP | hP
    · have hEq := hCopy.2.2.1 last b hne bit
      rw [hLast] at hEq
      exact Or.inl (hEq.trans hP)
    · have hEq := hCopy.2.2.1 b last hne.symm bit
      rw [hLast] at hEq
      exact Or.inr (hEq.trans hP)
  obtain ⟨i,j,q,m,hij,hq,hm,hGate,hEll,hOriginal⟩ :=
    i3_named_upper_link_numeric_generators
      K k N ell W (e b) (original v) hAfter hType hLink
  obtain ⟨i0,hTested⟩ := hGeneration
  have hNonTop : r-1 < k := by omega
  have hStrict : r-1 < m :=
    i3_named_upper_generation_strict_of_nonTop_tested
      K k N ell W (e b) (original v) hAfter hType hLink
      i0 j (r-1) m hTested hOriginal hNonTop hm
  exact ⟨v,j,m,hSelected,hOriginal,hStrict,hm,hType⟩

/-- For the actual selected (not merely cut-eligible) fixed original
pool, a failed B3 yields an induced forbidden copy whose chosen
upper ORIGINAL NAMES all have generation strictly above the tested
real vertex's generation r-1. -/
theorem finiteNumericH_failedSelectedStageB3_originals_higher
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N ell : Nat) (hEll : ell < N)
    (original : Fin M → Fin N)
    (Selected : Fin M → Prop)
    (hFamilyBound : ∀ bad, bad ∈ family →
      bad.patternCard ≤ k+1)
    (hFailure :
      ¬ (selectedStagePoolPrescribedData
        (finiteNumericH K k N) ell original Selected).CorrectedB3 family) :
    ∃ W : AgeTestModel db du dd,
      W.BoundedCarrier ∧
      SameInitialL W (finiteNumericHL K k N) ell ∧
      (∀ bad, bad ∈ family → bad.Avoids (W.withoutVertex ell)) ∧
      ∃ (t : Nat) (P : ForbiddenAtomicPattern t db du dd)
        (e : Fin t → Nat) (r : Nat)
        (hr : 0 < r) (hrt : r < t),
        P.Irreducible ∧
        W.Realizes P e ∧
        (∀ a : Fin t, a.val < r ↔ e a ≤ ell) ∧
        (∀ a : Fin t, r ≤ a.val ↔ ell < e a) ∧
        (∃ i : Nat,
          ell = hPosition k i (r-1) ∧
          ∀ b : Fin t, r ≤ b.val →
            ∃ v : Fin M, ∃ j m : Nat,
              Selected v ∧
              ell+1 ≤ (finiteNumericH K k N).freeLevel (original v).val ∧
              (original v).val = hPosition k j m ∧
              r-1 < m ∧ m ≤ k ∧
              RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
                RelationalPrefixType.ofAgeModel
                  (finiteNumericHL K k N) (ell+1) (original v).val) := by
  classical
  let A : EnumeratedPartialStructure db du dd :=
    finiteNumericH K k N
  have hEllA : ell < A.size := hEll
  obtain ⟨S0,hS0,W,hFinite,hSocle,hDelete,hUpper,bad,hMember,hBad⟩ :=
    selectedStagePool_failedCorrectedB3_has_selected_original_witness
      family A ell hEllA original Selected hFailure
  have hSocleH :
      SameInitialL W (finiteNumericHL K k N) ell := hSocle
  have hAvoidA : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N) :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  obtain ⟨t,P,e,r,hr,hrt,hrk,hIrred,hCopy,hDeleteP,hLast,hLow,hHigh⟩ :=
    normalizedForbidden_bounded_I3_proper_cut
      (finiteNumericHL K k N) W ell k bad
      (hFamilyBound bad hMember) hSocleH
      (hAvoidA bad hMember) (hDelete bad hMember) hBad
  have hNamed : ∀ b : Fin t, r ≤ b.val →
      ∃ v : Fin M,
        (Selected v ∧ ell+1 ≤ A.freeLevel (original v).val) ∧
        ell < (original v).val ∧
        RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (ell+1) (original v).val := by
    intro b hb
    have hAbove : ell < e b := (hHigh b).1 hb
    obtain ⟨v,hSel,hCut,hType⟩ :=
      hUpper (e b) (hCopy.2.1 b) hAbove
    have hAddress : A.freeLevel (original v).val ≤
        (original v).val :=
      A.freeLevel_le (original v).val
    have hAfter : ell < (original v).val := by omega
    exact ⟨v,⟨hSel,hCut⟩,hAfter,hType⟩
  have hUpperNamed : ∀ b : Fin t, r ≤ b.val →
      ∃ orig : Nat, ell < orig ∧
        RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (ell+1) orig := by
    intro b hb
    obtain ⟨v,_hSel,hAfter,hType⟩ := hNamed b hb
    exact ⟨(original v).val,hAfter,hType⟩
  obtain ⟨i,hGeneration,_hUpperCoords⟩ :=
    numericI3_actual_witness_generation_conclusions
      K k N ell r hr hrt hrk W hSocleH
      P hIrred e hCopy hDeleteP hLast hUpperNamed
  have hChosenHigh :=
    numericI3_selected_named_originals_have_higher_generation
      K k N ell r hr hrt hrk W P hIrred e hCopy hLast
      (fun v => (original v).val)
      (fun v => Selected v ∧ ell+1 ≤ A.freeLevel (original v).val)
      hNamed ⟨i,hGeneration⟩
  refine ⟨W,hFinite,hSocleH,hDelete,t,P,e,r,hr,hrt,
    hIrred,hCopy,hLow,hHigh,i,hGeneration,?_⟩
  intro b hb
  obtain ⟨v,j,m,hBoth,hReal,hStrict,hm,hType⟩ := hChosenHigh b hb
  exact ⟨v,j,m,hBoth.1,hBoth.2,hReal,hStrict,hm,hType⟩

end SuccessorTree.V10

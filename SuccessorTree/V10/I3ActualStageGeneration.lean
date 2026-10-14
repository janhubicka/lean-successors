import SuccessorTree.V10.I3ActualWitnessGeneration
import SuccessorTree.V10.I3AmbientSocleBridge
import SuccessorTree.V10.HFiniteAge
import Mathlib.Tactic

/-!
# Lemma 6.53 for a failed finite B3 test in the actual numerical H model

The author uses k at least one less than the maximum forbidden
size. The finite family bound is expressed here by the size of each
normalized forbidden pattern, not by an unrelated bound on every
possible atomic configuration.

A failed corrected B3 test for the ambient-original pool yields a
genuine finite L-only witness. Because the exact numerical H model
is forbidden-free, that witness's forbidden copy has a nonempty
proper lower segment ending at ell. A full upper prefix type over
the tested cut comes from an original numerical H address. If that
original has free cut at least ell+1, then it lies strictly after
ell; irreducibility proves it is a REAL numerical H vertex without
assuming realness or a coordinate decomposition.

The checked complete induced-copy relocation now proves that
ell has generation r-1 and every upper original appearing in the
forbidden copy has strictly greater generation. All Boolean
directed, unary, diagonal and absent L atoms are preserved. No E
is imposed on the arbitrary finite L-age witness.

The remaining manuscript-facing step is identifying the exact I3
selected-stage source function with the finite ambient-pool
prescription used below, and inserting the resulting per-generation
bound into the already checked numerical recurrence.
-/

namespace SuccessorTree.V10

/-- The number of vertices of a normalized forbidden structure;
the neutral singleton is excluded separately by the normalization. -/
def NormalizedForbidden.patternCard
    {db du dd : Nat} : NormalizedForbidden db du dd → Nat
  | .singleton _ _ => 1
  | .nontrivial t _ _ _ => t

/-- A forbidden copy meeting ell in an age witness whose lower
socle is a forbidden-free ambient model has a PROPER lower cut,
and its size is at most the given bound on the particular
forbidden pattern. Thus the lower segment has size ≤k.

We deliberately retain the exact forbidden pattern in the witness:
it is an actual member of the bad family, not an invented one.
-/
theorem normalizedForbidden_bounded_I3_proper_cut
    {db du dd : Nat}
    (C W : AgeTestModel db du dd) (ell k : Nat)
    (bad : NormalizedForbidden db du dd)
    (hBound : bad.patternCard ≤ k+1)
    (hSocle : SameInitialL W C ell)
    (hAvoidC : bad.Avoids C)
    (hAvoidDelete : bad.Avoids (W.withoutVertex ell))
    (hViolation : ¬ bad.Avoids W) :
    ∃ (t : Nat) (P : ForbiddenAtomicPattern t db du dd)
      (e : Fin t → Nat) (r : Nat)
      (hr : 0 < r) (hrt : r < t) (hrk : r ≤ k),
      P.Irreducible ∧
      W.Realizes P e ∧
      (¬ ∃ f : Fin t → Nat, (W.withoutVertex ell).Realizes P f) ∧
      e (⟨r-1, by omega⟩ : Fin t) = ell ∧
      (∀ a : Fin t, a.val < r ↔ e a ≤ ell) ∧
      (∀ a : Fin t, r ≤ a.val ↔ ell < e a) := by
  classical
  cases bad with
  | singleton P hNonNeutral =>
      change ¬ ∃ f : Fin 1 → Nat, C.Realizes P f at hAvoidC
      change ¬ ∃ f : Fin 1 → Nat,
        (W.withoutVertex ell).Realizes P f at hAvoidDelete
      change ¬ ¬ ∃ f : Fin 1 → Nat, W.Realizes P f at hViolation
      obtain ⟨e,hCopy⟩ := not_not.mp hViolation
      obtain ⟨a,ha⟩ :=
        forbiddenCopy_meets_tested_coordinate
          W ell P e hCopy hAvoidDelete
      obtain ⟨b,hb⟩ :=
        forbiddenCopy_has_upper_of_sameInitialL
          W C ell P e hSocle hAvoidC hCopy
      have hab : a = b := Subsingleton.elim _ _
      rw [←hab] at hb
      omega
  | nontrivial t P ht hIrred =>
      change t ≤ k+1 at hBound
      change ¬ ∃ f : Fin t → Nat, C.Realizes P f at hAvoidC
      change ¬ ∃ f : Fin t → Nat,
        (W.withoutVertex ell).Realizes P f at hAvoidDelete
      change ¬ ¬ ∃ f : Fin t → Nat, W.Realizes P f at hViolation
      obtain ⟨e,hCopy⟩ := not_not.mp hViolation
      have hAt : ∃ a : Fin t, e a = ell :=
        forbiddenCopy_meets_tested_coordinate
          W ell P e hCopy hAvoidDelete
      have hUpper : ∃ b : Fin t, ell < e b :=
        forbiddenCopy_has_upper_of_sameInitialL
          W C ell P e hSocle hAvoidC hCopy
      obtain ⟨r,hr,hrt,hLast,hLow,hHigh⟩ :=
        i3_forbidden_age_copy_lower_cut
          W P e hCopy ell hAt hUpper
      have hrk : r ≤ k := by omega
      exact ⟨t,P,e,r,hr,hrt,hrk,hIrred,hCopy,
        hAvoidDelete,hLast,hLow,hHigh⟩

/-- Lemma 6.53's generation assertion for a failed corrected B3
test of the actual finite numerical H ambient-original pool.

The only explicit source/cut input is that each listed original has
the cut ell+1 in its actual E-free-level type. This automatically
places it strictly after ell. No premise says that an original
is a real H vertex or prescribes its generation: those numerical
coordinates and the strict-generation conclusion follow from
the irreducible forbidden configuration itself.

A further bounded-family size premise is exactly the manuscript's
choice of k for its finite forbidden family. -/
theorem finiteNumericH_failedPoolB3_generation
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N ell : Nat)
    (hEll : ell < N)
    (original : Fin M → Nat)
    (hFreeCut : ∀ v : Fin M,
      ell+1 ≤ (finiteNumericH K k N).freeLevel (original v))
    (hFamilyBound : ∀ bad, bad ∈ family →
      bad.patternCard ≤ k+1)
    (hFailure :
      ¬ (ambientPoolPrescribedData
        (finiteNumericH K k N) ell original).CorrectedB3 family) :
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
            ∃ j m : Nat, r-1 < m ∧ m ≤ k ∧
              ell < hPosition k j m ∧
              RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
                RelationalPrefixType.ofAgeModel
                  (finiteNumericHL K k N) (ell+1)
                  (hPosition k j m)) := by
  classical
  let A := finiteNumericH K k N
  have hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  obtain ⟨S0,hS0,W,hFinite,hSame,hDelete,hUpper,bad,hMember,hBad⟩ :=
    ambientPool_failedCorrectedB3_has_original_witness
      family A ell original hFailure
  have hSocle : SameInitialL W (finiteNumericHL K k N) ell := by
    exact ambientPool_B3_witness_sameAmbientSocle
      A ell original hEll S0 hS0 W hSame
  obtain ⟨t,P,e,r,hr,hrt,hrk,hIrred,hCopy,hDeleteP,hLast,hLow,hHigh⟩ :=
    normalizedForbidden_bounded_I3_proper_cut
      A.L W ell k bad (hFamilyBound bad hMember)
      hSocle (hAvoidA bad hMember) (hDelete bad hMember) hBad
  have hUpperNamed : ∀ b : Fin t, r ≤ b.val →
      ∃ originalAddress : Nat,
        ell < originalAddress ∧
        RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (ell+1) originalAddress := by
    intro b hb
    have hAbove : ell < e b := (hHigh b).1 hb
    obtain ⟨v,hType⟩ := hUpper (e b) (hCopy.2.1 b) hAbove
    have hAfter : ell < original v := by
      have hcut : ell+1 ≤ A.freeLevel (original v) := hFreeCut v
      have haddress : A.freeLevel (original v) ≤ original v :=
        A.freeLevel_le (original v)
      exact lt_of_lt_of_le (Nat.lt_succ_self ell)
        (hcut.trans haddress)
    exact ⟨original v,hAfter,hType⟩
  obtain ⟨i,hEllGeneration,hStrictUpper⟩ :=
    numericI3_actual_witness_generation_conclusions
      K k N ell r hr hrt hrk W hSocle
      P hIrred e hCopy hDeleteP hLast hUpperNamed
  exact ⟨W,hFinite,hSocle,hDelete,t,P,e,r,hr,hrt,
    hIrred,hCopy,hLow,hHigh,i,hEllGeneration,hStrictUpper⟩

end SuccessorTree.V10

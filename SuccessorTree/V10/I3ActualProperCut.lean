import SuccessorTree.V10.I3ForbiddenCutIndex
import SuccessorTree.V10.I3AmbientSocleBridge
import SuccessorTree.V10.M2B3CopyCases
import Mathlib.Tactic

/-!
# A failed I3 B3 test forces a genuine nonempty proper lower cut

There are two separate facts in the manuscript's argument:

1. The finite failed-B3 L-witness contains a forbidden copy through
   the inserted coordinate ell.
2. That copy must have a vertex ABOVE ell. Otherwise all its vertices
   lie in the common initial L-socle, so the same forbidden pattern
   already occurs in the forbidden-free ambient H model.

Combining them with ordered strict monotonicity gives the precise
nonempty proper lower initial segment of Lemma 6.53. This eliminates
the extra hUpper premise of the previously checked exact-cut lemma
for actual forbidden-free I3 ambient witnesses.

No auxiliary E is added to the finite L witness, and no axiom or
manuscript proof text is changed.
-/

namespace SuccessorTree.V10

/-- A forbidden pattern present in W but absent both from its
ambient initial L-model and from W with ell deleted yields an
ordered copy crossing ell, with a uniquely defined proper initial
lower segment. A singleton bad pattern is impossible in this
situation: it cannot meet ell AND have an upper vertex. -/
theorem normalizedForbidden_I3_proper_lower_cut
    {db du dd : Nat}
    (C W : AgeTestModel db du dd)
    (ell : Nat)
    (bad : NormalizedForbidden db du dd)
    (hSocle : SameInitialL W C ell)
    (hAvoidAmbient : bad.Avoids C)
    (hAvoidDelete : bad.Avoids (W.withoutVertex ell))
    (hNotAvoidW : ¬ bad.Avoids W) :
    ∃ (t : Nat) (P : ForbiddenAtomicPattern t db du dd)
      (e : Fin t → Nat) (r : Nat)
      (hr : 0 < r) (hrt : r < t),
      P.Irreducible ∧
      W.Realizes P e ∧
      e (⟨r-1, by omega⟩ : Fin t) = ell ∧
      (∀ a : Fin t, a.val < r ↔ e a ≤ ell) ∧
      (∀ a : Fin t, r ≤ a.val ↔ ell < e a) := by
  classical
  cases bad with
  | singleton P hNonNeutral =>
      change ¬ ∃ f : Fin 1 → Nat, C.Realizes P f at hAvoidAmbient
      change ¬ ∃ f : Fin 1 → Nat,
        (W.withoutVertex ell).Realizes P f at hAvoidDelete
      change ¬ ¬ ∃ f : Fin 1 → Nat, W.Realizes P f at hNotAvoidW
      obtain ⟨e,hCopy⟩ := not_not.mp hNotAvoidW
      obtain ⟨a,ha⟩ :=
        forbiddenCopy_meets_tested_coordinate
          W ell P e hCopy hAvoidDelete
      obtain ⟨b,hb⟩ :=
        forbiddenCopy_has_upper_of_sameInitialL
          W C ell P e hSocle hAvoidAmbient hCopy
      have hab : a = b := Subsingleton.elim _ _
      rw [← hab] at hb
      omega
  | nontrivial t P ht hIrred =>
      change ¬ ∃ f : Fin t → Nat, C.Realizes P f at hAvoidAmbient
      change ¬ ∃ f : Fin t → Nat,
        (W.withoutVertex ell).Realizes P f at hAvoidDelete
      change ¬ ¬ ∃ f : Fin t → Nat, W.Realizes P f at hNotAvoidW
      obtain ⟨e,hCopy⟩ := not_not.mp hNotAvoidW
      have hAt : ∃ a : Fin t, e a = ell :=
        forbiddenCopy_meets_tested_coordinate
          W ell P e hCopy hAvoidDelete
      have hUpper : ∃ b : Fin t, ell < e b :=
        forbiddenCopy_has_upper_of_sameInitialL
          W C ell P e hSocle hAvoidAmbient hCopy
      obtain ⟨r,hr,hrt,hLast,hLow,hHigh⟩ :=
        i3_forbidden_age_copy_lower_cut
          W P e hCopy ell hAt hUpper
      exact ⟨t,P,e,r,hr,hrt,hIrred,hCopy,hLast,hLow,hHigh⟩

/-- Failure of the ACTUAL finite ambient-original pool B3 test,
when the ambient age is forbidden-free, automatically yields a
nontrivial irreducible forbidden copy with exactly the lower cut
required by Lemma 6.53. All upper witnesses still carry genuine
ambient original L-types.

The only remaining manuscript identification is that its I3
prescription f_ell is this actual pool map, or an equivalent
representative selection on the same source data. -/
theorem ambientPool_failedB3_has_proper_I3_cut
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (ell : Nat) (hCut : ell < A.size)
    (original : Fin M → Nat)
    (hFailure :
      ¬ (ambientPoolPrescribedData A ell original).CorrectedB3 family) :
    ∃ W : AgeTestModel db du dd,
      W.BoundedCarrier ∧
      SameInitialL W A.L ell ∧
      (∀ bad, bad ∈ family → bad.Avoids (W.withoutVertex ell)) ∧
      (∀ x, x ∈ W.carrier → ell < x →
        ∃ v : Fin M,
          RelationalPrefixType.ofAgeModel W (ell + 1) x =
            RelationalPrefixType.ofAgeModel A.L (ell + 1) (original v)) ∧
      ∃ (t : Nat) (P : ForbiddenAtomicPattern t db du dd)
        (e : Fin t → Nat) (r : Nat)
        (hr : 0 < r) (hrt : r < t),
        P.Irreducible ∧
        W.Realizes P e ∧
        e (⟨r-1, by omega⟩ : Fin t) = ell ∧
        (∀ a : Fin t, a.val < r ↔ e a ≤ ell) ∧
        (∀ a : Fin t, r ≤ a.val ↔ ell < e a) := by
  obtain ⟨S0,hS0,W,hFinite,hSame,hDelete,hUpper,bad,hMember,hBad⟩ :=
    ambientPool_failedCorrectedB3_has_original_witness
      family A ell original hFailure
  have hSocle : SameInitialL W A.L ell :=
    ambientPool_B3_witness_sameAmbientSocle
      A ell original hCut S0 hS0 W hSame
  obtain ⟨t,P,e,r,hr,hrt,hIrred,hCopy,hLast,hLow,hHigh⟩ :=
    normalizedForbidden_I3_proper_lower_cut
      A.L W ell bad hSocle
      (hAvoidA bad hMember) (hDelete bad hMember) hBad
  exact ⟨W,hFinite,hSocle,hDelete,hUpper,
    t,P,e,r,hr,hrt,hIrred,hCopy,hLast,hLow,hHigh⟩

end SuccessorTree.V10

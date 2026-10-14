import SuccessorTree.V10.I3AmbientPrescribedPool
import Mathlib.Tactic

/-!
# I3 finite age witness: its actual ambient ordinary L-socle

The manuscript's signatures compare age witnesses at different
tested coordinates INSIDE one ambient numerical H+ model. The B3
failure theorem originally provided agreement with the prescribed
socle of f(S0). For the ACTUAL finite ambient-pool prescription,
that socle is the induced L-socle of the same ambient partial
structure. Therefore no extra "common socle" axiom is needed in
the signature-splice step.

We also select one concrete ordered forbidden copy meeting the
tested coordinate, including the non-neutral singleton case.
Everything below holds for the existing normalized finite
binary/unary/diagonal signature. No higher arity, axiom weakening
or manuscript prose edit is involved.
-/

namespace SuccessorTree.V10

/-- Each prescribed target is literally the actual next-cut type
of one of the named original source representatives, not just an
abstract L-reduct of such a type. -/
theorem ambientPoolPrescribedData_target_original
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Nat)
    (T : PartialTypeWithE ell db du dd)
    (hT : T ∈ (ambientPoolPrescribedData A ell original).source) :
    ∃ v : Fin M,
      (ambientPoolPrescribedData A ell original).target T =
        A.partialTypeAt (ell + 1) (original v) := by
  classical
  change ∃ v : Fin M, A.partialTypeAt ell (original v) = T at hT
  refine ⟨Classical.choose hT, ?_⟩
  change ambientPoolTarget A ell original T =
    A.partialTypeAt (ell + 1) (original (Classical.choose hT))
  simp only [ambientPoolTarget, dite_eq_left hT]

/-- The finite ordinary socle recovered from an actual ambient type
is the same induced L-socle as the ambient partial structure itself.
No agreement on the distinguished type vertex or E is asserted. -/
theorem ambient_partialType_prescribedSocle
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell v : Nat) (hCut : ell < A.size) :
    SameInitialL
      (prescribedOrdinarySocle (A.partialTypeAt (ell + 1) v))
      A.L ell := by
  have h : SameInitialL A.L
      (prescribedOrdinarySocle (A.partialTypeAt (ell + 1) v))
      ell :=
    prescribedOrdinarySocle_matches_witness A v
      (A.partialTypeAt (ell + 1) v) hCut rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (h.1 x hx).symm
  · intro x y hx hy t
    exact (h.2.1 x y hx hy t).symm
  · intro x hx t
    exact (h.2.2.1 x hx t).symm
  · intro x hx t
    exact (h.2.2.2 x hx t).symm

/-- A B3 witness matching any ACTUAL finite-pool prescribed target
has the exact lower ordinary L-socle of the same ambient model,
even if source representatives had identical old types. -/
theorem ambientPool_B3_witness_sameAmbientSocle
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Nat)
    (hCut : ell < A.size)
    (S0 : PartialTypeWithE ell db du dd)
    (hS0 : S0 ∈ (ambientPoolPrescribedData A ell original).source)
    (W : AgeTestModel db du dd)
    (hSame : SameInitialL W
      (prescribedOrdinarySocle
        ((ambientPoolPrescribedData A ell original).target S0)) ell) :
    SameInitialL W A.L ell := by
  obtain ⟨v,hTarget⟩ :=
    ambientPoolPrescribedData_target_original A ell original S0 hS0
  have hAmbient : SameInitialL
      (prescribedOrdinarySocle
        ((ambientPoolPrescribedData A ell original).target S0))
      A.L ell := by
    rw [hTarget]
    exact ambient_partialType_prescribedSocle A ell (original v) hCut
  exact hSame.trans hAmbient

/-- The canonical ambient-pool output really is an admissible
Kpt next-cut type, provided the named original vertices are in the
forbidden-free ambient structure and their genuine free cuts reach
the inserted level. The guard is essential: a merely numerical
`partialTypeAt (ell+1)` need not be an admissible Kpt node when the
original's free cut is shorter. -/
theorem ambientPoolPrescribedData_targets_admissible
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (ell : Nat) (original : Fin M → Nat)
    (hIn : ∀ v : Fin M, original v < A.size)
    (hCut : ∀ v : Fin M, ell + 1 ≤ A.freeLevel (original v)) :
    ∀ T, T ∈ (ambientPoolPrescribedData A ell original).source →
      IsAdmissibleRawType family
        (⟨ell + 1,
          (ambientPoolPrescribedData A ell original).target T⟩ :
          RawPartialTypeNode db du dd) := by
  intro T hT
  obtain ⟨v,hTarget⟩ :=
    ambientPoolPrescribedData_target_original A ell original T hT
  rw [hTarget]
  have hRawAd : IsAdmissibleRawType family
      (A.rawTypeAtFree (original v)) :=
    ⟨A,original v,hIn v,hAvoid,rfl⟩
  have hPrefix :=
    admissibleRawType_closed_under_prefix family
      hRawAd (ell+1) (hCut v)
  change IsAdmissibleRawType family
    (⟨ell+1, (A.partialTypeAt
      (A.freeLevel (original v)) (original v)).restrict (hCut v)⟩ :
      RawPartialTypeNode db du dd) at hPrefix
  rw [A.partialTypeAt_restrict
    (ell+1) (A.freeLevel (original v)) (original v) (hCut v)] at hPrefix
  exact hPrefix

/-- Failure of the actual finite ambient-pool corrected B3 supplies
an age witness with the manuscript's common AMBIENT socle, complete
original names on all upper vertices, and a concrete forbidden
ordered copy meeting the tested coordinate. This contains all
finite-age data needed for the chosen-signature construction.

What remains for actual I3 is to identify its prescribed f_ell and
selected original pool with this source function, and prove the
generation constraints of Lemma 6.53. -/
theorem ambientPool_failedCorrectedB3_full_I3_witness
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
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
      ∃ (bad : NormalizedForbidden db du dd),
        bad ∈ family ∧
        ∃ (r : Nat) (P : ForbiddenAtomicPattern r db du dd)
          (e : Fin r → Nat),
          W.Realizes P e ∧ ∃ a : Fin r, e a = ell := by
  obtain ⟨S0,hS0,W,hFinite,hSame,hDelete,hUpper,bad,hMem,hBad⟩ :=
    ambientPool_failedCorrectedB3_has_original_witness
      family A ell original hFailure
  have hSocle : SameInitialL W A.L ell :=
    ambientPool_B3_witness_sameAmbientSocle
      A ell original hCut S0 hS0 W hSame
  obtain ⟨r,P,e,hCopy,hAt⟩ :=
    normalizedForbidden_bad_copy_meets_tested_coordinate
      W ell bad (hDelete bad hMem) hBad
  exact ⟨W,hFinite,hSocle,hDelete,hUpper,bad,hMem,r,P,e,hCopy,hAt⟩

end SuccessorTree.V10

import SuccessorTree.V10.PrescribedInsertPartial
import SuccessorTree.V10.AdmissibleSigmaSTree
import Mathlib.Tactic

/-!
# A prescribed admissible Kpt crossing supplies its OWN valid insertion cut

Lemma 6.51's f maps actual admissible level-ell types to actual admissible
level-(ell+1) types. The finite prescribed insertion constructor from the
previous module uses a parameter d whose E-column is valid and satisfies
the strict gate d=0 or d<ell.

These are not additional hypotheses on f. Every actual admissible target
at level ell+1 has a forbidden-free ambient witness. Extract the actual
ordinary vertex ell, its uniquely determined first missing E coordinate d,
and the valid no-new-tuples column. All requirements follow from the three
partial-structure axioms. In particular both directed L relations above d
vanish.

When two such targets agree on their complete ordinary socle (the B2
condition), their cuts AND entire lower inserted L columns coincide.
This is the precise source-choice-independence input for the prescribed
matching-socle branch.
-/

namespace SuccessorTree.V10

/-- EVERY genuinely admissible prescribed target at level ell+1 supplies
a valid canonical new-ordinary E cut. Both the no-new-tuples condition and
the strict 0-or-below-ell gate are DERIVED, not postulated. -/
theorem admissiblePrescribedCut_exists
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat)
    (b : AdmissibleKptNode family)
    (hbLevel : b.1.1 = ell + 1) :
    ∃ d : Nat,
      d ≤ ell ∧ (d = 0 ∨ d < ell) ∧
      ValidNewOrdinaryColumn
        (b.1.2) d := by
  rcases b with ⟨⟨n,Q⟩,hAd⟩
  dsimp at hbLevel
  subst n
  obtain ⟨A,v,hv,hAvoid,hRaw⟩ := hAd
  have hFree : A.freeLevel v = ell + 1 := by
    have hh := congrArg Sigma.fst hRaw
    change ell + 1 = A.freeLevel v at hh
    omega
  have hType : Q = A.partialTypeAt (ell+1) v := by
    have hPair :
        (⟨ell+1,Q⟩ : RawPartialTypeNode db du dd) =
          (⟨ell+1,A.partialTypeAt (ell+1) v⟩ :
            RawPartialTypeNode db du dd) := by
      calc
        (⟨ell+1,Q⟩ : RawPartialTypeNode db du dd) =
          A.rawTypeAtFree v := hRaw
        _ = (⟨ell+1,A.partialTypeAt (ell+1) v⟩ :
          RawPartialTypeNode db du dd) := by
            change
              (⟨A.freeLevel v,
                A.partialTypeAt (A.freeLevel v) v⟩ :
                RawPartialTypeNode db du dd) =
              (⟨ell+1,A.partialTypeAt (ell+1) v⟩ :
                RawPartialTypeNode db du dd)
            rw [hFree]
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hPair
  let d := A.freeLevel ell
  have hd : d ≤ ell := A.freeLevel_le ell
  have hGate : d = 0 ∨ d < ell := by
    by_cases hz : d = 0
    · exact Or.inl hz
    · exact Or.inr (freeLevel_pos_lt_vertex A ell (by omega))
  have hValid : ValidNewOrdinaryColumn Q d := by
    rw [hType]
    exact validNewColumn_of_extracted_partialType A v ell hv (by omega)
  exact ⟨d,hd,hGate,hValid⟩

/-- The extracted cut is intrinsic to the prescribed target, regardless of
which finite ambient structure represents its admissibility. -/
theorem admissiblePrescribedCut_unique
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (d e : Nat) (hd : d ≤ ell) (he : e ≤ ell)
    (hD : ValidNewOrdinaryColumn Q d)
    (hE : ValidNewOrdinaryColumn Q e) :
    d = e :=
  lowerInsertedCut_eq_of_sameSocle
    (sameOrdinarySocle_refl Q) d e hd he hD hE

/-- The UNIQUE prescribed cut may be selected once and for all. It depends
only on the actual Kpt node, not on its witnessing ambient structure. -/
noncomputable def admissiblePrescribedCut
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat)
    (b : AdmissibleKptNode family)
    (hbLevel : b.1.1 = ell + 1) : Nat :=
  Classical.choose (admissiblePrescribedCut_exists family ell b hbLevel)

/-- Every selected cut is bounded, strict when positive, and validates the
actual E/last-ordinary-column record of the admissible target. -/
theorem admissiblePrescribedCut_spec
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat)
    (b : AdmissibleKptNode family)
    (hbLevel : b.1.1 = ell + 1) :
    admissiblePrescribedCut family ell b hbLevel ≤ ell ∧
    (admissiblePrescribedCut family ell b hbLevel = 0 ∨
      admissiblePrescribedCut family ell b hbLevel < ell) ∧
    ValidNewOrdinaryColumn
      (b.1.2) (admissiblePrescribedCut family ell b hbLevel) :=
  Classical.choose_spec (admissiblePrescribedCut_exists family ell b hbLevel)

/-- B2 ordinary-socle compatibility of two admissible targets forces their
selected E cuts AND every new ordinary L bit to be exactly equal. This is
the choice-independence needed for the lower half of the prescribed map. -/
theorem admissiblePrescribed_lower_data_unique
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat)
    (b c : AdmissibleKptNode family)
    (hb : b.1.1 = ell + 1) (hc : c.1.1 = ell + 1)
    (hSocle : SameOrdinarySocle (b.1.2) (c.1.2)) :
    admissiblePrescribedCut family ell b hb =
      admissiblePrescribedCut family ell c hc ∧
    lowerInsertedColumn (b.1.2) =
      lowerInsertedColumn (c.1.2) := by
  have hB := admissiblePrescribedCut_spec family ell b hb
  have hC := admissiblePrescribedCut_spec family ell c hc
  refine ⟨?_,lowerInsertedColumn_eq_of_sameSocle hSocle⟩
  exact lowerInsertedCut_eq_of_sameSocle hSocle
    (admissiblePrescribedCut family ell b hb)
    (admissiblePrescribedCut family ell c hc)
    hB.1 hC.1 hB.2.2 hC.2.2

end SuccessorTree.V10

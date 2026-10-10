import SuccessorTree.V10.AmbientSignature
import SuccessorTree.V10.AdmissibleKptLevelTree
import Mathlib.Tactic

/-!
# Signature types from actual admissible Kpt crossings

The signature argument labels every upper age-test vertex by an original
vertex of one fixed ambient partial structure C. The manuscript says that
the upper vertex realizes the prescribed crossing at level ell+1.

Here the crossing is no longer an opaque type record: it is the actual
LevelTree ancestor, at that level, of the admissible Kpt type represented
by the named ambient original. We prove that its complete L-reduct is
literally the induced ambient L-type through the same cut. Consequently
an age-test vertex realizing that crossing has the full atomic type of the
named original required by the checked signature-splice theorem.

No age-test existence or boring-extension lemma is assumed or proved here.
That is the remaining construction step.
-/

namespace SuccessorTree.V10

/-- The actual Kpt ancestor of an original represented in A is exactly
the complete induced L+ prefix extracted from A at that cut. -/
theorem admissibleKpt_original_ancestor_value
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (v cut : Nat)
    (hAd : IsAdmissibleRawType family (A.rawTypeAtFree v))
    (hcut : cut ≤ A.freeLevel v) :
    (LevelTree.ancestor
      (⟨A.rawTypeAtFree v, hAd⟩ : AdmissibleKptNode family)
      cut (by
        change cut ≤ A.freeLevel v
        exact hcut)).1 =
      (⟨cut, A.partialTypeAt cut v⟩ :
        RawPartialTypeNode db du dd) := by
  rw [admissibleKpt_levelTree_ancestor_eq]
  change rawPartialTypeAncestor (A.rawTypeAtFree v) cut hcut =
    (⟨cut, A.partialTypeAt cut v⟩ : RawPartialTypeNode db du dd)
  apply Sigma.ext
  · rfl
  · change
      (A.partialTypeAt (A.freeLevel v) v).restrict hcut =
        A.partialTypeAt cut v
    exact A.partialTypeAt_restrict cut (A.freeLevel v) v hcut

/-- If an upper vertex of an age-test witness realizes the L-reduct of
that ACTUAL Kpt crossing, then it has exactly the full directed atomic
type of the named ambient original through the cut. -/
theorem actualKpt_crossing_implies_fullAtomic
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (C : EnumeratedPartialStructure db du dd)
    (W : AgeTestModel db du dd)
    (original upper cut : Nat)
    (hAd : IsAdmissibleRawType family (C.rawTypeAtFree original))
    (hcut : cut ≤ C.freeLevel original)
    (hWitness :
      RelationalPrefixType.ofAgeModel W cut upper =
        (LevelTree.ancestor
          (⟨C.rawTypeAtFree original, hAd⟩ :
            AdmissibleKptNode family)
          cut (by
            change cut ≤ C.freeLevel original
            exact hcut)).1.2.lReduct) :
    fullAtomicTypePrefix W.binary W.unary W.diagonal cut upper =
      fullAtomicTypePrefix C.L.binary C.L.unary C.L.diagonal
        cut original := by
  have hAncestor :=
    admissibleKpt_original_ancestor_value
      family C original cut hAd hcut
  have hLR : RelationalPrefixType.ofAgeModel W cut upper =
      (C.partialTypeAt cut original).lReduct := by
    rw [hAncestor] at hWitness
    exact hWitness
  exact equal_reduct_types_imply_fullAtomic W C.L
    cut upper original hLR

/-- Signature collision contradiction when every non-bottom signature
label is an actual ambient original and the witness upper vertex realizes
the corresponding genuine Kpt ancestor at its own tested cut.

Thus the former manuscript-facing full-type hypotheses are consequences,
rather than assumptions. The remaining paper-specific input is exactly
that the local-age construction realizes these prescribed crossings. -/
theorem signature_collision_impossible_of_actual_kpt_crossings
    {r M db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : ForbiddenAtomicPattern r db du dd)
    (C : EnumeratedPartialStructure db du dd)
    (A0 A1 : AgeTestModel db du dd)
    (original : Fin M → Nat)
    (signature : Fin r → Option (Fin M))
    (e0 e1 : Fin r → Nat) (ell0 ell1 : Nat)
    (hLevels : ell0 < ell1)
    (hOld : A0.Realizes F e0)
    (hNew : A1.Realizes F e1)
    (hCutOld : ∀ i, signature i = none ↔ e0 i ≤ ell0)
    (hCutNew : ∀ i, signature i = none ↔ e1 i ≤ ell1)
    (hLaterSocle : ∀ x, x ≤ ell1 → x ∈ A1.carrier)
    (hSocle0B : ∀ x y, x ≤ ell0 → y ≤ ell0 →
      ∀ t : Fin db, A0.binary x y t = C.L.binary x y t)
    (hSocle1B : ∀ x y, x ≤ ell1 → y ≤ ell1 →
      ∀ t : Fin db, A1.binary x y t = C.L.binary x y t)
    (hSocle0U : ∀ x, x ≤ ell0 →
      ∀ t : Fin du, A0.unary x t = C.L.unary x t)
    (hSocle1U : ∀ x, x ≤ ell1 →
      ∀ t : Fin du, A1.unary x t = C.L.unary x t)
    (hSocle0D : ∀ x, x ≤ ell0 →
      ∀ t : Fin dd, A0.diagonal x t = C.L.diagonal x t)
    (hSocle1D : ∀ x, x ≤ ell1 →
      ∀ t : Fin dd, A1.diagonal x t = C.L.diagonal x t)
    (hAd : ∀ v : Fin M,
      IsAdmissibleRawType family (C.rawTypeAtFree (original v)))
    (hOriginalCut0 : ∀ b v, signature b = some v →
      ell0 + 1 ≤ C.freeLevel (original v))
    (hOriginalCut1 : ∀ b v, signature b = some v →
      ell1 + 1 ≤ C.freeLevel (original v))
    (hCross0 : ∀ b v, signature b = some v →
      RelationalPrefixType.ofAgeModel A0 (ell0 + 1) (e0 b) =
        (LevelTree.ancestor
          (⟨C.rawTypeAtFree (original v), hAd v⟩ :
            AdmissibleKptNode family)
          (ell0 + 1) (by
            change ell0 + 1 ≤ C.freeLevel (original v)
            exact hOriginalCut0 b v ‹signature b = some v›)).1.2.lReduct)
    (hCross1 : ∀ b v, signature b = some v →
      RelationalPrefixType.ofAgeModel A1 (ell1 + 1) (e1 b) =
        (LevelTree.ancestor
          (⟨C.rawTypeAtFree (original v), hAd v⟩ :
            AdmissibleKptNode family)
          (ell1 + 1) (by
            change ell1 + 1 ≤ C.freeLevel (original v)
            exact hOriginalCut1 b v ‹signature b = some v›)).1.2.lReduct)
    (hNoForbiddenAway : ∀ f : Fin r → Nat,
      A1.Realizes F f → (∀ i, f i ≠ ell1) → False) :
    False := by
  have hType0 : ∀ b v, signature b = some v →
      fullAtomicTypePrefix A0.binary A0.unary A0.diagonal
          (ell0 + 1) (e0 b) =
        fullAtomicTypePrefix C.L.binary C.L.unary C.L.diagonal
          (ell0 + 1) (original v) := by
    intro b v hb
    exact actualKpt_crossing_implies_fullAtomic
      family C A0 (original v) (e0 b) (ell0 + 1)
      (hAd v) (hOriginalCut0 b v hb) (hCross0 b v hb)
  have hType1 : ∀ b v, signature b = some v →
      fullAtomicTypePrefix A1.binary A1.unary A1.diagonal
          (ell1 + 1) (e1 b) =
        fullAtomicTypePrefix C.L.binary C.L.unary C.L.diagonal
          (ell1 + 1) (original v) := by
    intro b v hb
    exact actualKpt_crossing_implies_fullAtomic
      family C A1 (original v) (e1 b) (ell1 + 1)
      (hAd v) (hOriginalCut1 b v hb) (hCross1 b v hb)
  exact signature_collision_impossible_of_ambient_types
    F C.L A0 A1 original signature e0 e1 ell0 ell1
    hLevels hOld hNew hCutOld hCutNew hLaterSocle
    hSocle0B hSocle1B hSocle0U hSocle1U hSocle0D hSocle1D
    hType0 hType1 hNoForbiddenAway

end SuccessorTree.V10

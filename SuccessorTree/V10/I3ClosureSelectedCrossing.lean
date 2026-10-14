import SuccessorTree.V10.I3NoSkipForcesB3
import SuccessorTree.EnvelopeAlgorithm
import Mathlib.Tactic

/-!
# V10: construct the actual crossing from selected closure originals

At one Algorithm 5.4 stage let Z be its meet-and-parameter
closure above the tested cut ell.  A finite original pool represents
Z by complete Kpt prefixes, as proved by ConcreteOriginalPool.
Select exactly those pool names which represent some z in Z
STRICTLY ABOVE ell.  The existing selected-stage constructor gives
a B1/B2 prescribed partial map with admissible outputs.

If (I2) fails, two closure nodes with equal ancestors at ell
have equal ancestors at ell+1.  Therefore this prescribed map
agrees with EVERY consecutive crossing in Z, not just its
chosen source representatives.  This is the missing well-defined
source/graph interface of the manuscript, with no new E on
arbitrary finite L-age witnesses.

Finally the already verified one-gap boring extension implies
that a genuine non-skippable positive level must fail corrected
B3.  The remaining global induction must identify these
closure stages with the actual envelope run and control the
higher-generation ORIGINAL NAMES used by the signatures.
-/

namespace SuccessorTree.V10

/-- At stage ell an ambient name is selected precisely when a
closure node above ell is a prefix of that original. -/
def closureSelectedOriginal
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (original : Fin M → Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (ell : Nat) (v : Fin M) : Prop :=
  ∃ z : AdmissibleKptNode family,
    z ∈ Z ∧
    ∃ (hz : ell < LevelTree.lev z),
      z ≤ A.kptOriginal family hAvoid (original v)

/-- The actual B1/B2 crossing on the source of represented closure
types, using a single fixed original-name universe Fin M and a
cut-dependent selected subset. -/
noncomputable def closureSelectedBoringData
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (original : Fin M → Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (ell : Nat) : PrescribedBoringData ell db du dd :=
  selectedStagePoolPrescribedData A ell original
    (closureSelectedOriginal family A hAvoid original Z ell)

/-- Every prefix of a genuine ambient original has length at
most that original's exact E-free cut. -/
theorem kptBelowOriginal_level_le_free
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (v : Fin A.size) (z : AdmissibleKptNode family)
    (hz : z ≤ A.kptOriginal family hAvoid v) :
    LevelTree.lev z ≤ A.freeLevel v.val := by
  have h := LevelTree.level_le_of_le hz
  change LevelTree.lev z ≤ A.freeLevel v.val at h
  exact h

/-- Exact raw ancestor of a represented prefix: all L and E
coordinates are inherited from the SAME ambient original. -/
theorem kptBelowOriginal_ancestor_raw
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (v : Fin A.size) (z : AdmissibleKptNode family)
    (hz : z ≤ A.kptOriginal family hAvoid v)
    (n : Nat) (hn : n ≤ LevelTree.lev z) :
    (LevelTree.ancestor z n hn).val =
      (⟨n,A.partialTypeAt n v.val⟩ : RawPartialTypeNode db du dd) := by
  have hBelow :
      LevelTree.ancestor z n hn ≤ A.kptOriginal family hAvoid v :=
    (LevelTree.ancestor_le z n hn).trans hz
  have hRaw := kpt_prefix_raw_eq_ambient
    A family hAvoid v (LevelTree.ancestor z n hn) hBelow
  have hLev : LevelTree.lev (LevelTree.ancestor z n hn) = n :=
    LevelTree.level_ancestor z n hn
  rw [hLev] at hRaw
  exact hRaw

/-- The selected-stage function agrees with ALL crossings of Z.
The crucial uniqueness step uses the published Algorithm 5.4
no-(I2) premise, via the already formalized
Envelope.nextPrefix_eq_of_no_meet.

If duplicate old types have different next types, their
representing closure nodes would have a meet exactly at ell,
contradicting no-(I2). -/
theorem closureSelectedBoringData_covers
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (original : Fin M → Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (hPool : ∀ z, z ∈ Z →
      ∃ v : Fin M, z ≤ A.kptOriginal family hAvoid (original v))
    (ell : Nat)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z ∧ ∃ b : AdmissibleKptNode family,
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = ell) :
    CoversClosureCrossing family Z ell
      (closureSelectedBoringData family A hAvoid original Z ell) := by
  classical
  let Selected : Fin M → Prop :=
    closureSelectedOriginal family A hAvoid original Z ell
  let F : PrescribedBoringData ell db du dd :=
    closureSelectedBoringData family A hAvoid original Z ell
  intro z hz hzCut
  obtain ⟨v,hZv⟩ := hPool z hz
  have hSelectedV : Selected v := ⟨z,hz,hzCut,hZv⟩
  have hCutV : ell+1 ≤ A.freeLevel (original v).val := by
    have hLev := kptBelowOriginal_level_le_free
      family A hAvoid (original v) z hZv
    omega
  let T : PartialTypeWithE ell db du dd :=
    A.partialTypeAt ell (original v).val
  have hSource : T ∈ F.source := by
    change ∃ u : Fin M,
      (Selected u ∧ ell+1 ≤ A.freeLevel (original u).val) ∧
      A.partialTypeAt ell (original u).val = T
    exact ⟨v,⟨hSelectedV,hCutV⟩,rfl⟩
  have hOldRaw :
      (LevelTree.ancestor z ell (Nat.le_of_lt hzCut)).val =
        (⟨ell,T⟩ : RawPartialTypeNode db du dd) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid (original v) z hZv ell (Nat.le_of_lt hzCut)
  obtain ⟨w,hSelectedW,_hCutW,hOldW,hNewW⟩ :=
    selectedStagePoolPrescribedData_source_original
      A ell original Selected T hSource
  obtain ⟨z',hz',hzCut',hZw⟩ := hSelectedW
  have hOldRaw' :
      (LevelTree.ancestor z' ell (Nat.le_of_lt hzCut')).val =
        (⟨ell,A.partialTypeAt ell (original w).val⟩ :
          RawPartialTypeNode db du dd) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid (original w) z' hZw ell (Nat.le_of_lt hzCut')
  have hSameOld :
      LevelTree.ancestor z ell (Nat.le_of_lt hzCut) =
        LevelTree.ancestor z' ell (Nat.le_of_lt hzCut') := by
    apply Subtype.ext
    calc
      (LevelTree.ancestor z ell (Nat.le_of_lt hzCut)).val =
          (⟨ell,T⟩ : RawPartialTypeNode db du dd) := hOldRaw
      _ = (⟨ell,A.partialTypeAt ell (original w).val⟩ :
          RawPartialTypeNode db du dd) := by rw [hOldW]
      _ = (LevelTree.ancestor z' ell (Nat.le_of_lt hzCut')).val :=
          hOldRaw'.symm
  have hSameComp : SMTree.Envelope.SameComponent z z' := by
    refine ⟨LevelTree.ancestor z ell (Nat.le_of_lt hzCut),
      LevelTree.ancestor_le z ell (Nat.le_of_lt hzCut),?_⟩
    rw [hSameOld]
    exact LevelTree.ancestor_le z' ell (Nat.le_of_lt hzCut')
  have hNotMeet :
      LevelTree.lev (LevelTree.meet z z') ≠ ell := by
    intro heq
    exact hNoMeet ⟨z,hz,z',hz',hSameComp,heq⟩
  have hSameNext :
      LevelTree.ancestor z (ell+1) (Nat.succ_le_iff.mpr hzCut) =
        LevelTree.ancestor z' (ell+1) (Nat.succ_le_iff.mpr hzCut') :=
    SMTree.Envelope.nextPrefix_eq_of_no_meet
      hzCut hzCut' hSameOld hNotMeet
  have hNextRaw' :
      (LevelTree.ancestor z' (ell+1) (Nat.succ_le_iff.mpr hzCut')).val =
        (⟨ell+1,A.partialTypeAt (ell+1) (original w).val⟩ :
          RawPartialTypeNode db du dd) :=
    kptBelowOriginal_ancestor_raw
      family A hAvoid (original w) z' hZw (ell+1)
        (Nat.succ_le_iff.mpr hzCut')
  have hNewF : F.target T = A.partialTypeAt (ell+1) (original w).val :=
    hNewW
  have hSelectedNext :
      (⟨ell+1,F.target T⟩ : RawPartialTypeNode db du dd) =
        (LevelTree.ancestor z (ell+1) (Nat.succ_le_iff.mpr hzCut)).val := by
    calc
      (⟨ell+1,F.target T⟩ : RawPartialTypeNode db du dd) =
          (⟨ell+1,A.partialTypeAt (ell+1) (original w).val⟩ :
            RawPartialTypeNode db du dd) := by rw [hNewF]
      _ = (LevelTree.ancestor z' (ell+1) (Nat.succ_le_iff.mpr hzCut')).val :=
          hNextRaw'.symm
      _ = (LevelTree.ancestor z (ell+1) (Nat.succ_le_iff.mpr hzCut)).val :=
          congrArg Subtype.val hSameNext.symm
  exact ⟨T,hSource,hOldRaw.symm,hSelectedNext⟩

/-- Genuine B3 failure at every positive non-skippable level
of the concrete represented closure, without any extra stage
source, graph or upper original assumptions. -/
theorem closureSelectedBoringData_failedB3_of_nonSkippable
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (original : Fin M → Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (hPool : ∀ z, z ∈ Z →
      ∃ v : Fin M, z ≤ A.kptOriginal family hAvoid (original v))
    (ell : Nat) (hPos : 0 < ell)
    (hNoMeet : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z ∧ ∃ b : AdmissibleKptNode family,
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = ell)
    (hNoSkip : NonSkippableClosureCrossing family Z ell) :
    ¬ (closureSelectedBoringData family A hAvoid original Z ell).CorrectedB3
      family := by
  let Selected : Fin M → Prop :=
    closureSelectedOriginal family A hAvoid original Z ell
  exact nonSkippableClosureCrossing_implies_failedCorrectedB3
    family Z ell hPos
    (closureSelectedBoringData family A hAvoid original Z ell)
    (closureSelectedBoringData_covers
      family A hAvoid original Z hPool ell hNoMeet)
    (selectedStagePoolPrescribedData_targets_admissible
      family A hAvoid ell original Selected)
    hNoSkip

/-- All positive non-skippable levels with no I1/I2 event,
whose closures are represented by ONE fixed finite original pool,
obey Observation 6.52's exact signature bound R(M).
There is no assumed age-witness or signature-injectivity premise. -/
theorem representedNonSkippableLevels_card_le_signature_capacity
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (original : Fin M → Fin A.size)
    (Z : Nat → Set (AdmissibleKptNode family))
    (levels : Finset Nat)
    (hLevel : ∀ ell, ell ∈ levels → 0 < ell ∧ ell < A.size)
    (hPool : ∀ ell, ell ∈ levels → ∀ z, z ∈ Z ell →
      ∃ v : Fin M, z ≤ A.kptOriginal family hAvoid (original v))
    (hNoMeet : ∀ ell, ell ∈ levels →
      ¬ ∃ a : AdmissibleKptNode family, a ∈ Z ell ∧
        ∃ b : AdmissibleKptNode family, b ∈ Z ell ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = ell)
    (hNoSkip : ∀ ell, ell ∈ levels →
      NonSkippableClosureCrossing family (Z ell) ell) :
    levels.card ≤
      ageSignatureCapacity
        (fun i : Fin family.length => (family.get i).patternCard) M := by
  let Selected : Nat → Fin M → Prop :=
    fun ell v => closureSelectedOriginal family A hAvoid original (Z ell) ell v
  apply selectedStagePool_B3_failure_levels_card_le_signature_capacity
    family A original Selected levels
  intro ell hEll
  obtain ⟨hPos,hCut⟩ := hLevel ell hEll
  have hFail :=
    closureSelectedBoringData_failedB3_of_nonSkippable
      family A hAvoid original (Z ell)
      (hPool ell hEll) ell hPos
      (hNoMeet ell hEll) (hNoSkip ell hEll)
  exact ⟨hCut,hFail⟩

end SuccessorTree.V10

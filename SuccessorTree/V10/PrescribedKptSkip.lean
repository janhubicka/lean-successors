import SuccessorTree.V10.PrescribedAdmissibleImage
import SuccessorTree.V10.LocalAgeNeutralSkip
import Mathlib.Tactic

/-!
# The total prescribed insertion on admissible Kpt nodes

Use the unique matching image whenever the ordinary source socle has
an f-compatible representative, and the previously verified neutral
image otherwise. Below ell, fix the node. Thus the candidate map is
total on actual admissible nodes, not only on selected finite models.

The level formula, the omitted level and the two branch specifications
are proved here. Prefix preservation, injectivity, prescribed values
and weak successor transport are NOT asserted by this module.
-/

namespace SuccessorTree.V10.PrescribedBoringData

variable {ell db du dd : Nat}
variable (F : PrescribedBoringData ell db du dd)
variable (family : List (NormalizedForbidden db du dd))
variable (hB3 : F.CorrectedB3 family)
variable (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
  (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
variable (hPos : 0 < ell)

/-- Select the matching image whose existence and uniqueness are proved
from the actual finite constructor. -/
noncomputable def matchingKptImage
    (a : AdmissibleKptNode family) (hlev : ell ≤ a.1.1)
    (hMatch : F.HasCompatibleSource (a.1.2.restrict hlev)) :
    AdmissibleKptNode family :=
  Classical.choose (F.matchingKptImage_exists family hB3 hTargets hPos
    a hlev hMatch)

/-- The selector has the literal finite-constructor image specification. -/
theorem matchingKptImage_isImage
    (a : AdmissibleKptNode family) (hlev : ell ≤ a.1.1)
    (hMatch : F.HasCompatibleSource (a.1.2.restrict hlev)) :
    F.IsMatchingKptImage family hPos a
      (F.matchingKptImage family hB3 hTargets hPos a hlev hMatch) :=
  (Classical.choose_spec (F.matchingKptImage_exists family hB3 hTargets hPos
    a hlev hMatch)).1

/-- The matching branch raises the level by exactly one. -/
theorem matchingKptImage_level
    (a : AdmissibleKptNode family) (hlev : ell ≤ a.1.1)
    (hMatch : F.HasCompatibleSource (a.1.2.restrict hlev)) :
    (F.matchingKptImage family hB3 hTargets hPos a hlev hMatch).1.1 =
      a.1.1 + 1 :=
  (Classical.choose_spec (F.matchingKptImage_exists family hB3 hTargets hPos
    a hlev hMatch)).2

/-- Any literal matching image agrees with the selected one. In particular
no choice of a finite ambient witness or compatible source affects it. -/
theorem matchingKptImage_eq_of_isImage
    (a : AdmissibleKptNode family) (hlev : ell ≤ a.1.1)
    (hMatch : F.HasCompatibleSource (a.1.2.restrict hlev))
    (b : AdmissibleKptNode family)
    (hb : F.IsMatchingKptImage family hPos a b) :
    F.matchingKptImage family hB3 hTargets hPos a hlev hMatch = b :=
  F.matchingKptImage_graph_unique family hPos a hlev _ b
    (F.matchingKptImage_isImage family hB3 hTargets hPos a hlev hMatch) hb

/-- Total candidate prescribed insertion: matching, neutral, or fixed
below the gap. Compatibility is tested on the node's own full prefix. -/
noncomputable def prescribedKptSkip
    (a : AdmissibleKptNode family) : AdmissibleKptNode family := by
  classical
  exact if hlev : ell ≤ a.1.1 then
    if hMatch : F.HasCompatibleSource (a.1.2.restrict hlev) then
      F.matchingKptImage family hB3 hTargets hPos a hlev hMatch
    else neutralKptImage family ell hPos a hlev
  else a

/-- A source node below ell is literally unchanged. -/
theorem prescribedKptSkip_fixed_below
    (a : AdmissibleKptNode family) (ha : a.1.1 < ell) :
    F.prescribedKptSkip family hB3 hTargets hPos a = a := by
  simp [prescribedKptSkip, Nat.not_le.mpr ha]

/-- In the matching case the total operation is the unique prescribed image. -/
theorem prescribedKptSkip_matching
    (a : AdmissibleKptNode family) (hlev : ell ≤ a.1.1)
    (hMatch : F.HasCompatibleSource (a.1.2.restrict hlev)) :
    F.prescribedKptSkip family hB3 hTargets hPos a =
      F.matchingKptImage family hB3 hTargets hPos a hlev hMatch := by
  simp [prescribedKptSkip, hlev, hMatch]

/-- With no compatible prescribed source, the operation uses the already
verified neutral image; it does not choose an arbitrary new column. -/
theorem prescribedKptSkip_neutral
    (a : AdmissibleKptNode family) (hlev : ell ≤ a.1.1)
    (hNone : ¬ F.HasCompatibleSource (a.1.2.restrict hlev)) :
    F.prescribedKptSkip family hB3 hTargets hPos a =
      neutralKptImage family ell hPos a hlev := by
  simp [prescribedKptSkip, hlev, hNone]

/-- The exact level formula holds in both upper branches. -/
theorem prescribedKptSkip_level
    (a : AdmissibleKptNode family) :
    (F.prescribedKptSkip family hB3 hTargets hPos a).1.1 =
      if ell ≤ a.1.1 then a.1.1+1 else a.1.1 := by
  classical
  by_cases hlev : ell ≤ a.1.1
  · by_cases hMatch : F.HasCompatibleSource (a.1.2.restrict hlev)
    · rw [F.prescribedKptSkip_matching family hB3 hTargets hPos a hlev hMatch,
        F.matchingKptImage_level family hB3 hTargets hPos a hlev hMatch,
        if_pos hlev]
    · rw [F.prescribedKptSkip_neutral family hB3 hTargets hPos a hlev hMatch,
        neutralKptImage_level family ell hPos a hlev, if_pos hlev]
  · simp [prescribedKptSkip, hlev]

/-- No node maps to the inserted level. -/
theorem prescribedKptSkip_omits_level
    (a : AdmissibleKptNode family) :
    (F.prescribedKptSkip family hB3 hTargets hPos a).1.1 ≠ ell := by
  rw [F.prescribedKptSkip_level family hB3 hTargets hPos]
  split_ifs <;> omega

/-- Equal source levels have equal image levels, regardless of which
compatibility branch the two nodes use. -/
theorem prescribedKptSkip_preserves_equal_level
    (a b : AdmissibleKptNode family) (hab : a.1.1 = b.1.1) :
    (F.prescribedKptSkip family hB3 hTargets hPos a).1.1 =
      (F.prescribedKptSkip family hB3 hTargets hPos b).1.1 := by
  rw [F.prescribedKptSkip_level family hB3 hTargets hPos,
    F.prescribedKptSkip_level family hB3 hTargets hPos, hab]

/-- The common numerical level map is strictly increasing. This is not
yet injectivity of the node map or preservation of its tree order. -/
theorem prescribedKptSkip_strict_level
    (a b : AdmissibleKptNode family) (hab : a.1.1 < b.1.1) :
    (F.prescribedKptSkip family hB3 hTargets hPos a).1.1 <
      (F.prescribedKptSkip family hB3 hTargets hPos b).1.1 := by
  rw [F.prescribedKptSkip_level family hB3 hTargets hPos,
    F.prescribedKptSkip_level family hB3 hTargets hPos]
  split_ifs <;> omega

end SuccessorTree.V10.PrescribedBoringData

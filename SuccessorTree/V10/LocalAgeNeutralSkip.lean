import SuccessorTree.V10.LocalAgeNeutralPrefix
import Mathlib.Tactic

/-!
# A total neutral insertion operation on the actual admissible Kpt forest

At levels below ell, leave each actual type unchanged. At level ell or above,
use the unique admissible neutral image. This gives a well-defined total
self-map of the normalized Kpt node set, with a rigid level function that
omits precisely the integer ell from its image on level NUMBERS.

This module proves the exact level formula, strict increase on levels,
level equality preservation, root fixing, and preservation of all prefixes
entirely below or entirely above the gap. A final prefix proof CROSSING the
gap, same-level injectivity and preservation of successor parameters/letters
are still required before claiming a ShapeMap.
-/

namespace SuccessorTree.V10

/-- Total candidate gap insertion on genuinely admissible Kpt nodes.
All noncomputable choices occur only through the representation-independent
neutral image operation from the preceding module. -/
noncomputable def neutralKptSkip
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a : AdmissibleKptNode family) : AdmissibleKptNode family :=
  if h : ell ≤ a.1.1 then neutralKptImage family ell hellPos a h else a

/-- The exact common level shift: n goes to n+1 iff n>=ell. -/
theorem neutralKptSkip_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a : AdmissibleKptNode family) :
    (neutralKptSkip family ell hellPos a).1.1 =
      if ell ≤ a.1.1 then a.1.1 + 1 else a.1.1 := by
  by_cases h : ell ≤ a.1.1
  · simp [neutralKptSkip, h, neutralKptImage_level]
  · simp [neutralKptSkip, h]

/-- No Kpt node maps to the skipped level itself. -/
theorem neutralKptSkip_omits_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a : AdmissibleKptNode family) :
    (neutralKptSkip family ell hellPos a).1.1 ≠ ell := by
  rw [neutralKptSkip_level]
  split_ifs <;> omega

/-- A neutral gap insertion preserves equality of source levels. -/
theorem neutralKptSkip_preserves_equal_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a b : AdmissibleKptNode family)
    (h : a.1.1 = b.1.1) :
    (neutralKptSkip family ell hellPos a).1.1 =
      (neutralKptSkip family ell hellPos b).1.1 := by
  rw [neutralKptSkip_level, neutralKptSkip_level, h]

/-- A neutral gap insertion preserves strict order on ALL numeric levels,
including across the gap. This statement concerns levels only. -/
theorem neutralKptSkip_strict_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a b : AdmissibleKptNode family)
    (h : a.1.1 < b.1.1) :
    (neutralKptSkip family ell hellPos a).1.1 <
      (neutralKptSkip family ell hellPos b).1.1 := by
  rw [neutralKptSkip_level, neutralKptSkip_level]
  by_cases ha : ell ≤ a.1.1
  · have hb : ell ≤ b.1.1 := by omega
    simp [ha, hb]
    omega
  · by_cases hb : ell ≤ b.1.1
    · simp [ha, hb]
      omega
    · simp [ha, hb]
      omega

/-- Every node below ell, including each root, is fixed pointwise. -/
theorem neutralKptSkip_fixed_below
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a : AdmissibleKptNode family)
    (ha : a.1.1 < ell) :
    neutralKptSkip family ell hellPos a = a := by
  simp [neutralKptSkip, Nat.not_le.mpr ha]

/-- Above the gap, the total map is the unique genuine admissible image. -/
theorem neutralKptSkip_above
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a : AdmissibleKptNode family) (ha : ell ≤ a.1.1) :
    neutralKptSkip family ell hellPos a =
      neutralKptImage family ell hellPos a ha := by
  simp [neutralKptSkip, ha]

/-- Every source prefix relation below the gap survives literally. -/
theorem neutralKptSkip_prefix_below
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a b : AdmissibleKptNode family)
    (hba : b ≤ a) (ha : a.1.1 < ell) :
    neutralKptSkip family ell hellPos b ≤
      neutralKptSkip family ell hellPos a := by
  have hraw : b.1 ≤ a.1 := hba
  have hb : b.1.1 < ell := lt_of_le_of_lt hraw.1 ha
  rw [neutralKptSkip_fixed_below family ell hellPos a ha,
    neutralKptSkip_fixed_below family ell hellPos b hb]
  exact hba

/-- Every source prefix relation above the gap remains a literal Kpt prefix
relation, by the checked source-replica compatibility argument. -/
theorem neutralKptSkip_prefix_above
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a b : AdmissibleKptNode family)
    (hba : b ≤ a) (hb : ell ≤ b.1.1) :
    neutralKptSkip family ell hellPos b ≤
      neutralKptSkip family ell hellPos a := by
  have hraw : b.1 ≤ a.1 := hba
  have ha : ell ≤ a.1.1 := hb.trans hraw.1
  rw [neutralKptSkip_above family ell hellPos a ha,
    neutralKptSkip_above family ell hellPos b hb]
  exact neutralKptImage_prefix_le family ell hellPos a b hba hb

end SuccessorTree.V10

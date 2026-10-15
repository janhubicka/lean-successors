import SuccessorTree.V10.KptE1PaddedFreeCutProfile
import SuccessorTree.V10.M2SourceTypeAge
import Mathlib.Tactic

/-!
# An actual forbidden-L-age source for the padded Kpt E1 witness

A complete (n+1)-type Q has an L-only age model whose source ordinary
vertices occupy 0,...,n, and whose type vertex is at n+1. To leave a
NEUTRAL spacer before the type vertex, represent it instead at n+2.

Use the checked carrier-relative sparse pullback and neutral filler
construction: real source coordinates are 0,...,n and n+2; the sole
absent source coordinate n+1 is filled by the allowed neutral singleton.
This preserves the complete L-model of Q on every real coordinate,
including all ABSENT directed binary, unary and diagonal records.
No auxiliary E is attached to any forbidden L-age witness.

This module supplies the forbidden-free L carrier for the already
formalized concrete E free-cut constructor. The remaining task is to
prove linked_E for the profile from the actual old E columns and the
canonical one-step ValidNewOrdinaryColumn premises, and that the resulting
type's complete E record equals Q.
-/

namespace SuccessorTree.V10

/-- Real source vertices before neutral spacing: all ordinary vertices,
together with the final type witness, but not the spacer. -/
def e1PaddedReal (n x : Nat) : Prop :=
  x ≤ n ∨ x = n + 2

/-- The order-preserving map to Q's L-age coordinates. -/
def e1PaddedAgeIndex (n x : Nat) : Nat :=
  if x ≤ n then x else n + 1

/-- Real source vertices map in strictly increasing order. -/
theorem e1PaddedAgeIndex_strict
    (n x y : Nat) (hxy : x < y)
    (hx : e1PaddedReal n x) (hy : e1PaddedReal n y) :
    e1PaddedAgeIndex n x < e1PaddedAgeIndex n y := by
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · simpa [e1PaddedAgeIndex, hx, hy] using hxy
    · subst y
      simpa [e1PaddedAgeIndex, hx] using
        (Nat.lt_succ_of_le hx)
  · subst x
    rcases hy with hy | hy <;> omega

/-- Every genuine source L vertex maps inside the original
complete Q age model (whose type vertex is at n+1). -/
theorem e1PaddedAgeIndex_inside
    (n x : Nat) (hx : e1PaddedReal n x) :
    e1PaddedAgeIndex n x ≤ n + 1 := by
  rcases hx with hx | hx
  · simpa [e1PaddedAgeIndex, hx] using Nat.le_succ_of_le hx
  · subst x
    simp [e1PaddedAgeIndex]

/-- The actual finite L-age source for the E1 padded witness.
Only the neutral spacer is added; no real L-atom is changed. -/
noncomputable def e1PaddedSourceAge
    {db du dd : Nat}
    {n : Nat} (Q : PartialTypeWithE (n + 1) db du dd) :
    AgeTestModel db du dd :=
  ((Q.ageModel).sparsePullback (n + 3)
    (e1PaddedReal n) (e1PaddedAgeIndex n)).fillNeutralCarrier (n + 3)

/-- Exactly the required dense initial carrier. -/
theorem e1PaddedSourceAge_carrier
    {db du dd : Nat}
    {n : Nat} (Q : PartialTypeWithE (n + 1) db du dd)
    (x : Nat) :
    x ∈ (e1PaddedSourceAge Q).carrier ↔ x < n + 3 := by
  rfl

/-- The type L-age avoidance survives the neutral spacer. The only
forbidden witnesses being tested are L-structures, not invented E types. -/
theorem e1PaddedSourceAge_avoids
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids Q.ageModel) :
    ∀ bad, bad ∈ family →
      bad.Avoids (e1PaddedSourceAge Q) := by
  exact AgeTestModel.sparsePullback_fill_avoids
    family Q.ageModel (n + 3)
    (e1PaddedReal n) (e1PaddedAgeIndex n)
    (by
      intro x y hx hy hrealx hrealy hxy
      exact e1PaddedAgeIndex_strict n x y hxy hrealx hrealy)
    (by
      intro x hx hreal
      change e1PaddedAgeIndex n x ≤ n + 1
      exact e1PaddedAgeIndex_inside n x hreal)
    hAvoid

/-- The neutral spacer has no outgoing positive directed L edge. -/
theorem e1PaddedSourceAge_spacer_left
    {db du dd : Nat}
    {n : Nat} (Q : PartialTypeWithE (n + 1) db du dd)
    (x : Nat) (t : Fin db) :
    (e1PaddedSourceAge Q).binary (n + 1) x t = false := by
  let sparse := Q.ageModel.sparsePullback (n + 3)
    (e1PaddedReal n) (e1PaddedAgeIndex n)
  have hMissing : n + 1 ∉ sparse.carrier := by
    change ¬(n + 1 < n + 3 ∧ e1PaddedReal n (n + 1))
    simp only [e1PaddedReal]
    omega
  exact sparse.fillNeutralCarrier_binary_neutral_left
    (n + 3) (n + 1) x hMissing t

/-- Nor can a positive directed edge point into the neutral spacer. -/
theorem e1PaddedSourceAge_spacer_right
    {db du dd : Nat}
    {n : Nat} (Q : PartialTypeWithE (n + 1) db du dd)
    (x : Nat) (t : Fin db) :
    (e1PaddedSourceAge Q).binary x (n + 1) t = false := by
  let sparse := Q.ageModel.sparsePullback (n + 3)
    (e1PaddedReal n) (e1PaddedAgeIndex n)
  have hMissing : n + 1 ∉ sparse.carrier := by
    change ¬(n + 1 < n + 3 ∧ e1PaddedReal n (n + 1))
    simp only [e1PaddedReal]
    omega
  exact sparse.fillNeutralCarrier_binary_neutral_right
    (n + 3) x (n + 1) hMissing t

end SuccessorTree.V10

import SuccessorTree.V10.KptE1FreeCutRealization
import Mathlib.Tactic

/-!
# A genuine padded E profile for the concrete Kpt E1 pullback

The one-level pullback witness needs an actual finite partial structure:
source ordinary coordinates 0,...,n-1 keep their inherited E cuts;
the new ordinary coordinate n has the canonical parameter cut f<n (or 0);
coordinate n+1 is the neutral spacer, of cut zero; the final
distinguished-type witness n+2 has cut n+1.

The spacer is essential. Without it, E(n,n+1)=true would violate
SpacedE. These lemmas check the entire profile and construct a real
EnumeratedPartialStructure using the existing exact free-cut constructor.
The caller must still supply the actual finite L model and linked-pair
condition; neither can be invented from an L-only forbidden witness.
-/

namespace SuccessorTree.V10

/-- The precise finite E-column cut profile needed in the proposed E1
source witness. Beyond the actual carrier it is harmlessly zero. -/
def paddedE1FreeCutProfile
    (n : Nat) (oldCut : Nat → Nat) (f : Nat) (v : Nat) : Nat :=
  if v < n then oldCut v
  else if v = n then f
  else if v = n + 1 then 0
  else if v = n + 2 then n + 1
  else 0

/-- The old columns are untouched, not reinterpreted after spacing. -/
theorem paddedE1FreeCutProfile_old
    (n : Nat) (oldCut : Nat → Nat) (f v : Nat)
    (hv : v < n) :
    paddedE1FreeCutProfile n oldCut f v = oldCut v := by
  simp [paddedE1FreeCutProfile, hv]

/-- The new ordinary coordinate has precisely the source parameter cut. -/
theorem paddedE1FreeCutProfile_new
    (n : Nat) (oldCut : Nat → Nat) (f : Nat) :
    paddedE1FreeCutProfile n oldCut f n = f := by
  simp [paddedE1FreeCutProfile]

/-- The inserted neutral spacer has no E-predecessors. -/
theorem paddedE1FreeCutProfile_spacer
    (n : Nat) (oldCut : Nat → Nat) (f : Nat) :
    paddedE1FreeCutProfile n oldCut f (n + 1) = 0 := by
  unfold paddedE1FreeCutProfile
  split_ifs <;> omega

/-- The type witness has exactly n+1 old E-predecessors. -/
theorem paddedE1FreeCutProfile_type
    (n : Nat) (oldCut : Nat → Nat) (f : Nat) :
    paddedE1FreeCutProfile n oldCut f (n + 2) = n + 1 := by
  unfold paddedE1FreeCutProfile
  split_ifs <;> omega

/-- Actual spacing of all n+3 columns, including the last witness:
the neutral spacer separates it from the preceding ordinary vertex. -/
theorem paddedE1FreeCutProfile_spaced
    (n : Nat) (oldCut : Nat → Nat) (f : Nat)
    (hOld : ∀ v, v < n → oldCut v = 0 ∨ oldCut v < v)
    (hNew : f = 0 ∨ f < n) :
    ∀ v, v < n + 3 →
      paddedE1FreeCutProfile n oldCut f v = 0 ∨
      paddedE1FreeCutProfile n oldCut f v < v := by
  intro v hv
  unfold paddedE1FreeCutProfile
  split_ifs with hOldV hNewV hSpacer hLast
  · exact hOld v hOldV
  · subst v
    exact hNew
  · exact Or.inl rfl
  · exact Or.inr (by omega)
  · exact Or.inl rfl

/-- Build the ACTUAL finite Kpt-style E structure with a neutral spacer
from a pre-existing L-model. Forbidden-age avoidance is deliberately a
separate obligation on that L-model; linked L pairs are explicitly checked. -/
def paddedE1PartialStructure
    {db du dd : Nat}
    (n : Nat) (A : AgeTestModel db du dd)
    (hCarrier : ∀ v, v ∈ A.carrier ↔ v < n + 3)
    (oldCut : Nat → Nat) (f : Nat)
    (hOld : ∀ v, v < n → oldCut v = 0 ∨ oldCut v < v)
    (hNew : f = 0 ∨ f < n)
    (hLinked : ∀ u v, u < v → u < n + 3 → v < n + 3 →
      (∃ r : Fin db,
        A.binary u v r = true ∨ A.binary v u r = true) →
      u < paddedE1FreeCutProfile n oldCut f v) :
    EnumeratedPartialStructure db du dd :=
  EnumeratedPartialStructure.ofFreeCutProfile
    (n + 3) A hCarrier
    (paddedE1FreeCutProfile n oldCut f)
    (paddedE1FreeCutProfile_spaced n oldCut f hOld hNew)
    hLinked

/-- The L reduct is literally the supplied finite L age model. -/
theorem paddedE1PartialStructure_L
    {db du dd : Nat}
    (n : Nat) (A : AgeTestModel db du dd)
    (hCarrier : ∀ v, v ∈ A.carrier ↔ v < n + 3)
    (oldCut : Nat → Nat) (f : Nat)
    (hOld : ∀ v, v < n → oldCut v = 0 ∨ oldCut v < v)
    (hNew : f = 0 ∨ f < n)
    (hLinked : ∀ u v, u < v → u < n + 3 → v < n + 3 →
      (∃ r : Fin db,
        A.binary u v r = true ∨ A.binary v u r = true) →
      u < paddedE1FreeCutProfile n oldCut f v) :
    (paddedE1PartialStructure n A hCarrier oldCut f
      hOld hNew hLinked).L = A := rfl

/-- The ACTUAL canonical free level of each column is its prescribed
profile cut, rather than a merely isomorphic E-column boundary. -/
theorem paddedE1PartialStructure_freeLevel
    {db du dd : Nat}
    (n : Nat) (A : AgeTestModel db du dd)
    (hCarrier : ∀ v, v ∈ A.carrier ↔ v < n + 3)
    (oldCut : Nat → Nat) (f : Nat)
    (hOld : ∀ v, v < n → oldCut v = 0 ∨ oldCut v < v)
    (hNew : f = 0 ∨ f < n)
    (hLinked : ∀ u v, u < v → u < n + 3 → v < n + 3 →
      (∃ r : Fin db,
        A.binary u v r = true ∨ A.binary v u r = true) →
      u < paddedE1FreeCutProfile n oldCut f v)
    (v : Nat) (hv : v < n + 3) :
    (paddedE1PartialStructure n A hCarrier oldCut f
      hOld hNew hLinked).freeLevel v =
      paddedE1FreeCutProfile n oldCut f v := by
  exact finiteFreeCutE_canonicalFreeLevel
    (n + 3) (paddedE1FreeCutProfile n oldCut f)
    (paddedE1FreeCutProfile_spaced n oldCut f hOld hNew)
    v hv

/-- The final type witness really has free level n+1. -/
theorem paddedE1PartialStructure_type_freeLevel
    {db du dd : Nat}
    (n : Nat) (A : AgeTestModel db du dd)
    (hCarrier : ∀ v, v ∈ A.carrier ↔ v < n + 3)
    (oldCut : Nat → Nat) (f : Nat)
    (hOld : ∀ v, v < n → oldCut v = 0 ∨ oldCut v < v)
    (hNew : f = 0 ∨ f < n)
    (hLinked : ∀ u v, u < v → u < n + 3 → v < n + 3 →
      (∃ r : Fin db,
        A.binary u v r = true ∨ A.binary v u r = true) →
      u < paddedE1FreeCutProfile n oldCut f v) :
    (paddedE1PartialStructure n A hCarrier oldCut f
      hOld hNew hLinked).freeLevel (n + 2) = n + 1 := by
  rw [paddedE1PartialStructure_freeLevel n A hCarrier oldCut f
    hOld hNew hLinked (n + 2) (by omega)]
  exact paddedE1FreeCutProfile_type n oldCut f

end SuccessorTree.V10

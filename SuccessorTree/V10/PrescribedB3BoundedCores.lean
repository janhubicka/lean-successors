import SuccessorTree.V10.PrescribedCorrectedB3
import Mathlib.Tactic

/-!
# A bounded-upper-core version of the finite B3 age test

The repaired B3 is a property of arbitrary finite ordered L-age
witnesses. It remains difficult to derive from a shape-preserving map
because several upper witnesses may have incompatible E-socles.

The following EXACT equivalence makes the unavoidable finite part
explicit. If a forbidden irreducible copy uses the inserted coordinate
ell, every upper vertex relevant to that copy belongs to a set of at
most r addresses, where r is its forbidden arity. The age test can
therefore be checked on restrictions to the initial socle together
with at most B upper addresses, where B is the maximum arity in the
finite forbidden family.

This is only a reduction of the strengthened B3 age assumption; it
does not assert its necessity for M2 or construct the missing one-gap
map. It introduces no E-lift assumption on arbitrary L-witnesses.
-/

namespace SuccessorTree.V10

/-- Number of vertices in a normalized forbidden configuration. -/
def NormalizedForbidden.arity
    {db du dd : Nat} : NormalizedForbidden db du dd → Nat
  | .singleton _ _ => 1
  | .nontrivial r _ _ _ => r

/-- Explicit uniform arity bound for a finite forbidden family. -/
def forbiddenFamilyArityBound
    {db du dd : Nat} : List (NormalizedForbidden db du dd) → Nat
  | [] => 0
  | h :: tail => max h.arity (forbiddenFamilyArityBound tail)

/-- The maximum really bounds the arity of EVERY member, including
forbidden singleton configurations. -/
theorem normalizedForbidden_arity_le_family_bound
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (bad : NormalizedForbidden db du dd)
    (hMem : bad ∈ family) :
    bad.arity ≤ forbiddenFamilyArityBound family := by
  induction family with
  | nil =>
      simp at hMem
  | cons first rest ih =>
      rcases List.mem_cons.mp hMem with hEq | hTail
      · subst first
        exact Nat.le_max_left _ _
      · exact (ih hTail).trans (Nat.le_max_right _ _)

/-- Avoidance of an induced forbidden pattern is inherited by ANY
restriction of the vertex carrier; all atomic L facts stay fixed. -/
theorem NormalizedForbidden.avoids_restrictCarrier
    {db du dd : Nat}
    (bad : NormalizedForbidden db du dd)
    (W : AgeTestModel db du dd) (P : Nat → Prop)
    (hAvoid : bad.Avoids W) :
    bad.Avoids (W.restrictCarrier P) := by
  cases bad with
  | singleton A hNeutral =>
      rintro ⟨e,he⟩
      exact hAvoid ⟨e,
        AgeTestModel.realizes_of_restrictCarrier W P A e he⟩
  | nontrivial r A hr hIrred =>
      rintro ⟨e,he⟩
      exact hAvoid ⟨e,
        AgeTestModel.realizes_of_restrictCarrier W P A e he⟩

/-- B3 tested on initial-socle cores with a uniformly bounded set of
upper vertices. The labels e need not be injective: restricting to
finitely many upper addresses suffices for the equivalence.

The conditions on W are the same four clauses as CommonSocleAgeTest;
only its forbidden-age conclusion has been localized. -/
def BoundedUpperCoreAgeTest
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (D : AgeTestModel db du dd)
    (ell : Nat)
    (Prescribed : RelationalPrefixType (ell + 1) db du dd → Prop) : Prop :=
  ∀ W : AgeTestModel db du dd,
    W.BoundedCarrier →
    SameInitialL W D ell →
    UpperTypesPrescribed W ell Prescribed →
    (∀ bad, bad ∈ family → bad.Avoids (W.withoutVertex ell)) →
    ∀ r : Nat, r ≤ forbiddenFamilyArityBound family →
      ∀ e : Fin r → Nat, ∀ bad, bad ∈ family →
        bad.Avoids (W.restrictCarrier
          (forbiddenWitnessCarrier ell e))

/-- The bounded-core age test is exactly equivalent to the full finite
common-socle B3 test. In the nontrivial direction any forbidden copy e
lies in its own initial-socle-plus-e image core; the forward direction
is heredity of induced forbidden avoidance.

In particular this DOES NOT weaken the age hypothesis of the
currently formalized prescribed insertion: it just identifies
precisely how many simultaneous upper types need consideration. -/
theorem boundedUpperCoreAgeTest_iff_commonSocleAgeTest
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (D : AgeTestModel db du dd) (ell : Nat)
    (Prescribed : RelationalPrefixType (ell + 1) db du dd → Prop) :
    BoundedUpperCoreAgeTest family D ell Prescribed ↔
      CommonSocleAgeTest family D ell Prescribed := by
  constructor
  · intro hCore W hFinite hSame hUpper hDelete bad hBad
    cases bad with
    | singleton A hNeutral =>
        intro hCopy
        obtain ⟨e,he⟩ := hCopy
        have hSize : 1 ≤ forbiddenFamilyArityBound family :=
          normalizedForbidden_arity_le_family_bound
            family (.singleton A hNeutral) hBad
        have hAvoidCore :=
          hCore W hFinite hSame hUpper hDelete 1 hSize
            e (.singleton A hNeutral) hBad
        apply hAvoidCore
        refine ⟨e, ?_⟩
        apply AgeTestModel.realizes_restrictCarrier W
          (forbiddenWitnessCarrier ell e) A e he
        intro a
        by_cases hLow : e a ≤ ell
        · exact Or.inl hLow
        · exact Or.inr ⟨a,rfl,by omega⟩
    | nontrivial r A hr hIrred =>
        intro hCopy
        obtain ⟨e,he⟩ := hCopy
        have hSize : r ≤ forbiddenFamilyArityBound family :=
          normalizedForbidden_arity_le_family_bound
            family (.nontrivial r A hr hIrred) hBad
        have hAvoidCore :=
          hCore W hFinite hSame hUpper hDelete r hSize
            e (.nontrivial r A hr hIrred) hBad
        apply hAvoidCore
        refine ⟨e, ?_⟩
        apply AgeTestModel.realizes_restrictCarrier W
          (forbiddenWitnessCarrier ell e) A e he
        intro a
        by_cases hLow : e a ≤ ell
        · exact Or.inl hLow
        · exact Or.inr ⟨a,rfl,by omega⟩
  · intro hAge W hFinite hSame hUpper hDelete
      r hR e bad hBad
    exact bad.avoids_restrictCarrier W
      (forbiddenWitnessCarrier ell e)
      (hAge W hFinite hSame hUpper hDelete bad hBad)

end SuccessorTree.V10

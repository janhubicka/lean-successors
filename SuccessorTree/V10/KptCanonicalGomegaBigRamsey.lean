import SuccessorTree.V10.KptOriginalBinaryUnaryBigRamsey
import Mathlib.Tactic

/-!
# Canonical countable Gω exists for every normalized forbidden family

An arbitrary normalized forbidden family explicitly excludes the
neutral singleton and every nontrivial forbidden pattern is
irreducible. Therefore the countable all-false L structure is
forbidden-free: non-neutral singleton patterns cannot occur and
irreducible patterns on at least two vertices require an actual
positive directed edge.

Give this structure the all-false auxiliary E relation. It is a
genuine countable enumerated partial structure satisfying spacing,
downward closure and linkage, so it witnesses every nonempty finite
G+ size layer.

This removes the final external countable C+ witness from the
normalized self-big-Ramsey theorem: a canonical exhaustive
size-respecting Gω and its finite big Ramsey degree are constructed
solely from the finite forbidden family. No neutral extension,
unproved amalgamation or arbitrarily chosen E expansion is assumed.

The normalized big Ramsey theorem covers all finite tuple sizes,
including zero; the separate finite original unary/binary copy
predicate has already been checked against the actual diagonal and
directed records.
-/

namespace SuccessorTree.V10

/-- The countable completely neutral L structure. -/
def allFalseAgeModel (db du dd : Nat) : AgeTestModel db du dd where
  carrier := Set.univ
  binary := fun _ _ _ => false
  unary := fun _ _ => false
  diagonal := fun _ _ => false

/-- Every normalized forbidden family is avoided by the infinite
all-false L structure. This is precisely where the definition
'NormalizedForbidden' (forbidden non-neutral singletons and
irreducible patterns) is used; no other age closure is postulated. -/
theorem allFalseAgeModel_avoids_family
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    ∀ bad, bad ∈ family →
      bad.Avoids (allFalseAgeModel db du dd) := by
  intro bad _hBad
  cases bad with
  | singleton F hNonNeutral =>
      rintro ⟨f,hCopy⟩
      rcases hNonNeutral with ⟨t,ht⟩ | ⟨t,ht⟩
      · have hh := hCopy.2.2.2.1 0 t
        simp [allFalseAgeModel,ht] at hh
      · have hh := hCopy.2.2.2.2 0 t
        simp [allFalseAgeModel,ht] at hh
  | nontrivial n F hn hIrred =>
      rintro ⟨f,hCopy⟩
      let a : Fin n := ⟨0,by omega⟩
      let b : Fin n := ⟨1,by omega⟩
      have hab : a ≠ b := by
        intro h
        have hval := congrArg Fin.val h
        norm_num [a,b] at hval
      obtain ⟨t,ht⟩ := hIrred a b hab
      rcases ht with hFwd | hRev
      · have hh := hCopy.2.2.1 a b hab t
        simp [allFalseAgeModel,hFwd] at hh
      · have hh := hCopy.2.2.1 b a hab.symm t
        simp [allFalseAgeModel,hRev] at hh

/-- The all-false E relation provides a genuine countable L+ partial
structure, not an E-assignment to a forbidden-age witness. -/
def allFalseCountablePartialStructure (db du dd : Nat) :
    CountableEnumeratedPartialStructure db du dd where
  L := allFalseAgeModel db du dd
  fullCarrier := by intro _; trivial
  E := fun _ _ => false
  spaced := by
    intro u v h
    simp at h
  downward := by
    intro u v h w hw
    simp at h
  linked_E := by
    intro u v huv hLink
    rcases hLink with ⟨t,ht | ht⟩
    · simp [allFalseAgeModel] at ht
    · simp [allFalseAgeModel] at ht

/-- Concrete single fixed Gω for the forbidden family: no caller
chooses a countable C+ to witness nonempty layers. -/
noncomputable def canonicalNormalizedGOmegaEnumeration
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    Nat ≃ FiniteGPlusVertex family :=
  GPlusEnumeration.enumerate
    (allFalseCountablePartialStructure db du dd) family
    (allFalseAgeModel_avoids_family family)

/-- Full normalized Gω self big Ramsey theorem with no source
existence/age-witness assumption. The original finite palette b(q)
is explicit and depends only on q and the normalized forbidden
family, never on the colouring. -/
theorem canonicalNormalizedGOmega_bigRamsey
    {db du dd : Nat}
    {κ : Type*} [Fintype κ]
    (family : List (NormalizedForbidden db du dd))
    (q : Nat) (χ : (Fin q → Nat) → κ) :
    let G := finiteGPlusEnumeratedL
      (canonicalNormalizedGOmegaEnumeration family)
    ∃ (e : G.InducedEmbedding G)
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family
          (numericHTopUniformPaletteHeight family
            (normalizedKptGeneration family) q) q) ∧
      ∀ indices : Fin q → Nat,
        χ (fun i => e.toFun (indices i)) ∈ colours := by
  exact normalizedKpt_GOmega_self_bigRamsey_bound
    family (allFalseCountablePartialStructure db du dd)
    (allFalseAgeModel_avoids_family family) q χ

/-- The canonical Gω is forbidden-free in its literal L-reduct,
with ALL negative unary/diagonal and directed binary atoms included
in the induced tests. -/
theorem canonicalNormalizedGOmega_avoids_family
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    ∀ bad, bad ∈ family → bad.Avoids
      (finiteGPlusEnumeratedL
        (canonicalNormalizedGOmegaEnumeration family)) :=
  GPlusEnumeration.enumeratedL_avoids_family
    (allFalseCountablePartialStructure db du dd) family
    (allFalseAgeModel_avoids_family family)

end SuccessorTree.V10

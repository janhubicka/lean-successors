import SuccessorTree.V10.I3SignatureCardinality
import Mathlib.Tactic

/-!
# Proposition 6.44: count I3 signatures using higher-generation names ONLY

A fixed full original pool can represent the whole current closure,
but it is too large for the manuscript's inductive bound R(M_r).
Lemma 6.53 gives a stronger conclusion: each NONBOTTOM name in
the signature of a level of generation r is an actual original of
generation STRICTLY GREATER THAN r.

Therefore choose a finite enumeration of those higher-generation
names, and RELABEL the upper witnesses through that enumeration.
The existing exact signature collision theorem now bounds the
number of I3 levels by R(H), where H is the number of higher names,
and hence by R(M_r) whenever H<=M_r.

This file proves the relabelling and cardinal algebra, not the
remaining geometric lemma asserting that each actual selected
stage has a witness with higher-generation names.  That lemma
must use the checked selected-stage Lemma 6.53 and the concrete
Algorithm 5.4 closure.
-/

namespace SuccessorTree.V10

/-- If every upper vertex of a genuine original-labelled I3
witness can be named in a FIXED smaller original pool, the same
induced copy, finite age witness and deletion certificate form
a valid I3 signature witness for the smaller pool.  No
hypothetical extra E on W is introduced. -/
noncomputable def I3OriginalSignatureWitness.relabelOriginals
    {k M H db du dd : Nat}
    {sizes : Fin k → Nat}
    {patterns : (i : Fin k) → ForbiddenAtomicPattern (sizes i) db du dd}
    {C : AgeTestModel db du dd}
    {original : Fin M → Nat}
    {ell : Nat}
    (w : I3OriginalSignatureWitness sizes patterns C original ell)
    (higher : Fin H → Fin M)
    (hUpper : ∀ a : Fin (sizes w.familyIndex), ell < w.e a →
      ∃ j : Fin H,
        RelationalPrefixType.ofAgeModel w.W (ell+1) (w.e a) =
          RelationalPrefixType.ofAgeModel C (ell+1)
            (original (higher j))) :
    I3OriginalSignatureWitness sizes patterns C
      (fun j : Fin H => original (higher j)) ell where
  familyIndex := w.familyIndex
  W := w.W
  e := w.e
  finite := w.finite
  copy := w.copy
  socle := w.socle
  deleteAvoids := w.deleteAvoids
  upperNames := hUpper

/-- Restrict names using any property, e.g. generation >r:
if all actually used upper labels satisfy that property and
every such label has a name in the higher pool, then the
underlying witness can be reindexed without changing L-atoms
or the forbidden pattern. -/
noncomputable def I3OriginalSignatureWitness.relabelHigherOriginals
    {k M H db du dd : Nat}
    {sizes : Fin k → Nat}
    {patterns : (i : Fin k) → ForbiddenAtomicPattern (sizes i) db du dd}
    {C : AgeTestModel db du dd}
    {original : Fin M → Nat}
    {ell : Nat}
    (w : I3OriginalSignatureWitness sizes patterns C original ell)
    (isHigher : Fin M → Prop)
    (higher : Fin H → Fin M)
    (hCover : ∀ v : Fin M, isHigher v → ∃ j : Fin H, higher j = v)
    (hWitnessHigher : ∀ a : Fin (sizes w.familyIndex), ell < w.e a →
      ∃ v : Fin M, isHigher v ∧
        RelationalPrefixType.ofAgeModel w.W (ell+1) (w.e a) =
          RelationalPrefixType.ofAgeModel C (ell+1) (original v)) :
    I3OriginalSignatureWitness sizes patterns C
      (fun j : Fin H => original (higher j)) ell := by
  apply w.relabelOriginals higher
  intro a ha
  obtain ⟨v,hHigher,hType⟩ := hWitnessHigher a ha
  obtain ⟨j,hj⟩ := hCover v hHigher
  refine ⟨j,?_⟩
  simpa [hj] using hType

/-- Sharp I3 level signature bound by R(H), where H counts
ONLY originals satisfying the designated higher-generation
predicate. Full closure originals need not themselves be high:
it is the upper names ACTUALLY USED in the forbidden witnesses
that are constrained. -/
theorem i3SelectedLevels_card_le_higherOriginalCapacity
    {k M H db du dd : Nat}
    (sizes : Fin k → Nat)
    (patterns : (i : Fin k) → ForbiddenAtomicPattern (sizes i) db du dd)
    (C : AgeTestModel db du dd)
    (original : Fin M → Nat)
    (isHigher : Fin M → Prop)
    (higher : Fin H → Fin M)
    (hCover : ∀ v, isHigher v → ∃ j : Fin H, higher j = v)
    (levels : Finset Nat)
    (hInitial : ∀ ell, ell ∈ levels →
      ∀ x, x ≤ ell → x ∈ C.carrier)
    (hWitness : ∀ ell, ell ∈ levels →
      ∃ w : I3OriginalSignatureWitness sizes patterns C original ell,
        ∀ a : Fin (sizes w.familyIndex), ell < w.e a →
          ∃ v : Fin M, isHigher v ∧
            RelationalPrefixType.ofAgeModel w.W (ell+1) (w.e a) =
              RelationalPrefixType.ofAgeModel C (ell+1) (original v)) :
    levels.card ≤ ageSignatureCapacity sizes H := by
  classical
  have hReindexed : ∀ ell, ell ∈ levels →
      Nonempty (I3OriginalSignatureWitness sizes patterns C
        (fun j : Fin H => original (higher j)) ell) := by
    intro ell hEll
    obtain ⟨w,hHigher⟩ := hWitness ell hEll
    exact ⟨w.relabelHigherOriginals isHigher higher hCover hHigher⟩
  exact i3SelectedLevels_card_le_signature_capacity
    sizes patterns C (fun j : Fin H => original (higher j))
    levels hInitial hReindexed

/-- The exact manuscript recurrence input: once the number H of
higher-generation names is bounded by M_r, the number of I3
levels at generation r is bounded by R(M_r). -/
theorem i3SelectedLevels_card_le_higherGenerationBudget
    {k M H db du dd : Nat}
    (sizes : Fin k → Nat)
    (patterns : (i : Fin k) → ForbiddenAtomicPattern (sizes i) db du dd)
    (C : AgeTestModel db du dd)
    (original : Fin M → Nat)
    (isHigher : Fin M → Prop)
    (higher : Fin H → Fin M)
    (hCover : ∀ v, isHigher v → ∃ j : Fin H, higher j = v)
    (levels : Finset Nat)
    (hInitial : ∀ ell, ell ∈ levels →
      ∀ x, x ≤ ell → x ∈ C.carrier)
    (hWitness : ∀ ell, ell ∈ levels →
      ∃ w : I3OriginalSignatureWitness sizes patterns C original ell,
        ∀ a : Fin (sizes w.familyIndex), ell < w.e a →
          ∃ v : Fin M, isHigher v ∧
            RelationalPrefixType.ofAgeModel w.W (ell+1) (w.e a) =
              RelationalPrefixType.ofAgeModel C (ell+1) (original v))
    (Mr : Nat) (hHighCount : H ≤ Mr) :
    levels.card ≤ ageSignatureCapacity sizes Mr := by
  calc
    levels.card ≤ ageSignatureCapacity sizes H :=
      i3SelectedLevels_card_le_higherOriginalCapacity
        sizes patterns C original isHigher higher hCover
        levels hInitial hWitness
    _ ≤ ageSignatureCapacity sizes Mr :=
      (ageSignatureCapacity_mono sizes) hHighCount

end SuccessorTree.V10

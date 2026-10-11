import SuccessorTree.V10.M3MiddleLinkedData
import Mathlib.Tactic

/-!
# The genuine gated M3 middle clone introduces no forbidden L-copy

Every forbidden copy avoiding the new coordinate projects to the old
finite structure by the old-atom L insertion interface. Every
irreducible forbidden copy involving the new coordinate projects to
the original preceding clone n by the linked-only finite clone lemma,
and therefore also avoids the inserted coordinate.

This theorem is for the actual finite L+ partial-structure constructor
at n<ell, not for hypothetical clone atoms on an E-witness. It
permits arbitrary normalized forbidden irreducible patterns,
including nonneutral forbidden singleton patterns.
-/

namespace SuccessorTree.V10

/-- Deleting the newly inserted M3 coordinate from its L-reduct
leaves a forbidden-free L-model whenever the old A was forbidden-free.
No irreducibility is needed for this away-from-ell implication. -/
theorem middleCloneInsertPartial_without_avoids
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    ∀ bad, bad ∈ family →
      bad.Avoids
        ((middleCloneInsertPartial A ell n hell hn).L.withoutVertex ell) := by
  let B := middleCloneInsertPartial A ell n hell hn
  have hIns : IsLInsertion A B ell :=
    middleCloneInsertPartial_isLInsertion A ell n hell hn
  intro bad hb
  cases bad with
  | singleton P hN =>
      rintro ⟨f,hCopy⟩
      have hB : B.L.Realizes P f :=
        AgeTestModel.realizes_of_restrictCarrier B.L
          (fun x => x ≠ ell) P f hCopy
      have hAway : ∀ a, f a ≠ ell := by
        intro a
        exact (hCopy.2.1 a).2
      exact (hAvoid (.singleton P hN) hb)
        ⟨_, hIns.realizes_away_projects P f hB hAway⟩
  | nontrivial r P hr hIrred =>
      rintro ⟨f,hCopy⟩
      have hB : B.L.Realizes P f :=
        AgeTestModel.realizes_of_restrictCarrier B.L
          (fun x => x ≠ ell) P f hCopy
      have hAway : ∀ a, f a ≠ ell := by
        intro a
        exact (hCopy.2.1 a).2
      exact (hAvoid (.nontrivial r P hr hIrred) hb)
        ⟨_,hIns.realizes_away_projects P f hB hAway⟩

/-- Every inserted middle clone has the same normalized forbidden
ordered L-age as its old source, including all present and absent
directed relations and arbitrary normalized forbidden singletons. -/
theorem middleCloneInsertPartial_preserves_avoidance
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    ∀ bad, bad ∈ family →
      bad.Avoids (middleCloneInsertPartial A ell n hell hn).L := by
  let B := middleCloneInsertPartial A ell n hell hn
  have hData : MiddleCloneLinkedLData B.L n ell (A.freeLevel n) :=
    middleCloneInsertPartial_linkedLData A ell n hell hn
  have hDel :
      ∀ bad, bad ∈ family → bad.Avoids (B.L.withoutVertex ell) :=
    middleCloneInsertPartial_without_avoids family A ell n hell hn hAvoid
  exact hData.avoidance_of_deletion family hDel

end SuccessorTree.V10

import SuccessorTree.V10.LocalAgeFreeCut
import Mathlib.Tactic

/-!
# Neutral insertion when the old socle does not match the prescribed one

In Lemma 6.51 the new vertex receives the allowed empty singleton type
and no L-relations whenever the old lower socle does not match D.
We construct this branch as an actual finite partial structure, including
its transported E columns, and show that it remains forbidden-free
WITHOUT invoking the local three-clause age test.

This is one of the two cases in the uniform insertion needed for the
global level-skipping ShapeMap. The matching-socle case is handled by
LocalAgeForbiddenTest, conditional on the prescribed crossing.
-/

namespace SuccessorTree.V10

/-- Empty L singleton and no directed links to any old vertex. -/
def neutralInsertedLData (db du dd : Nat) : InsertedLData db du dd where
  loop := fun _ => false
  unary := fun _ => false
  diagonal := fun _ => false
  incoming := fun _ _ => false
  outgoing := fun _ _ => false

private theorem neutral_insert_below
    (db du dd ell : Nat) :
    ∀ x, x < ell →
      (∃ r : Fin db,
        (neutralInsertedLData db du dd).incoming x r = true ∨
        (neutralInsertedLData db du dd).outgoing x r = true) →
      x < 0 := by
  intro x hx h
  simp [neutralInsertedLData] at h

private theorem neutral_insert_above
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) :
    ∀ y, ell ≤ y → y < A.size →
      (∃ r : Fin db,
        (neutralInsertedLData db du dd).outgoing y r = true ∨
        (neutralInsertedLData db du dd).incoming y r = true) →
      ell ≤ A.freeLevel y := by
  intro y hy hsize h
  simp [neutralInsertedLData] at h

/-- Neutral one-coordinate insertion is a genuine partial structure.
The positive-level condition is inherited from Lemma 6.51. -/
noncomputable def neutralInsert
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell) :
    EnumeratedPartialStructure db du dd :=
  insertPartial A ell 0 (neutralInsertedLData db du dd)
    hell hellPos (Nat.zero_le ell) (Or.inl rfl)
    (neutral_insert_below db du dd ell)
    (neutral_insert_above A ell)

/-- Every off-diagonal link involving the inserted neutral vertex is absent,
in both directed orientations. The loop atom is absent too. -/
@[simp] theorem neutralInsert_binary_from_inserted
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (x : Nat) (t : Fin db) :
    (neutralInsert A ell hell hellPos).L.binary ell x t = false := by
  by_cases hx : x = ell
  · simp [neutralInsert, insertPartial, insertL, neutralInsertedLData, hx]
  · simp [neutralInsert, insertPartial, insertL, neutralInsertedLData, hx]

@[simp] theorem neutralInsert_binary_to_inserted
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (x : Nat) (t : Fin db) :
    (neutralInsert A ell hell hellPos).L.binary x ell t = false := by
  by_cases hx : x = ell
  · simp [neutralInsert, insertPartial, insertL, neutralInsertedLData, hx]
  · simp [neutralInsert, insertPartial, insertL, neutralInsertedLData, hx]

@[simp] theorem neutralInsert_unary_inserted
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (t : Fin du) :
    (neutralInsert A ell hell hellPos).L.unary ell t = false := by
  simp [neutralInsert, insertPartial, insertL, neutralInsertedLData]

@[simp] theorem neutralInsert_diagonal_inserted
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (t : Fin dd) :
    (neutralInsert A ell hell hellPos).L.diagonal ell t = false := by
  simp [neutralInsert, insertPartial, insertL, neutralInsertedLData]

/-- The neutral inserted L structure contains all the old ordered atoms
exactly, including negative facts. -/
theorem neutralInsert_isLInsertion
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell) :
    IsLInsertion A (neutralInsert A ell hell hellPos) ell := by
  exact insertPartial_isLInsertion A ell 0
    (neutralInsertedLData db du dd)
    hell hellPos (Nat.zero_le ell) (Or.inl rfl)
    (neutral_insert_below db du dd ell)
    (neutral_insert_above A ell)

/-- A non-neutral forbidden singleton cannot be realized at the freshly
inserted neutral vertex. -/
theorem neutralInsert_forbidden_singleton_not_at_inserted
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (F : ForbiddenAtomicPattern 1 db du dd)
    (hNonNeutral : F.NonNeutralSingleton) :
    ¬ (neutralInsert A ell hell hellPos).L.Realizes F (fun _ => ell) := by
  intro hCopy
  rcases hNonNeutral with ⟨t, ht⟩ | ⟨t, ht⟩
  · have h := hCopy.2.2.2.1 0 t
    rw [neutralInsert_unary_inserted, ht] at h
    contradiction
  · have h := hCopy.2.2.2.2 0 t
    rw [neutralInsert_diagonal_inserted, ht] at h
    contradiction

/-- An irreducible forbidden copy of size at least two cannot contain
the inserted neutral vertex: irreducibility would demand one directed
edge from it to a different copy vertex. -/
theorem neutralInsert_irreducible_copy_avoids_inserted
    {r db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (F : ForbiddenAtomicPattern r db du dd)
    (hr : 1 < r) (hIrred : F.Irreducible)
    (f : Fin r → Nat)
    (hCopy : (neutralInsert A ell hell hellPos).L.Realizes F f) :
    ∀ a, f a ≠ ell := by
  intro a ha
  let z : Fin r := ⟨0, by omega⟩
  let o : Fin r := ⟨1, hr⟩
  have hzo : z ≠ o := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [z, o] at hv
  obtain ⟨b, hab⟩ : ∃ b : Fin r, a ≠ b := by
    by_cases haz : a = z
    · refine ⟨o, ?_⟩
      simpa [haz] using hzo
    · exact ⟨z, haz⟩
  obtain ⟨t, ht⟩ := hIrred a b hab
  have hForward := hCopy.2.2.1 a b hab t
  have hReverse := hCopy.2.2.1 b a hab.symm t
  rw [ha, neutralInsert_binary_from_inserted] at hForward
  rw [ha, neutralInsert_binary_to_inserted] at hReverse
  rcases ht with ht | ht
  · rw [ht] at hForward
    contradiction
  · rw [ht] at hReverse
    contradiction

/-- The neutral branch is forbidden-free for every normalized family,
without any B3 age-test assumption. -/
theorem neutralInsert_preserves_avoidance
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    ∀ bad, bad ∈ family →
      bad.Avoids (neutralInsert A ell hell hellPos).L := by
  have hIns := neutralInsert_isLInsertion A ell hell hellPos
  intro bad hbad
  cases bad with
  | singleton F hNonNeutral =>
      rintro ⟨f, hf⟩
      by_cases hAt : f 0 = ell
      · have hfEq : f = fun _ => ell := by
          funext a
          have ha : a = 0 := Subsingleton.elim _ _
          simpa [ha] using hAt
        exact (neutralInsert_forbidden_singleton_not_at_inserted
          A ell hell hellPos F hNonNeutral) (by simpa [hfEq] using hf)
      · have hAway : ∀ a : Fin 1, f a ≠ ell := by
          intro a
          have ha : a = 0 := Subsingleton.elim _ _
          simpa [ha] using hAt
        exact (hAvoid (.singleton F hNonNeutral) hbad)
          ⟨_, hIns.realizes_away_projects F f hf hAway⟩
  | nontrivial r F hr hIrred =>
      rintro ⟨f, hf⟩
      have hAway :=
        neutralInsert_irreducible_copy_avoids_inserted A ell hell hellPos
          F hr hIrred f hf
      exact (hAvoid (.nontrivial r F hr hIrred) hbad)
        ⟨_, hIns.realizes_away_projects F f hf hAway⟩

end SuccessorTree.V10

import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# The elementary non-edge amalgamation age lemma for M2

When two vertices a and b are not L-linked in either direction,
a forbidden nontrivial irreducible copy cannot contain both.
Consequently forbidden avoidance of the two restrictions deleting a
and b already implies forbidden avoidance of the whole structure.

The singleton case is included: a one-vertex copy cannot contain
both different distinguished vertices. This is the L-only argument
underlying the simultaneous source witnesses used for M2/B2, and
requires no E expansion of an arbitrary finite target L model.
-/

namespace SuccessorTree.V10

/-- Any induced copy avoiding a selected vertex remains an induced
copy after removing that vertex from the age model's carrier. -/
theorem AgeTestModel.realizes_withoutVertex
    {r db du dd : Nat}
    (W : AgeTestModel db du dd)
    (a : Nat) (P : ForbiddenAtomicPattern r db du dd)
    (e : Fin r → Nat) (hCopy : W.Realizes P e)
    (hAway : ∀ i, e i ≠ a) :
    (W.withoutVertex a).Realizes P e :=
  W.realizes_restrictCarrier (fun x => x ≠ a) P e hCopy hAway

/-- For an irreducible forbidden pattern, no copy can use both
vertices of a pair whose two directed L links are absent. -/
theorem ForbiddenAtomicPattern.no_copy_uses_nonedge_pair
    {r db du dd : Nat}
    (P : ForbiddenAtomicPattern r db du dd)
    (hIrred : P.Irreducible)
    (W : AgeTestModel db du dd)
    (a b : Nat) (hab : a ≠ b)
    (hNonedge : ∀ t : Fin db,
      W.binary a b t = false ∧ W.binary b a t = false)
    (e : Fin r → Nat) (hCopy : W.Realizes P e) :
    ¬ (∃ i, e i = a) ∨ ¬ (∃ j, e j = b) := by
  by_contra hBad
  push_neg at hBad
  obtain ⟨i,hi⟩ := hBad.1
  obtain ⟨j,hj⟩ := hBad.2
  have hij : i ≠ j := by
    intro h
    apply hab
    calc
      a = e i := hi.symm
      _ = e j := congrArg e h
      _ = b := hj
  obtain ⟨t,ht | ht⟩ := hIrred i j hij
  · have h := hCopy.2.2.1 i j hij t
    have hTrue : W.binary a b t = true := by
      calc
        W.binary a b t = P.binary i j t := by
          simpa only [hi,hj] using h
        _ = true := ht
    have hFalse := (hNonedge t).1
    exact Bool.false_ne_true (hFalse.symm.trans hTrue)
  · have h := hCopy.2.2.1 j i hij.symm t
    have hTrue : W.binary b a t = true := by
      calc
        W.binary b a t = P.binary j i t := by
          simpa only [hj,hi] using h
        _ = true := ht
    have hFalse := (hNonedge t).2
    exact Bool.false_ne_true (hFalse.symm.trans hTrue)

/-- The exact non-edge amalgamation property of normalized
forbidden-free L ages: if both one-vertex-deleted restrictions
avoid a forbidden pattern, then their free non-edge union does too. -/
theorem NormalizedForbidden.avoids_of_nonedge_pair
    {db du dd : Nat}
    (bad : NormalizedForbidden db du dd)
    (W : AgeTestModel db du dd)
    (a b : Nat) (hab : a ≠ b)
    (hNonedge : ∀ t : Fin db,
      W.binary a b t = false ∧ W.binary b a t = false)
    (hAvoidA : bad.Avoids (W.withoutVertex a))
    (hAvoidB : bad.Avoids (W.withoutVertex b)) :
    bad.Avoids W := by
  cases bad with
  | singleton P hNeutral =>
      rintro ⟨e,hCopy⟩
      by_cases hA : e 0 = a
      · have hAway : ∀ i : Fin 1, e i ≠ b := by
          intro i
          have hi : i = 0 := Subsingleton.elim _ _
          subst i
          intro hB
          exact hab (hA.symm.trans hB)
        exact hAvoidB ⟨e,W.realizes_withoutVertex b P e hCopy hAway⟩
      · have hAway : ∀ i : Fin 1, e i ≠ a := by
          intro i
          have hi : i = 0 := Subsingleton.elim _ _
          subst i
          exact hA
        exact hAvoidA ⟨e,W.realizes_withoutVertex a P e hCopy hAway⟩
  | nontrivial r P hr hIrred =>
      rintro ⟨e,hCopy⟩
      rcases P.no_copy_uses_nonedge_pair hIrred W a b hab
        hNonedge e hCopy with hAwayA | hAwayB
      · have hAway : ∀ i, e i ≠ a := by
          intro i hi
          exact hAwayA ⟨i,hi⟩
        exact hAvoidA ⟨e,W.realizes_withoutVertex a P e hCopy hAway⟩
      · have hAway : ∀ i, e i ≠ b := by
          intro i hi
          exact hAwayB ⟨i,hi⟩
        exact hAvoidB ⟨e,W.realizes_withoutVertex b P e hCopy hAway⟩

end SuccessorTree.V10

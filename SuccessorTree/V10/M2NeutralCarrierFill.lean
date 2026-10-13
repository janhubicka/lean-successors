import SuccessorTree.V10.M2InducedAgeTransfer
import SuccessorTree.V10.NonedgePadding
import Mathlib.Tactic

/-!
# Neutral completion of a finite sparse L-age witness

Before non-edge padding we need a finite INITIAL ordinal carrier.
A bad copy picks only finitely many genuine upper vertices, leaving
unoccupied numerical positions. Fill those positions by the permitted
neutral singleton with no L-relations, WITHOUT claiming that their
L-types are prescribed image types.

Any new nontrivial irreducible forbidden copy would have to avoid all
fresh neutral vertices; a forbidden singleton is non-neutral by the
normalization. Hence forbidden avoidance is preserved.

This is a purely L-language finite-age theorem. E is absent.
-/

namespace SuccessorTree.V10

/-- Replace an arbitrary finite sparse carrier by an initial interval.
No old L atom between genuine carrier vertices is changed. Fresh
carrier points have the allowed neutral singleton and no incident
binary L atom. -/
def AgeTestModel.fillNeutralCarrier {db du dd : Nat}
    (A : AgeTestModel db du dd) (N : Nat) : AgeTestModel db du dd where
  carrier := {x | x < N}
  binary := fun x y t =>
    if x ∈ A.carrier ∧ y ∈ A.carrier then A.binary x y t else false
  unary := fun x t => if x ∈ A.carrier then A.unary x t else false
  diagonal := fun x t => if x ∈ A.carrier then A.diagonal x t else false

/-- Every real vertex keeps every incident atom to another real
vertex, together with its singleton and diagonal data. -/
theorem AgeTestModel.fillNeutralCarrier_old_binary {db du dd : Nat}
    (A : AgeTestModel db du dd) (N x y : Nat)
    (hx : x ∈ A.carrier) (hy : y ∈ A.carrier)
    (t : Fin db) :
    (A.fillNeutralCarrier N).binary x y t = A.binary x y t := by
  simp [AgeTestModel.fillNeutralCarrier,hx,hy]

theorem AgeTestModel.fillNeutralCarrier_old_unary {db du dd : Nat}
    (A : AgeTestModel db du dd) (N x : Nat)
    (hx : x ∈ A.carrier) (t : Fin du) :
    (A.fillNeutralCarrier N).unary x t = A.unary x t := by
  simp [AgeTestModel.fillNeutralCarrier,hx]

theorem AgeTestModel.fillNeutralCarrier_old_diagonal {db du dd : Nat}
    (A : AgeTestModel db du dd) (N x : Nat)
    (hx : x ∈ A.carrier) (t : Fin dd) :
    (A.fillNeutralCarrier N).diagonal x t = A.diagonal x t := by
  simp [AgeTestModel.fillNeutralCarrier,hx]

/-- An inserted neutral point is never joined by a positive directed
L atom to any other point. -/
theorem AgeTestModel.fillNeutralCarrier_binary_neutral_left {db du dd : Nat}
    (A : AgeTestModel db du dd) (N x y : Nat)
    (hx : x ∉ A.carrier) (t : Fin db) :
    (A.fillNeutralCarrier N).binary x y t = false := by
  simp [AgeTestModel.fillNeutralCarrier,hx]

theorem AgeTestModel.fillNeutralCarrier_binary_neutral_right {db du dd : Nat}
    (A : AgeTestModel db du dd) (N x y : Nat)
    (hy : y ∉ A.carrier) (t : Fin db) :
    (A.fillNeutralCarrier N).binary x y t = false := by
  simp [AgeTestModel.fillNeutralCarrier,hy]

/-- An induced forbidden copy in the filled carrier cannot touch a
neutral point. For a nontrivial forbidden pattern use irreducibility;
for singleton patterns use the non-neutral unary/diagonal certificate. -/
theorem AgeTestModel.fillNeutralCarrier_realizes_old {r db du dd : Nat}
    (A : AgeTestModel db du dd) (N : Nat)
    (P : ForbiddenAtomicPattern r db du dd)
    (e : Fin r → Nat)
    (hCopy : (A.fillNeutralCarrier N).Realizes P e)
    (hReal : ∀ a, e a ∈ A.carrier) :
    A.Realizes P e := by
  refine ⟨hCopy.1, ?_, ?_, ?_, ?_⟩
  · intro a
    exact hReal a
  · intro a b hab t
    simpa only [AgeTestModel.fillNeutralCarrier,
      if_pos ⟨hReal a,hReal b⟩] using hCopy.2.2.1 a b hab t
  · intro a t
    simpa only [AgeTestModel.fillNeutralCarrier,
      if_pos (hReal a)] using hCopy.2.2.2.1 a t
  · intro a t
    simpa only [AgeTestModel.fillNeutralCarrier,
      if_pos (hReal a)] using hCopy.2.2.2.2 a t

/-- Normalized forbidden-free ages remain forbidden-free after
filling gaps in an arbitrary finite carrier with neutral vertices.
The original carrier must lie below N, but need not itself be an
initial interval. -/
theorem NormalizedForbidden.avoids_fillNeutralCarrier {db du dd : Nat}
    (bad : NormalizedForbidden db du dd)
    (A : AgeTestModel db du dd) (N : Nat)
    (_hCarrier : ∀ x, x ∈ A.carrier → x < N)
    (hAvoid : bad.Avoids A) :
    bad.Avoids (A.fillNeutralCarrier N) := by
  cases bad with
  | singleton P hNeutral =>
      rintro ⟨e,he⟩
      have hReal : ∀ a : Fin 1, e a ∈ A.carrier := by
        intro a
        have ha : a = 0 := Subsingleton.elim _ _
        subst a
        by_contra hNot
        rcases hNeutral with ⟨t,ht⟩ | ⟨t,ht⟩
        · have h := he.2.2.2.1 0 t
          simp [AgeTestModel.fillNeutralCarrier,hNot,ht] at h
        · have h := he.2.2.2.2 0 t
          simp [AgeTestModel.fillNeutralCarrier,hNot,ht] at h
      exact hAvoid ⟨_, A.fillNeutralCarrier_realizes_old N P e he hReal⟩
  | nontrivial r P hr hIrred =>
      rintro ⟨e,he⟩
      have hReal : ∀ a : Fin r, e a ∈ A.carrier := by
        intro a
        by_contra hNot
        let z : Fin r := ⟨0, by omega⟩
        let o : Fin r := ⟨1,hr⟩
        have hzo : z ≠ o := by
          intro h
          have hh := congrArg Fin.val h
          norm_num [z,o] at hh
        obtain ⟨b,hab⟩ : ∃ b : Fin r, a ≠ b := by
          by_cases haz : a = z
          · exact ⟨o,by simpa [haz] using hzo⟩
          · exact ⟨z,haz⟩
        obtain ⟨t,ht | ht⟩ := hIrred a b hab
        · have h := he.2.2.1 a b hab t
          simp [AgeTestModel.fillNeutralCarrier,hNot,ht] at h
        · have h := he.2.2.1 b a hab.symm t
          simp [AgeTestModel.fillNeutralCarrier,hNot,ht] at h
      exact hAvoid ⟨_, A.fillNeutralCarrier_realizes_old N P e he hReal⟩

end SuccessorTree.V10

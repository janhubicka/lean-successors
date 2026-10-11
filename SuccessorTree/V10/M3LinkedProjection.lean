import SuccessorTree.V10.M3MiddleInsert
import Mathlib.Tactic

/-!
# Irreducible clone projection needs upper copying only when linked

The genuine finite M3 insertion gates its new-to-upper L pairs by
ell <= freeLevel_A(u), as required by E3. Thus the cloned vertex may
have absent relations to an ungated upper vertex even when the old
source n was L-linked to it. It would be incorrect to require copied
upper atoms for every upper vertex of the ambient inserted structure.

The projection argument actually needs copying only for upper vertices
appearing together with ell in an irreducible forbidden copy. Every
such vertex is L-linked to ell in some direction.

We prove this weaker version WITHOUT duplicating the previous full
MiddleCloneLData projection proof: restrict the carrier to the source n
and the vertices of the given forbidden copy. Every selected upper
vertex is then linked to ell by irreducibility, so the older exact
clone-data theorem applies to this restricted L-model. Its projected
copy is lifted back to W without ell.

All finite witnesses here are pure L-structures, never E-partials.
-/

namespace SuccessorTree.V10

/-- Clone data with an E3-compatible upper requirement: only an
actually L-linked upper vertex needs to copy its old n-pairs.
All lower and singleton fields are unchanged. -/
structure MiddleCloneLinkedLData {db du dd : Nat}
    (W : AgeTestModel db du dd) (n ell d : Nat) : Prop where
  n_before : n < ell
  cut_before_source : d ≤ n
  source_in_carrier : n ∈ W.carrier
  same_unary : ∀ t : Fin du, W.unary ell t = W.unary n t
  same_diagonal : ∀ t : Fin dd, W.diagonal ell t = W.diagonal n t
  no_lower_links : ∀ x, d ≤ x → x < ell → ∀ t : Fin db,
    W.binary ell x t = false ∧ W.binary x ell t = false
  copy_lower : ∀ x, x < d → ∀ t : Fin db,
    W.binary ell x t = W.binary n x t ∧
    W.binary x ell t = W.binary x n t
  copy_upper_linked : ∀ x, x ∈ W.carrier → ell < x →
    (∃ t : Fin db,
      W.binary ell x t = true ∨ W.binary x ell t = true) →
    ∀ t : Fin db,
      W.binary ell x t = W.binary n x t ∧
      W.binary x ell t = W.binary x n t

/-- A strict upper-copy clone structure is also a linked-upper clone;
this adapter retains the earlier independently verified projection API. -/
theorem MiddleCloneLData.toLinked
    {db du dd : Nat}
    {W : AgeTestModel db du dd} {n ell d : Nat}
    (h : MiddleCloneLData W n ell d) :
    MiddleCloneLinkedLData W n ell d := {
  n_before := h.n_before
  cut_before_source := h.cut_before_source
  source_in_carrier := h.source_in_carrier
  same_unary := h.same_unary
  same_diagonal := h.same_diagonal
  no_lower_links := h.no_lower_links
  copy_lower := h.copy_lower
  copy_upper_linked := by
    intro x hx hAbove hLink t
    exact h.copy_upper x hx hAbove t
}

/-- Every irreducible copy through the middle clone projects even
when the upper-copy identities hold only for upper vertices linked
to the clone. The restriction to the copy's own carrier is crucial:
it prevents smuggling an ungated relation into the projected copy. -/
theorem MiddleCloneLinkedLData.irred_copy_projects
    {r db du dd : Nat}
    {W : AgeTestModel db du dd} {n ell d : Nat}
    (h : MiddleCloneLinkedLData W n ell d)
    (P : ForbiddenAtomicPattern r db du dd)
    (hIrred : P.Irreducible)
    (e : Fin r → Nat)
    (hCopy : W.Realizes P e) :
    (W.withoutVertex ell).Realizes P
      (fun a => projectMiddleClone ell n (e a)) := by
  classical
  by_cases hContains : ∃ a : Fin r, e a = ell
  · obtain ⟨a0, ha0⟩ := hContains
    let Select : Nat → Prop := fun x => x = n ∨ ∃ a : Fin r, e a = x
    let V : AgeTestModel db du dd := W.restrictCarrier Select
    have hStrong : MiddleCloneLData V n ell d := by
      refine {
        n_before := h.n_before
        cut_before_source := h.cut_before_source
        source_in_carrier := ?_
        same_unary := h.same_unary
        same_diagonal := h.same_diagonal
        no_lower_links := h.no_lower_links
        copy_lower := h.copy_lower
        copy_upper := ?_ }
      · exact ⟨h.source_in_carrier, Or.inl rfl⟩
      · intro x hx hAbove t
        have hIn : x ∈ W.carrier := hx.1
        have hSel : Select x := hx.2
        rcases hSel with hEq | ⟨a, ha⟩
        · have hn := h.n_before
          rw [hEq] at hAbove
          omega
        · have hne : a0 ≠ a := by
            intro hEq
            subst a
            omega
          obtain ⟨t0, ht0⟩ := hIrred a0 a hne
          have hLinked : ∃ t1 : Fin db,
              W.binary ell x t1 = true ∨
              W.binary x ell t1 = true := by
            refine ⟨t0, ?_⟩
            rcases ht0 with hForward | hBackward
            · left
              have hh := hCopy.2.2.1 a0 a hne t0
              rw [ha0, ha] at hh
              exact hh.trans hForward
            · right
              have hh := hCopy.2.2.1 a a0 hne.symm t0
              rw [ha, ha0] at hh
              exact hh.trans hBackward
          exact h.copy_upper_linked x hIn hAbove hLinked t
    have hSelectedCopy : V.Realizes P e :=
      AgeTestModel.realizes_restrictCarrier W Select P e hCopy
        (by
          intro a
          exact Or.inr ⟨a, rfl⟩)
    have hProjectedV : (V.withoutVertex ell).Realizes P
        (fun a => projectMiddleClone ell n (e a)) :=
      hStrong.irred_copy_projects P hIrred e hSelectedCopy
    have hProjectedVUnrestricted : V.Realizes P
        (fun a => projectMiddleClone ell n (e a)) :=
      AgeTestModel.realizes_of_restrictCarrier V
        (fun x => x ≠ ell) P _ hProjectedV
    have hProjectedW : W.Realizes P
        (fun a => projectMiddleClone ell n (e a)) :=
      AgeTestModel.realizes_of_restrictCarrier W
        Select P _ hProjectedVUnrestricted
    apply AgeTestModel.realizes_restrictCarrier W
      (fun x => x ≠ ell) P _ hProjectedW
    intro a
    by_cases ha : e a = ell
    · simp [projectMiddleClone, ha, Nat.ne_of_lt h.n_before]
    · simp [projectMiddleClone, ha]
  · have hAway : ∀ a : Fin r, e a ≠ ell := by
      intro a ha
      exact hContains ⟨a,ha⟩
    have hProjEq :
        (fun a : Fin r => projectMiddleClone ell n (e a)) = e := by
      funext a
      simp [projectMiddleClone, hAway a]
    rw [hProjEq]
    exact AgeTestModel.realizes_restrictCarrier W
      (fun x => x ≠ ell) P e hCopy hAway

/-- The linked-only clone conditions suffice for the corrected finite
deletion test on any forbidden normalized age. Forbidden singleton
patterns project to n, and irreducible patterns use the actual
linked-upper reduction. -/
theorem MiddleCloneLinkedLData.avoidance_of_deletion
    {db du dd : Nat}
    {W : AgeTestModel db du dd} {n ell d : Nat}
    (h : MiddleCloneLinkedLData W n ell d)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (W.withoutVertex ell)) :
    ∀ bad, bad ∈ family → bad.Avoids W := by
  intro bad hBad
  cases bad with
  | singleton P hNonNeutral =>
      rintro ⟨e,hCopy⟩
      exact (hAvoid (.singleton P hNonNeutral) hBad)
        ⟨_, h.irred_copy_projects P
          (forbidden_singleton_irreducible P) e hCopy⟩
  | nontrivial r P hr hIrred =>
      rintro ⟨e,hCopy⟩
      exact (hAvoid (.nontrivial r P hr hIrred) hBad)
        ⟨_, h.irred_copy_projects P hIrred e hCopy⟩

end SuccessorTree.V10

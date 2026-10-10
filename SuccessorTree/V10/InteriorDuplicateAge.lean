import SuccessorTree.V10.EndDuplicateAge
import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# Projection through an interior duplicated L-coordinate

The repaired finite common-socle B3 condition for M3 involves an
arbitrary finite L-age test witness, not a partial structure. Its
copy of the source vertex n at a later inserted coordinate ell is
interior to that witness, with possibly many vertices above ell.

A checked projection requires precisely the following atomic profile:
the clone has the original singleton, it is unlinked to all
intermediate vertices n<=x<ell, and it has the same directed L
relations as n to each x<n and to each x>ell. The profile includes
negative tuples in each direction.

For an irreducible forbidden induced copy using ell, every lower
member must therefore lie below n. Replacing ell by n preserves
strict order, all unary/diagonal information and every binary atom.
Thus the forbidden copy survives deletion of ell. In particular,
an interior duplicate satisfying this profile causes no finite
L-age change, regardless of auxiliary E.
-/

namespace SuccessorTree.V10

/-- Atomic conditions for one interior duplicate in a finite
L-age witness. No auxiliary E relation is assumed or needed. -/
structure InteriorDuplicateLProfile
    {db du dd : Nat}
    (W : AgeTestModel db du dd) (n ell : Nat) : Prop where
  n_lt_ell : n < ell
  original_mem : n ∈ W.carrier
  unary_eq : ∀ t : Fin du, W.unary ell t = W.unary n t
  diagonal_eq : ∀ t : Fin dd, W.diagonal ell t = W.diagonal n t
  below_eq : ∀ x, x < n → ∀ t : Fin db,
    W.binary ell x t = W.binary n x t ∧
    W.binary x ell t = W.binary x n t
  middle_zero : ∀ x, n ≤ x → x < ell → ∀ t : Fin db,
    W.binary ell x t = false ∧ W.binary x ell t = false
  above_eq : ∀ x, ell < x → ∀ t : Fin db,
    W.binary ell x t = W.binary n x t ∧
    W.binary x ell t = W.binary x n t

/-- Replace only the inserted duplicate ell by its original n. -/
def interiorDuplicateProject (n ell x : Nat) : Nat :=
  if x = ell then n else x

/-- In any irreducible copy containing the duplicate, all OTHER
vertices below the duplicate must lie strictly below the original.
This also shows the original n cannot occur in the same copy. -/
theorem interiorDuplicate_irred_lower_below_original
    {r db du dd : Nat}
    (W : AgeTestModel db du dd) (n ell : Nat)
    (h : InteriorDuplicateLProfile W n ell)
    (P : ForbiddenAtomicPattern r db du dd)
    (hirred : P.Irreducible)
    (f : Fin r → Nat) (hCopy : W.Realizes P f)
    (a0 a : Fin r) (ha : a ≠ a0)
    (ha0 : f a0 = ell)
    (hBelow : f a < ell) :
    f a < n := by
  by_contra hBad
  have hge : n ≤ f a := by omega
  obtain ⟨t, hp⟩ := hirred a0 a ha.symm
  have hzero := h.middle_zero (f a) hge hBelow t
  rcases hp with hp | hp
  · have heq := hCopy.2.2.1 a0 a ha.symm t
    rw [ha0, hzero.1, hp] at heq
    cases heq
  · have heq := hCopy.2.2.1 a a0 ha t
    rw [ha0, hzero.2, hp] at heq
    cases heq

/-- Project an irreducible induced ordered forbidden copy containing
the interior duplicate into the L-structure with that coordinate
removed. Unlike an unordered projection, the monotonicity proof
essentially uses the absence of clone links to intermediate vertices. -/
theorem interiorDuplicate_irred_copy_projects
    {r db du dd : Nat}
    (W : AgeTestModel db du dd) (n ell : Nat)
    (h : InteriorDuplicateLProfile W n ell)
    (P : ForbiddenAtomicPattern r db du dd)
    (hirred : P.Irreducible)
    (f : Fin r → Nat) (hCopy : W.Realizes P f)
    (a0 : Fin r) (ha0 : f a0 = ell) :
    (W.withoutVertex ell).Realizes P
      (fun a => interiorDuplicateProject n ell (f a)) := by
  have hinj := hCopy.1.injective
  have hne (a : Fin r) (ha : a ≠ a0) : f a ≠ ell := by
    intro hf
    exact ha (hinj (hf.trans ha0.symm))
  have hsmall (a : Fin r) (ha : a ≠ a0) (hl : f a < ell) :
      f a < n :=
    interiorDuplicate_irred_lower_below_original W n ell h
      P hirred f hCopy a0 a ha ha0 hl
  have hindex (a : Fin r) :
      interiorDuplicateProject n ell (f a) =
        if a = a0 then n else f a := by
    by_cases ha : a = a0
    · subst a
      simp [interiorDuplicateProject, ha0]
    · simp [interiorDuplicateProject, hne a ha, ha]
  have hm : StrictMono
      (fun a : Fin r => interiorDuplicateProject n ell (f a)) := by
    intro a b hab
    by_cases hb : b = a0
    · subst b
      have hlt : f a < ell := by simpa [ha0] using hCopy.1 hab
      have hneA : a ≠ a0 := by
        intro hEq
        subst a
        exact (lt_irrefl a0) hab
      have hlow := hsmall a hneA hlt
      simpa [hindex, hneA] using hlow
    · by_cases ha : a = a0
      · subst a
        have hhigh : ell < f b := by
          simpa [ha0] using hCopy.1 hab
        have hval : n < f b := lt_trans h.n_lt_ell hhigh
        simpa [hindex, hb] using hval
      · simpa [hindex, ha, hb] using hCopy.1 hab
  refine ⟨hm, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : a = a0
    · subst a
      change (interiorDuplicateProject n ell (f a0)) ∈
        W.carrier ∧ interiorDuplicateProject n ell (f a0) ≠ ell
      simpa [interiorDuplicateProject, ha0] using
        And.intro h.original_mem (Nat.ne_of_lt h.n_lt_ell)
    · change (interiorDuplicateProject n ell (f a)) ∈
        W.carrier ∧ interiorDuplicateProject n ell (f a) ≠ ell
      simpa [interiorDuplicateProject, hne a ha] using
        And.intro (hCopy.2.1 a) (hne a ha)
  · intro a b hab t
    by_cases ha : a = a0
    · subst a
      have hb : b ≠ a0 := by
        intro heq
        subst b
        exact (ne_of_lt hab) rfl
      have hbne := hne b hb
      have hpair :
          W.binary n (f b) t = W.binary ell (f b) t := by
        rcases lt_or_gt_of_ne hbne with hlow | hhigh
        · exact (h.below_eq (f b) (hsmall b hb hlow) t).1.symm
        · exact (h.above_eq (f b) hhigh t).1.symm
      calc
        W.binary (interiorDuplicateProject n ell (f a0))
            (interiorDuplicateProject n ell (f b)) t =
          W.binary n (f b) t := by
            simp [interiorDuplicateProject, ha0, hbne]
        _ = W.binary ell (f b) t := hpair
        _ = P.binary a0 b t := by
          have heq := hCopy.2.2.1 a0 b (ne_of_lt hab) t
          simpa [ha0] using heq
    · by_cases hb : b = a0
      · subst b
        have hane := hne a ha
        have hlow : f a < ell := by
          simpa [ha0] using hCopy.1 hab
        have hpair :
            W.binary (f a) n t = W.binary (f a) ell t :=
          (h.below_eq (f a) (hsmall a ha hlow) t).2.symm
        calc
          W.binary (interiorDuplicateProject n ell (f a))
              (interiorDuplicateProject n ell (f a0)) t =
            W.binary (f a) n t := by
              simp [interiorDuplicateProject, ha0, hane]
          _ = W.binary (f a) ell t := hpair
          _ = P.binary a a0 t := by
            have heq := hCopy.2.2.1 a a0 (ne_of_lt hab) t
            simpa [ha0] using heq
      · have hane := hne a ha
        have hbne := hne b hb
        simpa [interiorDuplicateProject, hane, hbne] using
          hCopy.2.2.1 a b (ne_of_lt hab) t
  · intro a t
    by_cases ha : a = a0
    · subst a
      calc
        W.unary (interiorDuplicateProject n ell (f a0)) t =
          W.unary n t := by simp [interiorDuplicateProject, ha0]
        _ = W.unary ell t := (h.unary_eq t).symm
        _ = P.unary a0 t := by
          simpa [ha0] using hCopy.2.2.2.1 a0 t
    · simpa [interiorDuplicateProject, hne a ha] using
        hCopy.2.2.2.1 a t
  · intro a t
    by_cases ha : a = a0
    · subst a
      calc
        W.diagonal (interiorDuplicateProject n ell (f a0)) t =
          W.diagonal n t := by simp [interiorDuplicateProject, ha0]
        _ = W.diagonal ell t := (h.diagonal_eq t).symm
        _ = P.diagonal a0 t := by
          simpa [ha0] using hCopy.2.2.2.2 a0 t
    · simpa [interiorDuplicateProject, hne a ha] using
        hCopy.2.2.2.2 a t

/-- Any irreducible induced ordered forbidden pattern which occurs in
a middle-duplicated L witness already occurs after deletion of ell. -/
theorem interiorDuplicate_forbidden_copy_projects
    {r db du dd : Nat}
    (W : AgeTestModel db du dd) (n ell : Nat)
    (h : InteriorDuplicateLProfile W n ell)
    (P : ForbiddenAtomicPattern r db du dd)
    (hirred : P.Irreducible)
    (f : Fin r → Nat) (hCopy : W.Realizes P f) :
    ∃ g : Fin r → Nat, (W.withoutVertex ell).Realizes P g := by
  classical
  by_cases hContains : ∃ a : Fin r, f a = ell
  · obtain ⟨a0,ha0⟩ := hContains
    exact ⟨_, interiorDuplicate_irred_copy_projects
      W n ell h P hirred f hCopy a0 ha0⟩
  · refine ⟨f, ?_⟩
    exact AgeTestModel.realizes_restrictCarrier
      W (fun x => x ≠ ell) P f hCopy
      (fun a => by
        intro he
        exact hContains ⟨a,he⟩)

/-- The finite no-age-change implication for a middle-clone profile.
This is the nontrivial finite combinatorial part of verifying M3's
corrected B3; it does not yet construct the middle clone from f. -/
theorem interiorDuplicate_avoids_of_delete
    {db du dd : Nat}
    (W : AgeTestModel db du dd) (n ell : Nat)
    (h : InteriorDuplicateLProfile W n ell)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family →
      bad.Avoids (W.withoutVertex ell)) :
    ∀ bad, bad ∈ family → bad.Avoids W := by
  intro bad hbad
  cases bad with
  | singleton P hp =>
      rintro ⟨f,hCopy⟩
      exact (hAvoid (.singleton P hp) hbad)
        (interiorDuplicate_forbidden_copy_projects W n ell h P
          (forbidden_singleton_irreducible P) f hCopy)
  | nontrivial r P hr hirred =>
      rintro ⟨f,hCopy⟩
      exact (hAvoid (.nontrivial r P hr hirred) hbad)
        (interiorDuplicate_forbidden_copy_projects W n ell h P
          hirred f hCopy)

end SuccessorTree.V10

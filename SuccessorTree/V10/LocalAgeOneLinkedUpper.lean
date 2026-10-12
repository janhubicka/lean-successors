import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# Age preservation for one linked upper vertex

For a finite one-coordinate L-insertion, suppose the newly inserted
vertex ell has L-links to at most ONE upper vertex v. Irreducibility
forces every forbidden nontrivial copy using ell to lie entirely
within the initial socle {0,...,ell} and this single upper vertex v.
Consequently it suffices to check forbidden age on that small
induced carrier. No B3 test on arbitrary collections of upper
crossing types is needed.

This is an AGE reduction, not a construction of the insertion and
not the M2 extension theorem. The condition that the single core
is forbidden-free remains an explicit hypothesis.
-/

namespace SuccessorTree.V10

/-- If all links from the inserted vertex to its upper tail point to
at most one designated vertex, and the initial socle plus that vertex
is forbidden-free, then the whole insertion is forbidden-free.

Copies avoiding ell pull back into A; copies containing ell are
restricted to the indicated core using binary irreducibility. This
holds for arbitrary directed binary symbols and all unary/diagonal
atoms, without any hypothesis on the auxiliary E relation. -/
theorem IsLInsertion.avoids_of_one_linked_upper
    {db du dd : Nat}
    {A B : EnumeratedPartialStructure db du dd}
    {ell : Nat}
    (hInsert : IsLInsertion A B ell)
    (family : List (NormalizedForbidden db du dd))
    (hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (v : Nat)
    (hOne : ∀ u, u < B.size → ell < u →
      (∃ t : Fin db,
        B.L.binary ell u t = true ∨
        B.L.binary u ell t = true) →
      u = v)
    (hCore : ∀ bad, bad ∈ family →
      bad.Avoids (B.L.restrictCarrier (fun x => x ≤ ell ∨ x = v))) :
    ∀ bad, bad ∈ family → bad.Avoids B.L := by
  intro bad hbad
  cases bad with
  | singleton P hNeutral =>
      rintro ⟨e, he⟩
      by_cases hEll : e 0 = ell
      · have hCoreMap :
            ∀ a : Fin 1, e a ≤ ell ∨ e a = v := by
          intro a
          have ha : a = 0 := Subsingleton.elim _ _
          subst a
          exact Or.inl (Nat.le_of_eq hEll)
        have hCoreCopy :=
          AgeTestModel.realizes_restrictCarrier B.L
            (fun x => x ≤ ell ∨ x = v) P e he hCoreMap
        exact (hCore (.singleton P hNeutral) hbad) ⟨e, hCoreCopy⟩
      · have hAway : ∀ a : Fin 1, e a ≠ ell := by
          intro a
          have ha : a = 0 := Subsingleton.elim _ _
          simpa [ha] using hEll
        exact (hAvoidA (.singleton P hNeutral) hbad)
          ⟨e, hInsert.realizes_away_projects P e he hAway⟩
  | nontrivial r P hr hIrred =>
      rintro ⟨e, he⟩
      by_cases hContains : ∃ a : Fin r, e a = ell
      · obtain ⟨aell, haell⟩ := hContains
        have hCoreMap :
            ∀ a : Fin r, e a ≤ ell ∨ e a = v := by
          intro a
          by_cases hLow : e a ≤ ell
          · exact Or.inl hLow
          · have hUpper : ell < e a := by omega
            have hane : aell ≠ a := by
              intro hEq
              subst a
              omega
            obtain ⟨t, ht⟩ := hIrred aell a hane
            have hBin0 := he.2.2.1 aell a hane t
            have hBin1 := he.2.2.1 a aell hane.symm t
            have hLinked :
                ∃ t : Fin db,
                  B.L.binary ell (e a) t = true ∨
                  B.L.binary (e a) ell t = true := by
              refine ⟨t, ?_⟩
              rw [haell] at hBin0 hBin1
              simpa only [hBin0, hBin1] using ht
            have hSize : e a < B.size :=
              (B.carrier_iff (e a)).1 (he.2.1 a)
            exact Or.inr (hOne (e a) hSize hUpper hLinked)
        have hCoreCopy :=
          AgeTestModel.realizes_restrictCarrier B.L
            (fun x => x ≤ ell ∨ x = v) P e he hCoreMap
        exact (hCore (.nontrivial r P hr hIrred) hbad)
          ⟨e, hCoreCopy⟩
      · have hAway : ∀ a : Fin r, e a ≠ ell := by
          intro a hEq
          exact hContains ⟨a, hEq⟩
        exact (hAvoidA (.nontrivial r P hr hIrred) hbad)
          ⟨e, hInsert.realizes_away_projects P e he hAway⟩

end SuccessorTree.V10

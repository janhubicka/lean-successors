import SuccessorTree.V10.EndDuplicatePartial
import SuccessorTree.V10.PrefixReplicaAge
import SuccessorTree.V10.AdmissibleKptPrefix
import Mathlib.Tactic

/-!
# Irreducible forbidden-age preservation for one terminal duplicate

The new final vertex N in duplicateEndPartial A n has no L-links
to any old vertex u outside the free socle u<fl_A(n). In any
irreducible forbidden copy using N, every other copied vertex
must therefore lie below fl_A(n)≤n, and the new vertex can be
projected back to n in the original structure, preserving order
and all positive/negative unary and directed binary atoms.

Consequently appending this particular duplicate cannot introduce
a forbidden irreducible configuration. Unlike insertion of an
isolated filler, here singleton forbidden structures cause no
difficulty: the new singleton is an exact copy of an old singleton.

This is the local end-duplication ingredient needed for the
global one-level skip map of (M3). It does not yet prove that
the global map is shape-preserving or skips only one level.
-/

namespace SuccessorTree.V10

/-- Project every old vertex to itself and the new clone to
its source original. The projection is increasing on any
irreducible induced copy, not necessarily on ALL vertices. -/
def duplicateEndProject (N n x : Nat) : Nat :=
  if x = N then n else x

/-- An irreducible forbidden copy cannot have an old vertex
outside the clone's free E-socle joined to the new clone. -/
theorem duplicateEnd_irred_before_new_belowCut
    {r db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) (hn : n < A.size)
    (F : ForbiddenAtomicPattern r db du dd)
    (hIrred : F.Irreducible)
    (f : Fin r → Nat)
    (hCopy : (duplicateEndL A n).Realizes F f)
    (a b : Fin r) (hab : a ≠ b)
    (haOld : f a < A.size)
    (hbNew : f b = A.size) :
    f a < A.freeLevel n := by
  by_contra hnot
  have hAbove : A.freeLevel n ≤ f a := by omega
  obtain ⟨t, hEdge⟩ := hIrred a b hab
  have hZero := duplicateEndL_cross_above A n (f a)
    hn hAbove haOld t
  rcases hEdge with hEdge | hEdge
  · have hPreserve := hCopy.2.2.1 a b hab t
    rw [hbNew, hZero.1, hEdge] at hPreserve
    contradiction
  · have hPreserve := hCopy.2.2.1 b a hab.symm t
    rw [hbNew, hZero.2, hEdge] at hPreserve
    contradiction

/-- Every forbidden copy of an irreducible pattern in the end
duplicate projects monotonically into the original structure. -/
theorem duplicateEnd_irred_copy_projects
    {r db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) (hn : n < A.size)
    (F : ForbiddenAtomicPattern r db du dd)
    (hIrred : F.Irreducible)
    (f : Fin r → Nat)
    (hCopy : (duplicateEndL A n).Realizes F f) :
    A.L.Realizes F
      (fun a => duplicateEndProject A.size n (f a)) := by
  obtain ⟨hMono, hIn, hBinary, hUnary, hDiagonal⟩ := hCopy
  have hOldOrNew (a : Fin r) :
      f a < A.size ∨ f a = A.size := by
    have hf : f a < A.size + 1 := hIn a
    omega
  have hNeOfNe (a b : Fin r) (hab : a ≠ b) :
      f a ≠ f b := fun heq => hab (hMono.injective heq)
  have hOldNew (a b : Fin r) (hab : a ≠ b)
      (haOld : f a < A.size) (hbNew : f b = A.size) :
      f a < A.freeLevel n :=
    duplicateEnd_irred_before_new_belowCut A n hn
      F hIrred f ⟨hMono, hIn, hBinary, hUnary, hDiagonal⟩
      a b hab haOld hbNew
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hmono := hMono hab
    rcases hOldOrNew b with hbOld | hbNew
    · have haOld : f a < A.size := by omega
      have haNe : f a ≠ A.size := Nat.ne_of_lt haOld
      have hbNe : f b ≠ A.size := Nat.ne_of_lt hbOld
      simpa [duplicateEndProject, haNe, hbNe] using hmono
    · have haOld : f a < A.size := by omega
      have haNe : f a ≠ A.size := Nat.ne_of_lt haOld
      have hCut := hOldNew a b (ne_of_lt hab) haOld hbNew
      have hlt : f a < n :=
        lt_of_lt_of_le hCut (A.freeLevel_le n)
      simp [duplicateEndProject, haNe, hbNew, hlt]
  · intro a
    have ha := hOldOrNew a
    apply (A.carrier_iff (duplicateEndProject A.size n (f a))).2
    rcases ha with haOld | haNew
    · have hNe : f a ≠ A.size := Nat.ne_of_lt haOld
      simpa [duplicateEndProject, hNe] using haOld
    · simpa [duplicateEndProject, haNew] using hn
  · intro a b hab t
    by_cases haNew : f a = A.size
    · have hbNe : f b ≠ A.size :=
        fun hbNew => hNeOfNe a b hab (haNew.trans hbNew.symm)
      have hbOld : f b < A.size := by
        rcases hOldOrNew b with h | h
        · exact h
        · exact (hbNe h).elim
      have hCut := hOldNew b a hab.symm hbOld haNew
      calc
        A.L.binary
            (duplicateEndProject A.size n (f a))
            (duplicateEndProject A.size n (f b)) t =
          A.L.binary n (f b) t := by
            simp [duplicateEndProject, haNew, hbNe]
        _ = (duplicateEndL A n).binary (f a) (f b) t := by
            rw [haNew]
            exact (duplicateEndL_cross_below A n (f b) hn hCut t).2.symm
        _ = F.binary a b t := hBinary a b hab t
    · rcases hOldOrNew b with hbOld | hbNew
      · have haOld : f a < A.size := by
          rcases hOldOrNew a with h | h
          · exact h
          · exact (haNew h).elim
        have hbNe : f b ≠ A.size := Nat.ne_of_lt hbOld
        calc
          A.L.binary
              (duplicateEndProject A.size n (f a))
              (duplicateEndProject A.size n (f b)) t =
            A.L.binary (f a) (f b) t := by
              simp [duplicateEndProject, haNew, hbNe]
          _ = (duplicateEndL A n).binary (f a) (f b) t :=
            ((duplicateEndL_old A n (f a) (f b)
              haOld hbOld).1 t).symm
          _ = F.binary a b t := hBinary a b hab t
      · have haOld : f a < A.size := by
          rcases hOldOrNew a with h | h
          · exact h
          · exact (haNew h).elim
        have hCut := hOldNew a b hab haOld hbNew
        calc
          A.L.binary
              (duplicateEndProject A.size n (f a))
              (duplicateEndProject A.size n (f b)) t =
            A.L.binary (f a) n t := by
              simp [duplicateEndProject, haNew, hbNew]
          _ = (duplicateEndL A n).binary (f a) (f b) t := by
              rw [hbNew]
              exact (duplicateEndL_cross_below A n (f a) hn hCut t).1.symm
          _ = F.binary a b t := hBinary a b hab t
  · intro a t
    by_cases ha : f a = A.size
    · calc
        A.L.unary (duplicateEndProject A.size n (f a)) t =
          A.L.unary n t := by simp [duplicateEndProject, ha]
        _ = (duplicateEndL A n).unary (f a) t := by
          rw [ha]
          exact ((duplicateEndL_newSingleton A n).2.1 t).symm
        _ = F.unary a t := hUnary a t
    · have hOld : f a < A.size := by
        rcases hOldOrNew a with h | h
        · exact h
        · exact (ha h).elim
      calc
        A.L.unary (duplicateEndProject A.size n (f a)) t =
          A.L.unary (f a) t := by simp [duplicateEndProject, ha]
        _ = (duplicateEndL A n).unary (f a) t :=
          ((duplicateEndL_old A n (f a) (f a)
            hOld hOld).2.1 t).symm
        _ = F.unary a t := hUnary a t
  · intro a t
    by_cases ha : f a = A.size
    · calc
        A.L.diagonal (duplicateEndProject A.size n (f a)) t =
          A.L.diagonal n t := by simp [duplicateEndProject, ha]
        _ = (duplicateEndL A n).diagonal (f a) t := by
          rw [ha]
          exact ((duplicateEndL_newSingleton A n).2.2 t).symm
        _ = F.diagonal a t := hDiagonal a t
    · have hOld : f a < A.size := by
        rcases hOldOrNew a with h | h
        · exact h
        · exact (ha h).elim
      calc
        A.L.diagonal (duplicateEndProject A.size n (f a)) t =
          A.L.diagonal (f a) t := by simp [duplicateEndProject, ha]
        _ = (duplicateEndL A n).diagonal (f a) t :=
          ((duplicateEndL_old A n (f a) (f a)
            hOld hOld).2.2 t).symm
        _ = F.diagonal a t := hDiagonal a t

/-- A nontrivial irreducible forbidden pattern remains avoided after
end duplication: any newly appearing copy would project back into A. -/
theorem duplicateEndL_preserves_avoidance
    {r db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) (hn : n < A.size)
    (F : ForbiddenAtomicPattern r db du dd)
    (hIrred : F.Irreducible)
    (hAvoid : ¬ ∃ f : Fin r → Nat, A.L.Realizes F f) :
    ¬ ∃ f : Fin r → Nat,
      (duplicateEndL A n).Realizes F f := by
  rintro ⟨f,hCopy⟩
  exact hAvoid ⟨_, duplicateEnd_irred_copy_projects
    A n hn F hIrred f hCopy⟩

/-- Singleton patterns are vacuously irreducible, so the clone
does not require the neutral-singleton normalization at all. -/
theorem forbidden_singleton_irreducible
    {db du dd : Nat}
    (F : ForbiddenAtomicPattern 1 db du dd) :
    F.Irreducible := by
  intro a b hab
  exact (hab (Subsingleton.elim a b)).elim

/-- Every normalized forbidden pattern is preserved by
terminal end duplication, including singleton and nontrivial cases. -/
theorem NormalizedForbidden.duplicateEnd_preserves_avoidance
    {db du dd : Nat}
    (bad : NormalizedForbidden db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) (hn : n < A.size)
    (hAvoid : bad.Avoids A.L) :
    bad.Avoids (duplicateEndL A n) := by
  cases bad with
  | singleton F hNeutral =>
    exact duplicateEndL_preserves_avoidance
      A n hn F (forbidden_singleton_irreducible F) hAvoid
  | nontrivial r F hr hIrred =>
    exact duplicateEndL_preserves_avoidance A n hn F hIrred hAvoid

end SuccessorTree.V10

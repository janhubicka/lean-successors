import SuccessorTree.V10.EndDuplicateAge
import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# Finite L-age projection for a duplicate inserted in the middle

This is an L-only auxiliary lemma towards the corrected B3 condition
for the M3 duplicate. The inserted vertex ell copies an earlier vertex n:
its singleton is copied; the new-to-lower directed tuples are copied
only below the source's free cut d <= n; those to old lower coordinates
in [d,ell) are absent; and those to upper coordinates >ell are copied
from n. Every comparison includes *both Boolean values*, not merely
positive edges.

For an irreducible forbidden copy containing ell, all other lower copy
vertices lie below d <= n (or else they would not be linked to ell).
Its upper copy vertices are >ell>n. The copy cannot use n itself.
Thus replacing ell by n is an order-preserving induced copy into the
structure with ell deleted. Singletons are covered the same way.

No E relation is imposed on the finite age witness. This module does
NOT prove that the canonical M3 successor prescription supplies these
atomic identities: that separate bridge remains OPEN.
-/

namespace SuccessorTree.V10

/-- The order-coordinate projection that sends the duplicate ell to
its earlier source n, and fixes every other coordinate. -/
def projectMiddleClone (ell n x : Nat) : Nat :=
  if x = ell then n else x

/-- Exact atomic data of a middle-inserted duplicate in an arbitrary
L-structure. The source cut d is no larger than n < ell.
This is an auxiliary Prop whose fields must later be *derived* from
the actual M3 prescription rather than postulated in the M3 theorem. -/
structure MiddleCloneLData {db du dd : Nat}
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
  copy_upper : ∀ x, ell < x → ∀ t : Fin db,
    W.binary ell x t = W.binary n x t ∧
    W.binary x ell t = W.binary x n t

/-- Every distinct lower coordinate of an irreducible copy using the
duplicate is strictly below the source free cut. -/
theorem MiddleCloneLData.lower_below_cut
    {r db du dd : Nat}
    {W : AgeTestModel db du dd} {n ell d : Nat}
    (h : MiddleCloneLData W n ell d)
    (P : ForbiddenAtomicPattern r db du dd)
    (hIrred : P.Irreducible)
    (e : Fin r → Nat)
    (hCopy : W.Realizes P e)
    (a b : Fin r) (hab : a ≠ b)
    (haBelow : e a < ell) (hbEll : e b = ell) :
    e a < d := by
  by_contra hn
  have hd : d ≤ e a := by omega
  obtain ⟨t, ht⟩ := hIrred a b hab
  obtain ⟨hElToA, hAToEl⟩ :=
    h.no_lower_links (e a) hd haBelow t
  have hAB := hCopy.2.2.1 a b hab t
  have hBA := hCopy.2.2.1 b a hab.symm t
  rcases ht with ht | ht
  · rw [hbEll, ht] at hAB
    exact Bool.false_ne_true (hAToEl.symm.trans hAB)
  · rw [hbEll, ht] at hBA
    exact Bool.false_ne_true (hElToA.symm.trans hBA)

/-- Replacing the duplicate by its old source is an ordered induced
realization of every irreducible L-pattern. The target carrier already
has the duplicate deleted, and all positive/negative atoms are exact. -/
theorem MiddleCloneLData.irred_copy_projects
    {r db du dd : Nat}
    {W : AgeTestModel db du dd} {n ell d : Nat}
    (h : MiddleCloneLData W n ell d)
    (P : ForbiddenAtomicPattern r db du dd)
    (hIrred : P.Irreducible)
    (e : Fin r → Nat)
    (hCopy : W.Realizes P e) :
    (W.withoutVertex ell).Realizes P
      (fun a => projectMiddleClone ell n (e a)) := by
  obtain ⟨hMono, hIn, hBinary, hUnary, hDiagonal⟩ := hCopy
  have hDist (a b : Fin r) (hab : a ≠ b) : e a ≠ e b :=
    fun hh => hab (hMono.injective hh)
  have hEarlier (a b : Fin r) (hab : a ≠ b)
      (haBelow : e a < ell) (hbEll : e b = ell) :
      e a < d := by
    exact h.lower_below_cut P hIrred e
      ⟨hMono, hIn, hBinary, hUnary, hDiagonal⟩
      a b hab haBelow hbEll
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    change projectMiddleClone ell n (e a) <
      projectMiddleClone ell n (e b)
    have hlt := hMono hab
    by_cases hb : e b = ell
    · have ha : e a ≠ ell := by omega
      change (if e a = ell then n else e a) <
        (if e b = ell then n else e b)
      rw [if_neg ha, if_pos hb]
      exact lt_of_lt_of_le
        (hEarlier a b (ne_of_lt hab) (by omega) hb)
        h.cut_before_source
    · by_cases ha : e a = ell
      · change (if e a = ell then n else e a) <
          (if e b = ell then n else e b)
        rw [if_pos ha, if_neg hb]
        omega
      · simpa [projectMiddleClone, ha, hb] using hlt
  · intro a
    change projectMiddleClone ell n (e a) ∈ W.carrier ∧
      projectMiddleClone ell n (e a) ≠ ell
    by_cases ha : e a = ell
    · simp [projectMiddleClone, ha, h.source_in_carrier,
        Nat.ne_of_lt h.n_before]
    · simp [projectMiddleClone, ha, hIn a]
  · intro a b hab t
    by_cases ha : e a = ell
    · have hb : e b ≠ ell := by
        intro he
        exact hDist a b hab (ha.trans he.symm)
      have hCopyEdge : W.binary n (e b) t = W.binary ell (e b) t := by
        by_cases hlow : e b < ell
        · have hCut := hEarlier b a hab.symm hlow ha
          exact (h.copy_lower (e b) hCut t).1.symm
        · have hUpper : ell < e b := by omega
          exact (h.copy_upper (e b) hUpper t).1.symm
      calc
        W.binary (projectMiddleClone ell n (e a))
            (projectMiddleClone ell n (e b)) t =
          W.binary n (e b) t := by simp [projectMiddleClone,ha,hb]
        _ = W.binary ell (e b) t := hCopyEdge
        _ = P.binary a b t := by simpa [ha] using hBinary a b hab t
    · by_cases hb : e b = ell
      · have haNe : e a ≠ ell := ha
        have hCopyEdge : W.binary (e a) n t =
            W.binary (e a) ell t := by
          by_cases hlow : e a < ell
          · have hCut := hEarlier a b hab hlow hb
            exact (h.copy_lower (e a) hCut t).2.symm
          · have hUpper : ell < e a := by omega
            exact (h.copy_upper (e a) hUpper t).2.symm
        calc
          W.binary (projectMiddleClone ell n (e a))
              (projectMiddleClone ell n (e b)) t =
            W.binary (e a) n t := by simp [projectMiddleClone,haNe,hb]
          _ = W.binary (e a) ell t := hCopyEdge
          _ = P.binary a b t := by simpa [hb] using hBinary a b hab t
      · simpa [projectMiddleClone, ha, hb] using hBinary a b hab t
  · intro a t
    by_cases ha : e a = ell
    · calc
        W.unary (projectMiddleClone ell n (e a)) t =
          W.unary n t := by simp [projectMiddleClone,ha]
        _ = W.unary ell t := (h.same_unary t).symm
        _ = P.unary a t := by simpa [ha] using hUnary a t
    · simpa [projectMiddleClone,ha] using hUnary a t
  · intro a t
    by_cases ha : e a = ell
    · calc
        W.diagonal (projectMiddleClone ell n (e a)) t =
          W.diagonal n t := by simp [projectMiddleClone,ha]
        _ = W.diagonal ell t := (h.same_diagonal t).symm
        _ = P.diagonal a t := by simpa [ha] using hDiagonal a t
    · simpa [projectMiddleClone,ha] using hDiagonal a t

/-- The exact clone L-atoms make the corrected finite deletion age-test
automatic: if the structure without ell is forbidden-free, so is W.
No auxiliary E conditions and no upper-tail partial structure occur. -/
theorem MiddleCloneLData.avoidance_of_deletion
    {db du dd : Nat}
    {W : AgeTestModel db du dd} {n ell d : Nat}
    (h : MiddleCloneLData W n ell d)
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
        ⟨_,h.irred_copy_projects P hIrred e hCopy⟩

end SuccessorTree.V10

import SuccessorTree.V10.CommonSocleType

/-!
# Longest common full partial-type prefix

The v10 meet proof needs more than a comparison of binary traces:
it needs an actual largest common induced L+ predecessor. This file
constructs that predecessor at the level of complete finite types
from a fixed ambient partial structure C, with no abstract LevelTree
axioms or first-difference assumptions.

For any two vertices with the same level-zero partial type, there
is a unique largest common prefix up to a finite bound. If the bound
lies below both E free levels and the maximal prefix ends early, the
first differing coordinate has a concrete directed binary atomic
witness in one of the two orientations. Every other L+ atom agrees
by the common ambient/free-socle argument.

The remaining bridge is to identify these finite prefixes as genuine
Kpt predecessors and prove their maximum is the tree meet.
-/

namespace SuccessorTree.V10

/-- Equality at a longer complete L+ type prefix entails equality
at every shorter initial socle, including every E bit. -/
theorem fullPartialType_eq_at_smaller
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (v w small large : Nat) (h : small ≤ large)
    (heq : A.partialTypeAt large v = A.partialTypeAt large w) :
    A.partialTypeAt small v = A.partialTypeAt small w := by
  have heq' := congrArg
    (fun T : PartialTypeWithE large db du dd => T.restrict h) heq
  rw [A.partialTypeAt_restrict small large v h,
      A.partialTypeAt_restrict small large w h] at heq'
  exact heq'

/-- There is a largest common complete L+ prefix below any prescribed
finite bound, provided the two roots agree. -/
theorem exists_maximal_common_fullPrefix
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (v w bound : Nat)
    (hroot : A.partialTypeAt 0 v = A.partialTypeAt 0 w) :
    ∃ d : Nat, d ≤ bound ∧
      A.partialTypeAt d v = A.partialTypeAt d w ∧
      (d = bound ∨
        A.partialTypeAt (d + 1) v ≠ A.partialTypeAt (d + 1) w) := by
  induction bound with
  | zero =>
      exact ⟨0, Nat.le_refl 0, hroot, Or.inl rfl⟩
  | succ n ih =>
      obtain ⟨d, hd, hEq, hMax⟩ := ih
      rcases hMax with hEnd | hDiff
      · subst d
        by_cases hNext : A.partialTypeAt (n + 1) v =
            A.partialTypeAt (n + 1) w
        · exact ⟨n + 1, Nat.le_refl _, hNext, Or.inl rfl⟩
        · exact ⟨n, Nat.le_succ n, hEq, Or.inr hNext⟩
      · exact ⟨d, hd.trans (Nat.le_succ n), hEq, Or.inr hDiff⟩

/-- The maximal common prefix cut is unique. Thus the recursive
construction is canonical, not a choice of incompatible witnesses. -/
theorem maximal_common_fullPrefix_unique
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (v w bound d e : Nat)
    (hd : d ≤ bound)
    (he : e ≤ bound)
    (hdEq : A.partialTypeAt d v = A.partialTypeAt d w)
    (heEq : A.partialTypeAt e v = A.partialTypeAt e w)
    (hdMax : d = bound ∨
      A.partialTypeAt (d + 1) v ≠ A.partialTypeAt (d + 1) w)
    (heMax : e = bound ∨
      A.partialTypeAt (e + 1) v ≠ A.partialTypeAt (e + 1) w) :
    d = e := by
  have hde : d ≤ e := by
    by_contra hn
    have hed : e < d := by omega
    rcases heMax with hTop | hDiff
    · omega
    · exact hDiff (fullPartialType_eq_at_smaller A v w
        (e + 1) d (by omega) hdEq)
  have hed : e ≤ d := by
    by_contra hn
    have hde' : d < e := by omega
    rcases hdMax with hTop | hDiff
    · omega
    · exact hDiff (fullPartialType_eq_at_smaller A v w
        (d + 1) e (by omega) heEq)
  omega

/-- If complete types agree through d but differ through d+1,
and both original vertices have that coordinate in their E socles,
the first difference is witnessed by a directed binary L-atom at
position d. Both orientations and false values are included. -/
theorem binary_witness_of_first_fullPrefix_difference
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (v w d : Nat)
    (hv : d + 1 ≤ A.freeLevel v)
    (hw : d + 1 ≤ A.freeLevel w)
    (hroot : A.partialTypeAt 0 v = A.partialTypeAt 0 w)
    (hEq : A.partialTypeAt d v = A.partialTypeAt d w)
    (hDiff : A.partialTypeAt (d + 1) v ≠
      A.partialTypeAt (d + 1) w) :
    (∃ r : Fin db, A.L.binary d v r ≠ A.L.binary d w r) ∨
    (∃ r : Fin db, A.L.binary v d r ≠ A.L.binary w d r) := by
  classical
  have hPrevious : SameAmbientCrossType A v w d :=
    (sameAmbient_partialType_eq_iff_cross A v w d
      (by omega) (by omega) hroot).1 hEq
  by_contra hNoWitness
  have hForward : ∀ r : Fin db,
      A.L.binary d v r = A.L.binary d w r := by
    intro r
    by_contra hn
    exact hNoWitness (Or.inl ⟨r, hn⟩)
  have hBackward : ∀ r : Fin db,
      A.L.binary v d r = A.L.binary w d r := by
    intro r
    by_contra hn
    exact hNoWitness (Or.inr ⟨r, hn⟩)
  have hCross : SameAmbientCrossType A v w (d + 1) := by
    constructor
    · intro i r
      by_cases hi : i.val < d
      · exact hPrevious.1 ⟨i.val, hi⟩ r
      · have heq : i.val = d := by omega
        simpa only [heq] using hForward r
    · intro i r
      by_cases hi : i.val < d
      · exact hPrevious.2 ⟨i.val, hi⟩ r
      · have heq : i.val = d := by omega
        simpa only [heq] using hBackward r
  exact hDiff ((sameAmbient_partialType_eq_iff_cross A v w
    (d + 1) hv hw hroot).2 hCross)

/-- Below both free levels, a maximal full common prefix either
reaches the chosen bound or ends at a concrete first differing
directed binary atom.

This supplies the first difference without assuming its coordinate
or an upper-generation charge. -/
theorem exists_maximal_common_fullPrefix_with_binary_witness
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (v w bound : Nat)
    (hv : bound ≤ A.freeLevel v)
    (hw : bound ≤ A.freeLevel w)
    (hroot : A.partialTypeAt 0 v = A.partialTypeAt 0 w) :
    ∃ d : Nat, d ≤ bound ∧
      A.partialTypeAt d v = A.partialTypeAt d w ∧
      (d = bound ∨
        (∃ r : Fin db, A.L.binary d v r ≠ A.L.binary d w r) ∨
        (∃ r : Fin db, A.L.binary v d r ≠ A.L.binary w d r)) := by
  obtain ⟨d, hd, hEq, hMax⟩ :=
    exists_maximal_common_fullPrefix A v w bound hroot
  refine ⟨d, hd, hEq, ?_⟩
  by_cases hEnd : d = bound
  · exact Or.inl hEnd
  · have hlt : d < bound := by omega
    have hDiff : A.partialTypeAt (d + 1) v ≠
        A.partialTypeAt (d + 1) w := by
      rcases hMax with hTop | hNext
      · exact False.elim (hEnd hTop)
      · exact hNext
    exact Or.inr (binary_witness_of_first_fullPrefix_difference
      A v w d (by omega) (by omega) hroot hEq hDiff)

end SuccessorTree.V10

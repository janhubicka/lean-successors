import SuccessorTree.V10.LocalAgeCanonicalInputs
import SuccessorTree.V10.LocalAgeNeutralFullPrefix
import Mathlib.Tactic

/-!
# The neutral gap map's crossing successor edge

When the source successor base lies below the inserted level ell, all of
its parameters lie still lower (by the ACTUAL S-tree axiom S1). Thus both
the base and its parameter list are fixed by neutral insertion.

If the successor target has level below ell it too is fixed. If the target
has level exactly ell, the original target is the level-ell prefix of its
neutral inserted image at level ell+1, as is seen directly from the complete
L+ partial type and the inserted E-cuts. The OLD successor therefore
remains a successor of the mapped base and maps below the shifted target,
which is precisely the weak rather than strong successor clause.

This resolves the subtle n=ell-1 boundary needed to build a ShapeMap.
No canonical crossing condition is postulated.
-/

namespace SuccessorTree.V10

/-- At the skipped level itself, every admissible original node is an
ACTUAL predecessor of its neutral inserted image, because all its L+ atoms
through ell are unchanged and its image acquires one extra socle vertex. -/
theorem neutralKptSkip_self_prefix_at_gap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (b : AdmissibleKptNode family)
    (hLevel : b.1.1 = ell) :
    b ≤ neutralKptSkip family ell hellPos b := by
  have hhi : ell ≤ b.1.1 := by omega
  obtain ⟨A, v, hell, hv, hAvoid, hRaw, hImage⟩ :=
    neutralKptImage_isImage family ell hellPos b hhi
  have hFree : A.freeLevel v = ell := by
    have ht := congrArg Sigma.fst hRaw
    change b.1.1 = A.freeLevel v at ht
    omega
  let B := neutralInsert A ell hell hellPos
  have hAType : b.1 =
      (⟨ell, A.partialTypeAt ell v⟩ :
        RawPartialTypeNode db du dd) := by
    calc
      b.1 = A.rawTypeAtFree v := hRaw
      _ = (⟨ell, A.partialTypeAt ell v⟩ :
        RawPartialTypeNode db du dd) := by
        change
          (⟨A.freeLevel v,A.partialTypeAt (A.freeLevel v) v⟩ :
            RawPartialTypeNode db du dd) =
          (⟨ell,A.partialTypeAt ell v⟩ :
            RawPartialTypeNode db du dd)
        rw [hFree]
  have hBT : B.partialTypeAt ell (insertAddress ell v) =
      A.partialTypeAt ell v :=
    neutralInsert_type_below_gap A ell hell hellPos v ell hv le_rfl
  have hShiftFree : B.freeLevel (insertAddress ell v) = ell+1 := by
    have ht := neutralInsert_freeLevel_old A ell hell hellPos v hv
    have hn : ¬ A.freeLevel v < ell := by omega
    have hf : B.freeLevel (insertAddress ell v) =
        A.freeLevel v + 1 := by
      simpa only [B, if_neg hn] using ht
    omega
  have hCut : ell ≤ B.freeLevel (insertAddress ell v) := by omega
  have hPrefix :
      b.1 ≤ B.rawTypeAtFree (insertAddress ell v) := by
    rw [hAType, ← hBT]
    exact rawPartialType_prefix_of_cut B
      (insertAddress ell v) ell hCut
  have hImageEq :
      (neutralKptSkip family ell hellPos b).1 =
        B.rawTypeAtFree (insertAddress ell v) := by
    rw [neutralKptSkip_above family ell hellPos b hhi]
    exact hImage
  change b.1 ≤ (neutralKptSkip family ell hellPos b).1
  rw [hImageEq]
  exact hPrefix

/-- Every original successor based strictly below the gap satisfies
the weak mapped-successor clause. The difficult boundary n=ell-1 is
covered by the literal source-prefix-of-shifted-target theorem above. -/
theorem neutralKptSkip_weak_succ_below_gap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : AdmissibleKptSigma family}
    (hSucc : (admissibleKptSTree family).succ a p c = some b)
    (hBaseLow : a.1.1 < ell) :
    ∃ d : AdmissibleKptNode family,
      (admissibleKptSTree family).succ
        (neutralKptSkip family ell hellPos a)
        (p.map (neutralKptSkip family ell hellPos)) c = some d ∧
      d ≤ neutralKptSkip family ell hellPos b := by
  have hOldCover := (admissibleKptSTree family).covBy_of_succ_eq_some hSucc
  have hBLevel : b.1.1 = a.1.1 + 1 := by
    have h := LevelTree.covBy_level_eq hOldCover
    change b.1.1 = a.1.1 + 1 at h
    exact h
  have hParam : ∀ x ∈ p, neutralKptSkip family ell hellPos x = x := by
    intro x hx
    have hlt := (admissibleKptSTree family).parameter_level_lt hSucc hx
    change x.1.1 < a.1.1 at hlt
    exact neutralKptSkip_fixed_below family ell hellPos x (by omega)
  have hMap : p.map (neutralKptSkip family ell hellPos) = p := by
    induction p with
    | nil => rfl
    | cons x xs ih =>
        have hx : neutralKptSkip family ell hellPos x = x :=
          hParam x (by simp)
        have hxs : ∀ y ∈ xs, neutralKptSkip family ell hellPos y = y := by
          intro y hy
          exact hParam y (by simp [hy])
        simp only [List.map_cons, hx]
        rw [ih hxs]
  have hA : neutralKptSkip family ell hellPos a = a :=
    neutralKptSkip_fixed_below family ell hellPos a hBaseLow
  have hBOld : b ≤ neutralKptSkip family ell hellPos b := by
    by_cases hbLow : b.1.1 < ell
    · rw [neutralKptSkip_fixed_below family ell hellPos b hbLow]
    · have hbEq : b.1.1 = ell := by omega
      exact neutralKptSkip_self_prefix_at_gap family ell hellPos b hbEq
  refine ⟨b, ?_, hBOld⟩
  simpa only [hA, hMap] using hSucc

end SuccessorTree.V10

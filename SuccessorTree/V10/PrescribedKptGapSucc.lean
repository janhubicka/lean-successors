import SuccessorTree.V10.PrescribedKptFullPrefix
import SuccessorTree.V10.LocalAgeNeutralGapSucc
import Mathlib.Tactic

/-!
# The prescribed gap map's weak successor clause below the gap

At level ell the original node is a genuine predecessor of its inserted
image in both branches. If a successor base is below ell, S1 puts every
parameter below the base, so the base and all parameters are fixed.
The original successor is then the required witness below its image.

This proves the crossing boundary without asserting the false equality
between the old successor and its image one level higher. The successor
parameter transport above the gap is a separate obligation.
-/

namespace SuccessorTree.V10.PrescribedBoringData

variable {ell db du dd : Nat}
variable (F : PrescribedBoringData ell db du dd)
variable (family : List (NormalizedForbidden db du dd))
variable (hB3 : F.CorrectedB3 family)
variable (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
  (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
variable (hPos : 0 < ell)

/-- At the omitted level itself, the source remains a complete predecessor
of its image, whether the selected insertion is prescribed or neutral. -/
theorem prescribedKptSkip_self_prefix_at_gap
    (b : AdmissibleKptNode family) (hLevel : b.1.1 = ell) :
    b ≤ F.prescribedKptSkip family hB3 hTargets hPos b := by
  have hhi : ell ≤ b.1.1 := by omega
  by_cases hMatch : F.HasCompatibleSource (b.1.2.restrict hhi)
  · rw [F.prescribedKptSkip_matching family hB3 hTargets hPos b hhi hMatch]
    exact F.matchingKptImage_self_prefix_at_gap family hB3 hTargets hPos
      b hLevel hMatch
  · rw [F.prescribedKptSkip_neutral family hB3 hTargets hPos b hhi hMatch]
    have h := neutralKptSkip_self_prefix_at_gap family ell hPos b hLevel
    rw [neutralKptSkip_above family ell hPos b hhi] at h
    exact h

/-- Weak successor preservation for every base below ell, including the
crossing edge ell-1 -> ell. The witness is the original successor, not the
image of that successor. Its parameter bounds come from the actual S-tree. -/
theorem prescribedKptSkip_weak_succ_below_gap
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : AdmissibleKptSigma family}
    (hSucc : (admissibleKptSTree family).succ a p c = some b)
    (hBaseLow : a.1.1 < ell) :
    ∃ d : AdmissibleKptNode family,
      (admissibleKptSTree family).succ
        (F.prescribedKptSkip family hB3 hTargets hPos a)
        (p.map (F.prescribedKptSkip family hB3 hTargets hPos)) c = some d ∧
      d ≤ F.prescribedKptSkip family hB3 hTargets hPos b := by
  have hOldCover := (admissibleKptSTree family).covBy_of_succ_eq_some hSucc
  have hBLevel : b.1.1 = a.1.1+1 := by
    have h := LevelTree.covBy_level_eq hOldCover
    change b.1.1 = a.1.1+1 at h
    exact h
  have hParam : ∀ x ∈ p, F.prescribedKptSkip family hB3 hTargets hPos x = x := by
    intro x hx
    have hlt := (admissibleKptSTree family).parameter_level_lt hSucc hx
    change x.1.1 < a.1.1 at hlt
    exact F.prescribedKptSkip_fixed_below family hB3 hTargets hPos x (by omega)
  have hMapAux : ∀ xs : List (AdmissibleKptNode family),
      (∀ x ∈ xs, F.prescribedKptSkip family hB3 hTargets hPos x = x) →
      xs.map (F.prescribedKptSkip family hB3 hTargets hPos) = xs := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons x xs ih =>
        intro hFix
        have hx := hFix x (by simp)
        have hxs : ∀ y ∈ xs, F.prescribedKptSkip family hB3 hTargets hPos y = y := by
          intro y hy
          exact hFix y (by simp [hy])
        simp only [List.map_cons, hx]
        rw [ih hxs]
  have hMap : p.map (F.prescribedKptSkip family hB3 hTargets hPos) = p :=
    hMapAux p hParam
  have hA := F.prescribedKptSkip_fixed_below family hB3 hTargets hPos a hBaseLow
  have hBOld : b ≤ F.prescribedKptSkip family hB3 hTargets hPos b := by
    by_cases hbLow : b.1.1 < ell
    · rw [F.prescribedKptSkip_fixed_below family hB3 hTargets hPos b hbLow]
    · exact F.prescribedKptSkip_self_prefix_at_gap family hB3 hTargets hPos b (by omega)
  refine ⟨b, ?_, hBOld⟩
  simpa only [hA, hMap] using hSucc

end SuccessorTree.V10.PrescribedBoringData

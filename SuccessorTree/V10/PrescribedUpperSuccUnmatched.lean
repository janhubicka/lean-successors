import SuccessorTree.V10.PrescribedUpperSuccMatching
import SuccessorTree.V10.LocalAgeNeutralUpperSucc
import Mathlib.Tactic

/-!
# Exact upper successor in the unmatched branch

When b is an upper successor with no compatible prescribed ell-socle,
all upper type vertices in any ambient finite representative of b are
unmatched, since they have the SAME ordinary ell-socle. The canonical
parameter is either empty or precisely the old vertex n of that
representative. On this parameter the prescribed map is consequently
the verified neutral map (or both maps fix it below ell).

The source parent a is an ell-prefix of b, so it is also unmatched.
The fully checked neutral upper successor identity can therefore be
rewritten to the actual prescribed map, without a second finite proof.
-/

namespace SuccessorTree.V10

theorem PrescribedBoringData.prescribedKptSkip_eq_neutral_of_no_match
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a : AdmissibleKptNode family)
    (hlev : ell ≤ a.1.1)
    (hNone : ¬ F.HasCompatibleSource (a.1.2.restrict hlev)) :
    F.prescribedKptSkip family hB3 hTargets hPos a =
      neutralKptSkip family ell hPos a := by
  rw [F.prescribedKptSkip_neutral family hB3 hTargets hPos
    a hlev hNone]
  exact (neutralKptSkip_above family ell hPos a hlev).symm

theorem PrescribedBoringData.prescribedKptSkip_eq_neutral_below
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a : AdmissibleKptNode family) (ha : a.1.1 < ell) :
    F.prescribedKptSkip family hB3 hTargets hPos a =
      neutralKptSkip family ell hPos a := by
  rw [F.prescribedKptSkip_fixed_below family hB3 hTargets hPos a ha,
    neutralKptSkip_fixed_below family ell hPos a ha]

/-- All original vertices of A have the same ordinary ell-socle.
If the source type of v is unmatched, every level-ell source type
extracted from any ordinary u is unmatched. -/
theorem PrescribedBoringData.no_match_same_ambient
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat)
    (hNone : ¬ F.HasCompatibleSource (A.partialTypeAt ell v))
    (u : Nat) :
    ¬ F.HasCompatibleSource (A.partialTypeAt ell u) := by
  intro hSome
  obtain ⟨S,hS,hComp⟩ := hSome
  exact hNone ⟨S,hS,
    sameOrdinaryAtCut_trans hComp
      (sameOrdinaryAtCut_sameAmbient A ell u v)⟩

/-- On every original vertex of an unmatched finite representative,
the total candidate uses the neutral branch wherever it is active.
The property holds also for a positive-level canonical parameter,
not just for the distinguished vertex representing the successor. -/
theorem PrescribedBoringData.prescribedKptSkip_neutral_on_ambient
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (v : Nat)
    (hNone : ¬ F.HasCompatibleSource (A.partialTypeAt ell v))
    (u : Nat) (hu : u < A.size) :
    F.prescribedKptSkip family hB3 hTargets hPos
      (⟨A.rawTypeAtFree u,⟨A,u,hu,hAvoid,rfl⟩⟩ :
        AdmissibleKptNode family) =
      neutralKptSkip family ell hPos
      (⟨A.rawTypeAtFree u,⟨A,u,hu,hAvoid,rfl⟩⟩ :
        AdmissibleKptNode family) := by
  let src : AdmissibleKptNode family :=
    ⟨A.rawTypeAtFree u,⟨A,u,hu,hAvoid,rfl⟩⟩
  by_cases hLow : A.freeLevel u < ell
  · exact F.prescribedKptSkip_eq_neutral_below family hB3
      hTargets hPos src hLow
  · have hlev : ell ≤ src.1.1 := by
      change ell ≤ A.freeLevel u
      omega
    have hRestr : src.1.2.restrict hlev = A.partialTypeAt ell u := by
      change (A.partialTypeAt (A.freeLevel u) u).restrict hlev =
        A.partialTypeAt ell u
      exact A.partialTypeAt_restrict ell (A.freeLevel u) u hlev
    have hn : ¬ F.HasCompatibleSource (src.1.2.restrict hlev) := by
      rw [hRestr]
      exact F.no_match_same_ambient A v hNone u
    exact F.prescribedKptSkip_eq_neutral_of_no_match family hB3
      hTargets hPos src hlev hn

/-- Exact canonical upper successor transport in the neutral fallback
case, with the genuinely mapped canonical parameter list. -/
theorem PrescribedBoringData.prescribedKptSkip_succ_unmatched_above
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : AdmissibleKptSigma family}
    (hSucc : (admissibleKptSTree family).succ a p c = some b)
    (hBaseHigh : ell ≤ a.1.1)
    (hNoneB : ¬ F.HasCompatibleSource
      (b.1.2.restrict (by
        have hCover := (admissibleKptSTree family).covBy_of_succ_eq_some hSucc
        have hh : a.1.1 ≤ b.1.1 := hCover.le.1
        omega))) :
    (admissibleKptSTree family).succ
      (F.prescribedKptSkip family hB3 hTargets hPos a)
      (p.map (F.prescribedKptSkip family hB3 hTargets hPos)) c =
      some (F.prescribedKptSkip family hB3 hTargets hPos b) := by
  let n := a.1.1
  have hSource : IsCanonicalKptStep family a p c.1 b :=
    canonicalKptSucc_spec family (by
      change canonicalKptSucc family a p c.1 = some b
      exact hSucc)
  have hOldCover : a ⋖ b :=
    (admissibleKptSTree family).covBy_of_succ_eq_some hSucc
  have hbLev : b.1.1 = n+1 := by
    have h := LevelTree.covBy_level_eq hOldCover
    change b.1.1 = a.1.1+1 at h
    exact h
  have hbHigh : ell ≤ b.1.1 := by omega
  have hNone : ¬ F.HasCompatibleSource (b.1.2.restrict hbHigh) :=
    hNoneB
  have haHigh : ell ≤ a.1.1 := hBaseHigh
  have hNoneA : ¬ F.HasCompatibleSource (a.1.2.restrict haHigh) := by
    intro hSome
    have hCo := F.compatibleSource_iff_of_Kpt_prefix b a hOldCover.le
      haHigh
    exact hNone (hCo.1 hSome)
  have hMapA := F.prescribedKptSkip_eq_neutral_of_no_match family
    hB3 hTargets hPos a haHigh hNoneA
  have hMapB := F.prescribedKptSkip_eq_neutral_of_no_match family
    hB3 hTargets hPos b hbHigh hNone
  obtain ⟨A,v,hv,hAvoid,hRaw⟩ := b.2
  have hFree : A.freeLevel v = n+1 := by
    have h := congrArg Sigma.fst hRaw
    change b.1.1 = A.freeLevel v at h
    omega
  have hn : n < A.size := by
    have h := A.freeLevel_le v
    omega
  have hFull : b.1.2 = A.partialTypeAt b.1.1 v :=
    record_eq_of_rawTypeAtFree b.1.2 A v hRaw
  have hEll : b.1.2.restrict hbHigh = A.partialTypeAt ell v := by
    rw [hFull]
    exact A.partialTypeAt_restrict ell b.1.1 v hbHigh
  have hAmbientNone : ¬ F.HasCompatibleSource (A.partialTypeAt ell v) := by
    rw [←hEll]
    exact hNone
  have hInputs :=
    canonicalKptStep_inputs_of_ambient family A v n hv hAvoid
      hFree hSource hRaw
  let par : AdmissibleKptNode family :=
    ⟨A.rawTypeAtFree n,⟨A,n,hn,hAvoid,rfl⟩⟩
  have hParam : p = (if A.freeLevel n = 0 then [] else [par]) :=
    hInputs.2
  have hParamEq :
      p.map (F.prescribedKptSkip family hB3 hTargets hPos) =
      p.map (neutralKptSkip family ell hPos) := by
    rw [hParam]
    by_cases hz : A.freeLevel n = 0
    · simp [hz]
    · have hParEq :
          F.prescribedKptSkip family hB3 hTargets hPos par =
            neutralKptSkip family ell hPos par :=
        F.prescribedKptSkip_neutral_on_ambient family hB3 hTargets
          hPos A hAvoid v hAmbientNone n hn
      simp only [if_neg hz, List.map_cons, List.map_nil]
      rw [hParEq]
  have hNeutralSucc :=
    neutralKptSkip_weak_succ_above_gap family ell hPos
      hSucc hBaseHigh
  rw [hMapA,hMapB,hParamEq]
  exact hNeutralSucc

end SuccessorTree.V10

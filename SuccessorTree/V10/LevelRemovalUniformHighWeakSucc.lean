import SuccessorTree.V10.LevelRemovalUniformLowWeakSucc
import SuccessorTree.V10.LevelRemovalUniformParameter
import SuccessorTree.V10.LevelRemovalCanonicalStepAssembly
import SuccessorTree.V10.LevelRemovalDeletedWeakTarget
import SuccessorTree.V10.LevelRemovalHighStepSafety
import Mathlib.Tactic

/-!
# Genuine upper weak successors of the intrinsic M2 deletion candidate

The checked pieces already give the intrinsic admissible candidate D,
complete raw deletion on all source levels, full optional parameter
transport, valid E columns, the same terminal Sigma letter and
admissibility of the deleted weak image successor.

For an actual source step whose base is at or above the first
affected level, use F's *weak* successor d ≤ F(b), delete the ordinary
coordinate m from its genuine full record, and assemble an ACTUAL
canonical step from D(a) to a deleted admissible d' ≤ D(b).
The sharp disjunction (m<k or f<m) is the proved HighStepSafety
theorem, not an extra hypothesis. All successor inputs are transported
elementwise by D, including the empty/singleton case.

This is the missing upper branch of the ShapeMap weak-successor law.
It does not assume the M2 axiom, a ShapeMap structure on D, or the
corrected finite L-only age-necessity argument.
-/

namespace SuccessorTree.V10

/-- Equality of complete raw Kpt nodes may be transported through
coordinate deletion; the proof argument establishing m<cut is
irrelevant. -/
private theorem rawDelete_congr
    {db du dd : Nat} {U V : RawPartialTypeNode db du dd}
    {m : Nat} (hu : m < U.1) (hv : m < V.1)
    (h : U = V) :
    rawPartialTypeDeleteAt U m hu =
      rawPartialTypeDeleteAt V m hv := by
  cases h
  rfl

/-- Upper-base weak successor preservation for the actual intrinsic
uniform M2 deletion function, with no additional age or deletion
guard hypotheses. -/
theorem uniformGapDeletedKpt_high_weak_succ
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ a b : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (p : List (AdmissibleKptNode family))
    (c : AdmissibleKptSigma family)
    (hSucc : (admissibleKptSTree family).succ a p c = some b)
    (hHigh : LevelTree.lev a₀ ≤ LevelTree.lev a) :
    ∃ d' : AdmissibleKptNode family,
      (admissibleKptSTree family).succ
        (uniformGapDeletedKpt family F q₀ a₀ hprev hgap a)
        (p.map (uniformGapDeletedKpt family F q₀ a₀ hprev hgap)) c =
          some d' ∧
      d' ≤ uniformGapDeletedKpt family F q₀ a₀ hprev hgap b := by
  classical
  let D := uniformGapDeletedKpt family F q₀ a₀ hprev hgap
  let m := LevelTree.lev (F a₀) - 1
  obtain ⟨d,hMapped,hBelow⟩ := F.weak_succ' hSucc
  have hCanonical :
      IsCanonicalKptStep family (F a) (p.map F) c.1 d := by
    apply canonicalKptSucc_spec family
    simpa only [admissibleKptSTree_succ_eq] using hMapped
  obtain ⟨ell,f,hf,Q,hBase,hTarget,hLetter,hValid,hOldParam,hGate⟩ :=
    hCanonical
  have hFBaseLevel : LevelTree.lev (F a) = ell := by
    have hh := congrArg Sigma.fst hBase
    exact hh
  have hFLevelLe : LevelTree.lev (F a₀) ≤ ell := by
    have hh := shapeMap_level_le_of_level_le family F hHigh
    rw [hFBaseLevel] at hh
    exact hh
  have hEllPos : 0 < ell := by
    omega
  cases ell with
  | zero =>
      omega
  | succ k =>
      have hmPos : 0 < m := by
        dsimp [m]
        omega
      have hm : m < k + 1 := by
        dsimp [m]
        omega
      have hSafety : m < k ∨ f < m :=
        mapped_upper_canonical_step_safe_for_gap
          family F q₀ a₀ a b p c hprev hgap hHigh hSucc
          k f hf Q hBase hOldParam
      have hBHigh : LevelTree.lev a₀ ≤ LevelTree.lev b := by
        have hCov :=
          (admissibleKptSTree family).covBy_of_succ_eq_some hSucc
        have hBLevel := LevelTree.covBy_level_eq hCov
        omega
      obtain ⟨hmFa,hDaRaw⟩ :=
        uniformGapDeletedKpt_above_raw family F q₀ a₀
          hprev hgap a hHigh
      obtain ⟨hmFb,hDbRaw⟩ :=
        uniformGapDeletedKpt_above_raw family F q₀ a₀
          hprev hgap b hBHigh
      have hmd : m < d.1.1 := by
        have hh := congrArg Sigma.fst hTarget
        change d.1.1 = k + 2 at hh
        omega
      obtain ⟨d',hDPrimeRaw,hDPrimeLe⟩ :=
        deleted_predecessor_node_of_admissible_upper
          family d (F b) (D b) hBelow m hmd hDbRaw
      have hDBase :
          (D a).1 =
            (⟨k, (Q.deleteOrdinary m (by omega)).restrict
                (Nat.le_succ k)⟩ : RawPartialTypeNode db du dd) := by
        have hBaseDelete :
            rawPartialTypeDeleteAt (F a).1 m hmFa =
              rawPartialTypeDeleteAt
                (⟨k + 1, Q.restrict (Nat.le_succ (k + 1))⟩ :
                  RawPartialTypeNode db du dd) m (by omega) :=
          rawDelete_congr hmFa (by omega) hBase
        calc
          (D a).1 = rawPartialTypeDeleteAt (F a).1 m hmFa :=
            hDaRaw
          _ = rawPartialTypeDeleteAt
                (⟨k + 1, Q.restrict (Nat.le_succ (k + 1))⟩ :
                  RawPartialTypeNode db du dd) m (by omega) :=
            hBaseDelete
          _ = (⟨k, (Q.deleteOrdinary m (by omega)).restrict
                  (Nat.le_succ k)⟩ :
                RawPartialTypeNode db du dd) := by
            change
              (⟨k,
                (Q.restrict (Nat.le_succ (k+1))).deleteOrdinary
                  m (by omega)⟩ : RawPartialTypeNode db du dd) = _
            apply congrArg (Sigma.mk k)
            simpa only [Nat.add_sub_cancel] using
              (Q.deleteOrdinary_restrict (Nat.le_succ (k+1))
                m (by omega)).symm
      have hDTarget :
          d'.1 =
            (⟨k + 1, Q.deleteOrdinary m (by omega)⟩ :
              RawPartialTypeNode db du dd) := by
        have hTargetDelete :
            rawPartialTypeDeleteAt d.1 m hmd =
              rawPartialTypeDeleteAt
                (⟨k + 2,Q⟩ : RawPartialTypeNode db du dd)
                m (by omega) :=
          rawDelete_congr hmd (by omega) hTarget
        calc
          d'.1 = rawPartialTypeDeleteAt d.1 m hmd := hDPrimeRaw
          _ = rawPartialTypeDeleteAt
                (⟨k + 2,Q⟩ : RawPartialTypeNode db du dd)
                m (by omega) := hTargetDelete
          _ = (⟨k + 1,Q.deleteOrdinary m (by omega)⟩ :
                RawPartialTypeNode db du dd) := by
            rfl
      have hNewParam :
          (p.map D).map (fun x => x.1) =
            ((p.map F).map (fun x => x.1)).map
              (rawPartialTypeDeleteIfAbove m) := by
        simpa only [rawPartialTypeDeleteIfAbove, List.map_map]
          using
            (uniformGapDeletedKpt_raw_parameter_list family
              F q₀ a₀ hprev hgap p)
      have hDeletedStep :
          IsCanonicalKptStep family (D a) (p.map D) c.1 d' :=
        canonicalKptStep_of_deleted_record
          family Q f hf hValid hGate
          m hm hmPos hSafety
          (D a) d' (p.map F) (p.map D) c.1
          hDBase hDTarget hLetter hOldParam hNewParam
      have hNewSucc :
          (admissibleKptSTree family).succ (D a) (p.map D) c =
            some d' := by
        change canonicalKptSucc family (D a) (p.map D) c.1 =
          some d'
        exact canonicalKptSucc_eq_some_of_step family hDeletedStep
      exact ⟨d',hNewSucc,hDPrimeLe⟩

/-- The intrinsic piecewise deleted-image function weakly preserves
EVERY genuine successor, including the crossing edge and successors
based at or above the affected source level. No M2 axiom is used. -/
theorem uniformGapDeletedKpt_weak_succ
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : AdmissibleKptSigma family}
    (hSucc : (admissibleKptSTree family).succ a p c = some b) :
    ∃ d' : AdmissibleKptNode family,
      (admissibleKptSTree family).succ
        (uniformGapDeletedKpt family F q₀ a₀ hprev hgap a)
        (p.map (uniformGapDeletedKpt family F q₀ a₀ hprev hgap)) c =
          some d' ∧
      d' ≤ uniformGapDeletedKpt family F q₀ a₀ hprev hgap b := by
  by_cases hLow : LevelTree.lev a < LevelTree.lev a₀
  · exact uniformGapDeletedKpt_low_weak_succ
      family F q₀ a₀ a b hprev hgap p c hSucc hLow
  · exact uniformGapDeletedKpt_high_weak_succ
      family F q₀ a₀ a b hprev hgap p c hSucc
      (Nat.le_of_not_gt hLow)

end SuccessorTree.V10

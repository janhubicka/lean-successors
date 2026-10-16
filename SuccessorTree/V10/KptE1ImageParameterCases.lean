import SuccessorTree.V10.KptE1SourceParameterCases
import Mathlib.Tactic

/-!
# Genuine target successor cuts have a canonical source preimage

The concrete Kpt target successor has an empty or singleton canonical
parameter. The image of the source list under a shape map has the same
length. For a root-preserving shape map the empty cut pulls back to
zero; for a singleton parameter it pulls back to the precise level of
that source parameter, strictly below the source predecessor's level.

This is the finite E1 cut choice needed before applying the checked
padded source admissibility construction, not an additional E1 axiom.
-/

namespace SuccessorTree.V10

/-- Root preservation in the actual Kpt monoid makes the
strictly increasing shape-level map fix level zero. -/
theorem kptShapeLevelMap_zero_of_mem
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hF : F ∈ KptM family)
    (a : AdmissibleKptNode family) :
    kptShapeLevelMap family F 0 = 0 := by
  let root := LevelTree.ancestor a 0 (Nat.zero_le _)
  have hr : LevelTree.lev root = 0 :=
    LevelTree.level_ancestor a 0 (Nat.zero_le _)
  have hLevel :
      kptShapeLevelMap family F 0 = LevelTree.lev (F root) := by
    simpa only [hr] using kptShapeLevelMap_eq family F root
  exact hLevel.trans (hF root hr)

/-- An actual target canonical parameter list determines either
an empty source cut or a singleton source parameter. The positive
source cut has its exact target shape level and is strictly lower
than the predecessor. No arbitrary image-parameter is assumed. -/
theorem kptE1_image_parameter_cases
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hF : F ∈ KptM family)
    (a : AdmissibleKptNode family)
    {ell : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (g : Nat) (hg : g ≤ ell)
    (p : List (AdmissibleKptNode family))
    (hLevel :
      ell = kptShapeLevelMap family F (LevelTree.lev a))
    (hGate : g = 0 ∨ g < ell)
    (hTargetParameter :
      ((p.map F).map (fun x => x.1)) =
        (Q.canonicalParameterRecord g hg).toList) :
    (p = [] ∧ g = kptShapeLevelMap family F 0) ∨
    (∃ x : AdmissibleKptNode family,
      p = [x] ∧
      g = kptShapeLevelMap family F (LevelTree.lev x) ∧
      0 < LevelTree.lev x ∧ LevelTree.lev x < LevelTree.lev a) := by
  have hZero := kptShapeLevelMap_zero_of_mem family F hF a
  have hEmpty :=
    kptImageParameter_empty_iff_cut_zero family F Q g hg p hTargetParameter
  by_cases hp : p = []
  · left
    refine ⟨hp, ?_⟩
    have hg0 : g = 0 := hEmpty.mp hp
    simpa [hZero] using hg0
  · right
    have hgNonzero : g ≠ 0 := by
      intro hz
      exact hp (hEmpty.mpr hz)
    have hLen : p.length = 1 := by
      have hh := congrArg List.length hTargetParameter
      simpa [PartialTypeWithE.canonicalParameterRecord, hgNonzero] using hh
    cases p with
    | nil => exact False.elim (hp rfl)
    | cons x xs =>
        cases xs with
        | nil =>
            have hCut :
                kptShapeLevelMap family F (LevelTree.lev x) = g :=
              kptImageParameter_singleton_cut family F Q g hg x hTargetParameter
            have hPos : 0 < LevelTree.lev x :=
              kptImageParameter_singleton_source_positive family F hF Q g hg x
                hTargetParameter
            have hglt : g < ell := by
              rcases hGate with hZero' | hLess
              · exact False.elim (hgNonzero hZero')
              · exact hLess
            have hlt : LevelTree.lev x < LevelTree.lev a := by
              by_contra hNot
              have hle : LevelTree.lev a ≤ LevelTree.lev x :=
                Nat.le_of_not_gt hNot
              have hMon :=
                (kptShapeLevelMap_strictMono family F).monotone hle
              rw [←hLevel, hCut] at hMon
              omega
            exact ⟨x, rfl, hCut.symm, hPos, hlt⟩
        | cons y ys =>
            simp at hLen

end SuccessorTree.V10

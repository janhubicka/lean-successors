import SuccessorTree.FreeAncestralM2Gap
import SuccessorTree.FreeAncestralM2InnerShape
import Mathlib.Tactic

/-! # Complete M2 factorisation for the free ancestral tree -/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat}
variable [Fintype Label] [Nonempty Label]

theorem free_m2_exists
    (n : Nat)
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (a : Node Label arity)
    (ha : a.level = n)
    (hpos : 0 < (F a).level)
    (hskip : F.Skips ((F a).level - 1)) :
    ∃ F1 F2 :
        ShapeMap (freeSTree (Label := Label) (arity := arity)),
      F2.SkipsOnly ((F a).level - 1) ∧
      ∀ x : Node Label arity,
        x.level ≤ n → F2 (F1 x) = F x := by
  let h : Nat := (F a).level - 1
  have hFa : (F a).level = h + 1 := by
    dsimp [h]
    omega
  have hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1 := by
    intro x hx
    calc
      (F x).level = (F a).level := by
        apply F.level_eq_of_level_eq
        exact hx.trans ha.symm
      _ = h + 1 := hFa
  have hskip' : F.Skips h := by
    simpa [h] using hskip
  let F1 :=
    m2InnerShapeMap F n h hskip' hlevel
  let choose :=
    m2GapChoice F n h hlevel
  let F2 :
      ShapeMap (freeSTree (Label := Label) (arity := arity)) :=
    oneGapShapeMap h choose
  refine ⟨F1, F2, ?_, ?_⟩
  · simpa [F2, h] using
      oneGapShapeMap_skipsOnly
        (Label := Label) (arity := arity) h choose
  · intro x hx
    by_cases hxn : x.level < n
    · have hFlev :
          (F x).level < h := by
        have himg :
            (F x).level = imageLevel F x.level :=
          imageLevel_eq F rfl
        rw [himg]
        exact imageLevel_below_lt_missing
          F n h x.level hxn hskip' hlevel
      have hF1 :
          F1 x = F x := by
        dsimp [F1]
        exact m2InnerNode_eq_F_of_lt
          F n h hskip' hlevel hxn
      rw [hF1]
      dsimp [F2]
      exact gapNode_eq_self_of_lt h choose hFlev
    · have hxeq : x.level = n := by omega
      let sx : {y : Node Label arity // y.level = n} :=
        ⟨x, hxeq⟩
      have hF1 :
          F1 x = lowerImage F n h hlevel sx := by
        dsimp [F1]
        exact m2InnerNode_at_cut
          F n h hskip' hlevel sx
      rw [hF1]
      dsimp [F2, choose]
      exact m2Gap_hits_lowerImage
        F n h hskip' hlevel sx

end FreeAncestral
end SuccessorTree

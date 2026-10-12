import SuccessorTree.V10.LevelRemovalUniformOrder
import Mathlib.Tactic

/-!
# The intrinsic M2 candidate acts on every Kpt parameter by raw deletion

The complete-image deletion function constructed in UniformFunction
is intrinsic. At any source node x, its raw output is the image F(x)
with ordinary coordinate m erased IF that coordinate occurs in its
complete socle; otherwise the output is exactly F(x).

The case split by source level n is therefore equivalent to the
simple case split on whether the *image* record contains m.
This gives the precise elementwise/listwise transport that will be
combined with the verified optional canonical-parameter record
identities in the actual above-gap weak successor proof.

No ShapeMap structure on the new function or M2 axiom is assumed.
-/

namespace SuccessorTree.V10

/-- The intrinsic total deletion candidate acts on EVERY parameter
node by the simple raw-record deletion-if-present operation.
At low source levels, m is above the entire F-image socle; at high
source levels, it occurs in the image socle. -/
theorem uniformGapDeletedKpt_raw_if_above
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : AdmissibleKptNode family) :
    let m := LevelTree.lev (F a₀) - 1
    (uniformGapDeletedKpt family F q₀ a₀ hprev hgap x).1 =
      if hm : m < (F x).1.1
      then rawPartialTypeDeleteAt (F x).1 m hm
      else (F x).1 := by
  classical
  let m := LevelTree.lev (F a₀) - 1
  by_cases hHigh : LevelTree.lev a₀ ≤ LevelTree.lev x
  · obtain ⟨hm,hRaw⟩ :=
      uniformGapDeletedKpt_above_raw family F q₀ a₀
        hprev hgap x hHigh
    simpa only [dif_pos hm] using hRaw
  · have hLow : LevelTree.lev x < LevelTree.lev a₀ := by omega
    have hXQ : LevelTree.lev x ≤ LevelTree.lev q₀ := by omega
    have hFLe : LevelTree.lev (F x) ≤ LevelTree.lev (F q₀) :=
      shapeMap_level_le_of_level_le family F hXQ
    have hmLow : ¬ m < (F x).1.1 := by
      change ¬ m < LevelTree.lev (F x)
      dsimp [m]
      omega
    simpa only [dif_neg hmLow] using
      congrArg Subtype.val
        (uniformGapDeletedKpt_below family F q₀ a₀
          hprev hgap x hLow)

/-- The same equality for an entire successor parameter list.
Every parameter is mapped individually; there is no need to select
or decompose a parameter from a potentially unrelated witness. -/
theorem uniformGapDeletedKpt_raw_parameter_list
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (p : List (AdmissibleKptNode family)) :
    let m := LevelTree.lev (F a₀) - 1
    (p.map (uniformGapDeletedKpt family F q₀ a₀ hprev hgap)).map
        (fun x => x.1) =
      (p.map F).map (fun x =>
        if h : m < x.1.1 then rawPartialTypeDeleteAt x.1 m h else x.1) := by
  classical
  let m := LevelTree.lev (F a₀) - 1
  induction p with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [uniformGapDeletedKpt_raw_if_above family F q₀ a₀
        hprev hgap x, ih]

end SuccessorTree.V10

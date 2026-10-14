import SuccessorTree.V10.LocalAgeAllLevels
import SuccessorTree.V10.LevelRemovalUniformShapeMap
import SuccessorTree.Monoid
import Mathlib.Tactic

/-!
# A one-gap Kpt shape map fixes everything below the gap

The general one-gap level-map and identity arguments do not use M2.
The published monoid discussion originally invoked these through
SMTree, which would be circular while establishing M2 itself.

All levels of the concrete normalized Kpt tree are inhabited, so
choose a level representative and construct its level function for
ANY shape map. Exact level range and strict increase follow from
level preservation. Together with the order-theoretic range formula,
this proves the ordinary one-gap level action. The general
weak-successor/root argument then gives literal identity below the
skipped level, still without M2 or a corrected-B3 hypothesis.
-/

namespace SuccessorTree.V10

/-- Total level map for the Kpt forest, available before constructing
its SMTree instance and independent of M2. -/
noncomputable def kptShapeLevelMap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n : Nat) : Nat :=
  LevelTree.lev (F (Classical.choose
    (admissibleKptLevel_nonempty family n)))

theorem kptShapeLevelMap_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (a : AdmissibleKptNode family) :
    kptShapeLevelMap family F (LevelTree.lev a) = LevelTree.lev (F a) := by
  unfold kptShapeLevelMap
  have hlev := Classical.choose_spec
    (admissibleKptLevel_nonempty family (LevelTree.lev a))
  exact F.level_eq_of_level_eq hlev

theorem kptShapeLevelMap_strictMono
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family)) :
    StrictMono (kptShapeLevelMap family F) := by
  intro n m hnm
  change LevelTree.lev (F (Classical.choose
      (admissibleKptLevel_nonempty family n))) <
    LevelTree.lev (F (Classical.choose
      (admissibleKptLevel_nonempty family m)))
  apply F.level_lt_of_level_lt
  have hn := Classical.choose_spec
    (admissibleKptLevel_nonempty family n)
  have hm := Classical.choose_spec
    (admissibleKptLevel_nonempty family m)
  change (Classical.choose
      (admissibleKptLevel_nonempty family n)).1.1 <
    (Classical.choose
      (admissibleKptLevel_nonempty family m)).1.1
  rw [hn, hm]
  exact hnm

theorem kptShapeLevelMap_range
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family)) :
    Set.range (kptShapeLevelMap family F) = F.levelRange := by
  ext k
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨Classical.choose (admissibleKptLevel_nonempty family n), rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨LevelTree.lev a, (kptShapeLevelMap_eq family F a).trans ha⟩

/-- The exact insertion-level function of a one-gap shape map is
certified without the M2 field of SMTree. -/
theorem kptShapeMap_skipsOnly_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (m : Nat) (hskip : F.SkipsOnly m)
    (a : AdmissibleKptNode family) :
    LevelTree.lev (F a) =
      if LevelTree.lev a < m then LevelTree.lev a
      else LevelTree.lev a + 1 := by
  have hFormula :=
    SuccessorTree.SMTree.strictMono_nat_range_compl_singleton
      (kptShapeLevelMap family F)
      (kptShapeLevelMap_strictMono family F) m
      ((kptShapeLevelMap_range family F).trans hskip)
      (LevelTree.lev a)
  exact (kptShapeLevelMap_eq family F a).symm.trans hFormula

/-- Any shape map skipping exactly m is literally the identity on
Kpt levels below m. No M2 or M3 assumption is used here. -/
theorem kptShapeMap_fixed_below_skip
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (m : Nat) (hskip : F.SkipsOnly m)
    (a : AdmissibleKptNode family)
    (ha : LevelTree.lev a < m) :
    F a = a := by
  exact SuccessorTree.SMTree.eq_id_below_of_level_eq
    F m
    (fun x hx => by
      rw [kptShapeMap_skipsOnly_level family F m hskip x]
      simp only [if_pos hx]) ha

end SuccessorTree.V10

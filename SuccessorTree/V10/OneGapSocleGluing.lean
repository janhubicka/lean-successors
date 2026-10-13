import SuccessorTree.V10.ShapeMapParameterTransport
import SuccessorTree.V10.PrescribedBoringData
import SuccessorTree.V10.LevelRemovalSkipsOnly
import SuccessorTree.WeakSuccessorInjectivity
import Mathlib.Tactic

/-!
# Gluing one-gap maps over ordinary L+ socles

A successor and every parameter at or above the gap have the same
ordinary initial socle. Below the gap every one-gap map is the identity.
Consequently one may select a different one-gap ShapeMap for each
ordinary socle, with no agreement assumption between different classes.

The parameter assertion is derived from the genuine canonical successor
record. Neither an M2 axiom nor an age-preservation axiom is used.
-/

namespace SuccessorTree.V10

/-- All atoms on the ordinary socle, excluding the distinguished vertex. -/
abbrev OrdinarySocleRecord (ell db du dd : Nat) :=
  (Fin ell → Fin ell → Fin db → Bool) ×
  (Fin ell → Fin du → Bool) ×
  (Fin ell → Fin dd → Bool) ×
  (Fin ell → Fin ell → Bool)

def PartialTypeWithE.ordinarySocleRecord {ell db du dd : Nat}
    (Q : PartialTypeWithE ell db du dd) : OrdinarySocleRecord ell db du dd :=
  ⟨fun i j t => Q.lReduct.binary (some i) (some j) t,
    fun i t => Q.lReduct.unary (some i) t,
    fun i t => Q.lReduct.diagonal (some i) t,
    fun i j => Q.eRelation (some i) (some j)⟩

theorem ordinarySocleRecord_eq_iff {ell db du dd : Nat}
    (Q R : PartialTypeWithE ell db du dd) :
    Q.ordinarySocleRecord = R.ordinarySocleRecord ↔ SameOrdinaryAtCut Q R := by
  simp only [PartialTypeWithE.ordinarySocleRecord, Prod.mk.injEq,
    funext_iff, SameOrdinaryAtCut]

/-- Below the cut the selected record is irrelevant: all maps used
there will be the identity. -/
def ordinarySocleAt {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (a : AdmissibleKptNode family) : OrdinarySocleRecord ell db du dd :=
  if h : ell ≤ a.1.1 then (a.1.2.restrict h).ordinarySocleRecord
  else ⟨fun _ _ _ => false, fun _ _ => false,
    fun _ _ => false, fun _ _ => false⟩

theorem ordinarySocleAt_of_le {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) (ell : Nat)
    {a b : AdmissibleKptNode family}
    (ha : ell ≤ LevelTree.lev a) (hab : a ≤ b) :
    ordinarySocleAt family ell a = ordinarySocleAt family ell b := by
  change ell ≤ a.1.1 at ha
  have hb : ell ≤ b.1.1 := le_trans ha hab.1
  simp only [ordinarySocleAt, dif_pos ha, dif_pos hb]
  rw [hab.2, PartialTypeWithE.restrict_trans]

/-- The full record of a genuine parameter has exactly the ambient
ordinary initial socle. This is not an extra compatibility assumption. -/
theorem ordinarySocleAt_of_parameter {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) (ell : Nat)
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)} {c : AdmissibleKptSigma family}
    (hSucc : (admissibleKptSTree family).succ a p c = some b)
    (v : AdmissibleKptNode family) (hv : v ∈ p)
    (hHigh : ell ≤ LevelTree.lev v) :
    ordinarySocleAt family ell v = ordinarySocleAt family ell b := by
  obtain ⟨hj, hf, hRaw⟩ := canonicalKptStep_parameter_in_upper family
    (canonicalKptSucc_spec family hSucc) le_rfl v hv
  have hRecord : v.1.2 = b.1.2.ordinaryType (LevelTree.lev a) hj
      (LevelTree.lev v) hf := eq_of_heq (Sigma.mk.inj_iff.mp hRaw).2
  change ell ≤ v.1.1 at hHigh
  have hb : ell ≤ b.1.1 := le_trans hHigh hf
  simp only [ordinarySocleAt, dif_pos hHigh, dif_pos hb]
  rw [hRecord]
  rfl

/-- Select a one-gap map separately for each ordinary initial socle. -/
noncomputable def oneGapBySocle {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) (ell : Nat)
    (Phi : OrdinarySocleRecord ell db du dd →
      SuccessorTree.ShapeMap (admissibleKptSTree family))
    (a : AdmissibleKptNode family) : AdmissibleKptNode family :=
  Phi (ordinarySocleAt family ell a) a

theorem oneGapBySocle_level {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) (ell : Nat)
    (Phi : OrdinarySocleRecord ell db du dd →
      SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hSkip : ∀ C, (Phi C).SkipsOnly ell) (a : AdmissibleKptNode family) :
    LevelTree.lev (oneGapBySocle family ell Phi a) =
      if LevelTree.lev a < ell then LevelTree.lev a else LevelTree.lev a + 1 :=
  kptShapeMap_skipsOnly_level family (Phi (ordinarySocleAt family ell a))
    ell (hSkip _) a

/-- On a low node the selected map can be replaced by any other class. -/
theorem oneGapBySocle_eq_at_low {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) (ell : Nat)
    (Phi : OrdinarySocleRecord ell db du dd →
      SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hSkip : ∀ C, (Phi C).SkipsOnly ell)
    (a : AdmissibleKptNode family) (ha : LevelTree.lev a < ell)
    (C : OrdinarySocleRecord ell db du dd) :
    oneGapBySocle family ell Phi a = Phi C a := by
  exact (kptShapeMap_fixed_below_skip family
    (Phi (ordinarySocleAt family ell a)) ell (hSkip _) a ha).trans
    (kptShapeMap_fixed_below_skip family (Phi C) ell (hSkip C) a ha).symm

/-- Every genuine successor can be checked within its one ambient
class: high parameters have that class and low parameters are fixed. -/
theorem oneGapBySocle_weak_succ {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) (ell : Nat)
    (Phi : OrdinarySocleRecord ell db du dd →
      SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hSkip : ∀ C, (Phi C).SkipsOnly ell)
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)} {c : AdmissibleKptSigma family}
    (hSucc : (admissibleKptSTree family).succ a p c = some b) :
    ∃ d, (admissibleKptSTree family).succ (oneGapBySocle family ell Phi a)
      (p.map (oneGapBySocle family ell Phi)) c = some d ∧
      d ≤ oneGapBySocle family ell Phi b := by
  let C := ordinarySocleAt family ell b
  have hA : oneGapBySocle family ell Phi a = Phi C a := by
    by_cases hLow : LevelTree.lev a < ell
    · exact oneGapBySocle_eq_at_low family ell Phi hSkip a hLow C
    · unfold oneGapBySocle
      rw [ordinarySocleAt_of_le family ell (by omega)
        ((admissibleKptSTree family).covBy_of_succ_eq_some hSucc).le]
  have hP : p.map (oneGapBySocle family ell Phi) = p.map (Phi C) := by
    apply List.map_congr_left
    intro v hv
    by_cases hLow : LevelTree.lev v < ell
    · exact oneGapBySocle_eq_at_low family ell Phi hSkip v hLow C
    · unfold oneGapBySocle
      rw [ordinarySocleAt_of_parameter family ell hSucc v hv (by omega)]
  obtain ⟨d, hd, hdb⟩ := (Phi C).weak_succ' hSucc
  refine ⟨d, ?_, hdb⟩
  rw [hA, hP]
  exact hd

/-- The selected function is an actual ShapeMap. Injectivity is derived
from weak successors, not an assumed cross-class injectivity condition. -/
noncomputable def oneGapSocleShapeMap {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) (ell : Nat)
    (Phi : OrdinarySocleRecord ell db du dd →
      SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hSkip : ∀ C, (Phi C).SkipsOnly ell) :
    SuccessorTree.ShapeMap (admissibleKptSTree family) := by
  have hLevel : ∀ {a b : AdmissibleKptNode family},
      LevelTree.lev a = LevelTree.lev b →
      LevelTree.lev (oneGapBySocle family ell Phi a) =
        LevelTree.lev (oneGapBySocle family ell Phi b) := by
    intro a b hab
    rw [oneGapBySocle_level family ell Phi hSkip,
      oneGapBySocle_level family ell Phi hSkip, hab]
  have hStrict : ∀ {a b : AdmissibleKptNode family},
      LevelTree.lev a < LevelTree.lev b →
      LevelTree.lev (oneGapBySocle family ell Phi a) <
        LevelTree.lev (oneGapBySocle family ell Phi b) := by
    intro a b hab
    rw [oneGapBySocle_level family ell Phi hSkip,
      oneGapBySocle_level family ell Phi hSkip]
    split_ifs <;> omega
  have hRoot : ∀ {a : AdmissibleKptNode family}, LevelTree.lev a = 0 →
      a ≤ oneGapBySocle family ell Phi a := by
    intro a ha
    exact (Phi (ordinarySocleAt family ell a)).root_le' ha
  exact
    { toFun := oneGapBySocle family ell Phi
      injective' := SuccessorTree.injective_of_level_order_and_weak_successors
        (admissibleKptSTree family) (oneGapBySocle family ell Phi)
        hLevel hStrict (oneGapBySocle_weak_succ family ell Phi hSkip) hRoot
      level_preserving' := hLevel
      weak_succ' := oneGapBySocle_weak_succ family ell Phi hSkip
      root_le' := hRoot }

theorem oneGapSocleShapeMap_mem_KptM {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) (ell : Nat)
    (Phi : OrdinarySocleRecord ell db du dd →
      SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hSkip : ∀ C, (Phi C).SkipsOnly ell) (hPos : 0 < ell) :
    oneGapSocleShapeMap family ell Phi hSkip ∈ KptM family := by
  intro a ha
  change LevelTree.lev (oneGapBySocle family ell Phi a) = 0
  rw [oneGapBySocle_level family ell Phi hSkip, ha]
  simp only [if_pos hPos]

theorem oneGapSocleShapeMap_skipsOnly {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) (ell : Nat)
    (Phi : OrdinarySocleRecord ell db du dd →
      SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hSkip : ∀ C, (Phi C).SkipsOnly ell) :
    (oneGapSocleShapeMap family ell Phi hSkip).SkipsOnly ell := by
  let C : OrdinarySocleRecord ell db du dd :=
    ⟨fun _ _ _ => false, fun _ _ => false,
      fun _ _ => false, fun _ _ => false⟩
  have hSame : ∀ a : AdmissibleKptNode family,
      LevelTree.lev (oneGapSocleShapeMap family ell Phi hSkip a) =
        LevelTree.lev (Phi C a) := by
    intro a
    exact (oneGapBySocle_level family ell Phi hSkip a).trans
      (kptShapeMap_skipsOnly_level family (Phi C) ell (hSkip C) a).symm
  have hRange : (oneGapSocleShapeMap family ell Phi hSkip).levelRange =
      (Phi C).levelRange := by
    ext k
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, (hSame a).symm.trans ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, (hSame a).trans ha⟩
  exact hRange.trans (hSkip C)

end SuccessorTree.V10

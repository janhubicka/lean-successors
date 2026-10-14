import SuccessorTree.V10.LevelRemovalAdmissibleType
import SuccessorTree.V10.CanonicalRawSTree
import SuccessorTree.V10.AdmissibleSigmaSTree
import SuccessorTree.ShapePreserving
import Mathlib.Tactic

/-!
# The successor column at a skipped target level has a strict free cut

This is the first uniform ingredient of the manuscript's level-removal
lemma. Suppose a shape-preserving map F separates the image of one
source level from the preceding image level by at least two. Every
parameter of an actual source successor has level strictly below
the source base. Its image therefore lies strictly below the
last omitted target coordinate m = lev(F a)-1.

The actual weak image successor starts at F a and has an admissible
canonical new ordinary column. Its E free cut is zero if there is
no parameter, and otherwise is the level of the unique mapped
canonical parameter; in both cases it is strictly below m.

Crucially, this uses a genuine image successor rather than an
arbitrary finite representation of the image at the boundary source
level. It does NOT construct the uniform deletion ShapeMap or imply M2.
-/

namespace SuccessorTree.V10

/-- With a gap of at least one omitted target level just before F(a),
the images of all parameter nodes of any genuine successor of a
lie strictly below the last omitted target coordinate. This uses
only S1 and level preservation of the shape map, not M2. -/
theorem mapped_successor_parameters_below_gap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q a b : AdmissibleKptNode family)
    (p : List (AdmissibleKptNode family))
    (c : AdmissibleKptSigma family)
    (hprev : LevelTree.lev q + 1 = LevelTree.lev a)
    (hgap : LevelTree.lev (F q) + 1 < LevelTree.lev (F a))
    (hSucc : (admissibleKptSTree family).succ a p c = some b) :
    ∀ x ∈ p, LevelTree.lev (F x) < LevelTree.lev (F a) - 1 := by
  intro x hx
  have hxlt : LevelTree.lev x < LevelTree.lev a :=
    (admissibleKptSTree family).parameter_level_lt hSucc hx
  have hxle : LevelTree.lev x ≤ LevelTree.lev q := by omega
  by_cases heq : LevelTree.lev x = LevelTree.lev q
  · have hFlevel := F.level_eq_of_level_eq heq
    omega
  · have hlt : LevelTree.lev x < LevelTree.lev q := by omega
    have hFlevel := F.level_lt_of_level_lt hlt
    omega

/-- If all parameters of an actual canonical step lie strictly
below the penultimate level of its base, the genuine new E column
has free cut strictly below that penultimate level. The parameter
list may be empty: in that case the canonical free cut is zero. -/
theorem canonical_step_free_cut_below_gap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (a b : AdmissibleKptNode family)
    (p : List (AdmissibleKptNode family))
    (c : RawKptLetter db du dd)
    (hStep : IsCanonicalKptStep family a p c b)
    (hBase : 1 < LevelTree.lev a)
    (hParams : ∀ x ∈ p,
      LevelTree.lev x < LevelTree.lev a - 1) :
    ∃ (ell f : Nat) (hf : f ≤ ell)
      (Q : PartialTypeWithE (ell + 1) db du dd),
      a.1 = (⟨ell,Q.restrict (Nat.le_succ ell)⟩ :
        RawPartialTypeNode db du dd) ∧
      b.1 = (⟨ell + 1,Q⟩ : RawPartialTypeNode db du dd) ∧
      ValidNewOrdinaryColumn Q f ∧
      f < LevelTree.lev a - 1 := by
  classical
  obtain ⟨ell,f,hf,Q,hSource,hTarget,_hLetter,hValid,hParameter,_hGate⟩ :=
    hStep
  have hLevel : LevelTree.lev a = ell := by
    change a.1.1 = ell
    rw [hSource]
  have hSmall : f < LevelTree.lev a - 1 := by
    by_cases hz : f = 0
    · omega
    · have hMem :
          (⟨f,Q.lastOrdinaryParameter f hf⟩ :
              RawPartialTypeNode db du dd) ∈
            p.map (fun x => x.1) := by
        rw [hParameter]
        simp [PartialTypeWithE.canonicalParameterRecord, hz]
      obtain ⟨x,hx,hxRecord⟩ := List.mem_map.mp hMem
      have hxLevel : LevelTree.lev x = f := by
        have hh := congrArg Sigma.fst hxRecord
        exact hh
      have hxBound := hParams x hx
      omega
  exact ⟨ell,f,hf,Q,hSource,hTarget,hValid,hSmall⟩

/-- The genuine weak successor supplied by a shape map at a target
gap provides a *valid* last ordinary column with a strictly low E
cut. Its value lies below F(b); no equality with F(b) is assumed
across a skipped level. -/
theorem mapped_successor_has_guarded_gap_column
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q a b : AdmissibleKptNode family)
    (p : List (AdmissibleKptNode family))
    (c : AdmissibleKptSigma family)
    (hprev : LevelTree.lev q + 1 = LevelTree.lev a)
    (hgap : LevelTree.lev (F q) + 1 < LevelTree.lev (F a))
    (hSucc : (admissibleKptSTree family).succ a p c = some b) :
    ∃ d : AdmissibleKptNode family,
      (admissibleKptSTree family).succ (F a) (p.map F) c = some d ∧
      d ≤ F b ∧
      ∃ (ell f : Nat) (hf : f ≤ ell)
        (Q : PartialTypeWithE (ell + 1) db du dd),
        (F a).1 = (⟨ell,Q.restrict (Nat.le_succ ell)⟩ :
          RawPartialTypeNode db du dd) ∧
        d.1 = (⟨ell + 1,Q⟩ : RawPartialTypeNode db du dd) ∧
        ValidNewOrdinaryColumn Q f ∧
        f < LevelTree.lev (F a) - 1 := by
  obtain ⟨d,hMapped,hBelow⟩ := F.weak_succ' hSucc
  have hBound : ∀ y ∈ p.map F,
      LevelTree.lev y < LevelTree.lev (F a) - 1 := by
    intro y hy
    obtain ⟨x,hx,hxy⟩ := List.mem_map.mp hy
    subst y
    exact mapped_successor_parameters_below_gap
      family F q a b p c hprev hgap hSucc x hx
  have hLong : 1 < LevelTree.lev (F a) := by omega
  have hStep : IsCanonicalKptStep family (F a) (p.map F) c.1 d := by
    apply canonicalKptSucc_spec family
    simpa only [admissibleKptSTree_succ_eq] using hMapped
  obtain ⟨ell,f,hf,Q,hSource,hTarget,hValid,hSmall⟩ :=
    canonical_step_free_cut_below_gap
      family (F a) d (p.map F) c.1 hStep hLong hBound
  exact ⟨d,hMapped,hBelow,ell,f,hf,Q,hSource,hTarget,hValid,hSmall⟩

end SuccessorTree.V10

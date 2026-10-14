import SuccessorTree.V10.LevelRemovalGapColumn
import SuccessorTree.V10.LevelRemovalPrefixCut
import SuccessorTree.V10.LevelRemovalSourceSuccessor
import Mathlib.Tactic

/-!
# An image gap gives the sharp deletion guard in every upper witness

Fix a shape-preserving map F and two successive source levels whose
images are separated by at least one omitted target coordinate. The
verified weak-successor theorem supplies a genuine new ordinary
column at F(a) and proves that its E free cut is below the last
missing target coordinate.

That canonical new step need not equal F(b) across a gap; it is
only a prefix of F(b). The witness/prefix-cut transfer shows that
its E-column free cut is still the actual free cut in EVERY finite
representation of F(z), whenever b is a predecessor of z.

At the first source level, a genuine successor b exists by the
independent M3-derived positive-level pruning theorem. One may
therefore obtain a guarded upper witness without assuming anything
about the next column of an arbitrary representative of F(a).

These statements do not construct the uniform deletion ShapeMap
nor establish M2 factorization or corrected finite L-only B3.
-/

namespace SuccessorTree.V10

/-- The complete E column of a genuine weak image successor
persists in every finite witness of any later image above that
source successor. The strict bound is uniform in the finite
representative: its proof uses actual Kpt prefix transport. -/
theorem gap_guard_in_every_upper_image_witness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q a b z : AdmissibleKptNode family)
    (p : List (AdmissibleKptNode family))
    (c : AdmissibleKptSigma family)
    (hPrev : LevelTree.lev q + 1 = LevelTree.lev a)
    (hGap : LevelTree.lev (F q) + 1 < LevelTree.lev (F a))
    (hSucc : (admissibleKptSTree family).succ a p c = some b)
    (hbz : b ≤ z)
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (hv : v < A.size)
    (hRep : (F z).1 = A.rawTypeAtFree v) :
    A.freeLevel (LevelTree.lev (F a)) <
      LevelTree.lev (F a) - 1 := by
  obtain ⟨d,_hMapped,hdb,ell,f,hf,Q,hBase,hRaw,hValid,hSmall⟩ :=
    mapped_successor_has_guarded_gap_column
      family F q a b p c hPrev hGap hSucc
  have hdbz : d ≤ F z :=
    hdb.trans (F.map_le_of_le hbz)
  have hGuard : A.freeLevel ell < LevelTree.lev (F a) - 1 :=
    guarded_gap_column_below_Kpt_witness
      family d (F z) ell (LevelTree.lev (F a) - 1)
      Q hRaw hdbz f hf hValid hSmall A v hv hRep
  have hLevel : LevelTree.lev (F a) = ell := by
    have hh := congrArg Sigma.fst hBase
    exact hh
  rw [← hLevel] at hGuard
  exact hGuard

/-- At every positive source level with a target gap, a genuine
source successor can be chosen whose image has an ACTUAL finite
forbidden-free representation with the sharp deletion guard.

The cut is inherited from the image successor's canonical record,
not postulated on a generic finite witness of the boundary type. -/
theorem boundary_gap_guarded_successor_witness_exists
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q a : AdmissibleKptNode family)
    (hPrev : LevelTree.lev q + 1 = LevelTree.lev a)
    (hGap : LevelTree.lev (F q) + 1 < LevelTree.lev (F a)) :
    ∃ (b : AdmissibleKptNode family)
      (p : List (AdmissibleKptNode family))
      (c : AdmissibleKptSigma family)
      (A : EnumeratedPartialStructure db du dd)
      (v : Nat),
      (admissibleKptSTree family).succ a p c = some b ∧
      v < A.size ∧
      (∀ bad, bad ∈ family → bad.Avoids A.L) ∧
      (F b).1 = A.rawTypeAtFree v ∧
      A.freeLevel (LevelTree.lev (F a)) <
        LevelTree.lev (F a) - 1 := by
  have hPos : 0 < LevelTree.lev a := by omega
  obtain ⟨b,p,c,hSucc⟩ :=
    admissibleKpt_exists_successor_step_of_level_pos family a hPos
  obtain ⟨A,v,hv,hAvoid,hRaw⟩ := (F b).2
  have hGuard := gap_guard_in_every_upper_image_witness
    family F q a b b p c hPrev hGap hSucc le_rfl A v hv hRaw
  exact ⟨b,p,c,A,v,hSucc,hv,hAvoid,hRaw,hGuard⟩

end SuccessorTree.V10

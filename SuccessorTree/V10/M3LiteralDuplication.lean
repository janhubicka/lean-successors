import SuccessorTree.V10.M3CombinedEndpoint
import Mathlib.Tactic

/-!
# The manuscript's universally quantified M3 duplication law

The chosen earlier canonical successor from M3CombinedEndpoint is not
yet literally (M3): the paper quantifies over every earlier successor
whose value lies below a node of level ell. We prove the conversion
using uniqueness of a predecessor at level n+1 and S2, not by
assuming the earlier parameters or the letter match the chosen ones.

This is the exact law inside the normalized Kpt S-tree. The remaining
boundary is the general manuscript language and its diagonal/nullary
coding, not the M3 quantifier order.
-/

namespace SuccessorTree.V10

/-- For a fixed n<ell, one ONE-GAP map works simultaneously for
every a of level n, every b of level ell, and every legitimate
earlier successor S(a,p,c) below b. Its output is exactly S(b,p,c).
No equality or compatibility of the earlier input parameters is
postulated. -/
theorem m3OneGapShapeMap_literalM3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n ell : Nat) (hn : n < ell) :
    ∃ Φ : SuccessorTree.ShapeMap (admissibleKptSTree family),
      Φ ∈ KptM family ∧ Φ.SkipsOnly ell ∧
      ∀ (a b x : AdmissibleKptNode family)
        (p : List (AdmissibleKptNode family))
        (c : AdmissibleKptSigma family),
        LevelTree.lev a = n →
        LevelTree.lev b = ell →
        (admissibleKptSTree family).succ a p c = some x →
        x ≤ b →
        (admissibleKptSTree family).succ b p c = some (Φ b) := by
  obtain ⟨Φ,hM,hSkip,hChosen⟩ :=
    m3OneGapShapeMap_repeats_old_step family n hn
  refine ⟨Φ,hM,hSkip,?_⟩
  intro a b x p c ha hb hStep hx
  rcases b with ⟨⟨k,T⟩,hT⟩
  change k = ell at hb
  subst k
  obtain ⟨aOld,bOld,pOld,cOld,hOldStep,hOldRaw,hNewSucc⟩ :=
    hChosen T hT
  have hBelow :
      bOld ≤ (⟨⟨ell,T⟩,hT⟩ : AdmissibleKptNode family) := by
    change bOld.1 ≤
      (⟨ell,T⟩ : RawPartialTypeNode db du dd)
    rw [hOldRaw]
    exact ⟨Nat.succ_le_of_lt hn, rfl⟩
  have hOldLevel : LevelTree.lev bOld = n+1 := by
    change bOld.1.1 = n+1
    rw [hOldRaw]
  have hXLevel : LevelTree.lev x = n+1 := by
    rw [LevelTree.covBy_level_eq
      ((admissibleKptSTree family).covBy_of_succ_eq_some hStep), ha]
  have hSame : x = bOld := by
    rcases LevelTree.comparable_below hx hBelow with h | h
    · exact LevelTree.same_level_of_le h
        (hXLevel.trans hOldLevel.symm)
    · exact (LevelTree.same_level_of_le h
        (hOldLevel.trans hXLevel.symm)).symm
  have hOldSucc :
      (admissibleKptSTree family).succ aOld pOld cOld =
        some bOld := by
    change canonicalKptSucc family aOld pOld cOld.1 =
      some bOld
    exact canonicalKptSucc_eq_some_of_step family hOldStep
  have hOldSucc' :
      (admissibleKptSTree family).succ aOld pOld cOld =
        some x := by
    rw [hSame]
    exact hOldSucc
  obtain ⟨_,hp,hc⟩ := (admissibleKptSTree family).s2
    hStep hOldSucc'
  simpa only [hp,hc] using hNewSucc

end SuccessorTree.V10

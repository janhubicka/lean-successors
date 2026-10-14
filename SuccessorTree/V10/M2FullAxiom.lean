import SuccessorTree.V10.M2BoundaryCompatibleB3Closure
import SuccessorTree.V10.LevelRemovalGapSeparation
import Mathlib.Tactic

/-!
# The literal M2 axiom for the normalized Kpt monoid

The finite forbidden-age argument proves factorization whenever the
images of two consecutive source levels have a gap.  The formal M2
axiom starts instead with an arbitrary source level n and assumes that
F skips the target level immediately preceding F(n).

Because F preserves level order and its monoid preserves level zero,
n is necessarily positive.  The immediate source predecessor of a
node on level n therefore exists, and its image lies strictly below
the omitted target level: otherwise the forbidden target level would
be attained.  Applying the established first-gap factorization gives
M2 with its ORIGINAL quantified premises.  No M2 or SMTree instance
is used anywhere in this derivation.

This is for the normalized unary/binary Kpt presentation.  The
original-language adapter and its relation to the paper's general
signature are separate.
-/

namespace SuccessorTree.V10

/-- A missing level directly below the image of a node produces the
actual consecutive-source-level image gap.  This step uses neither
the forbidden-age lemma nor the M2 axiom. -/
theorem kpt_predecessor_gap_of_skipped
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hFM : F ∈ KptM family)
    (n : Nat) (a : AdmissibleKptNode family)
    (ha : LevelTree.lev a = n)
    (hFpositive : 0 < LevelTree.lev (F a))
    (hSkipped : F.Skips (LevelTree.lev (F a) - 1)) :
    ∃ q : AdmissibleKptNode family,
      LevelTree.lev q + 1 = LevelTree.lev a ∧
      LevelTree.lev (F q) + 1 < LevelTree.lev (F a) := by
  have hnPositive : 0 < n := by
    by_contra hnp
    have hnZero : n = 0 := by omega
    have hRoot : LevelTree.lev a = 0 := ha.trans hnZero
    have hFRoot : LevelTree.lev (F a) = 0 := hFM a hRoot
    omega
  have hAncestorCut : n-1 ≤ LevelTree.lev a := by omega
  let q := LevelTree.ancestor a (n-1) hAncestorCut
  have hqLevel : LevelTree.lev q = n-1 :=
    LevelTree.level_ancestor a (n-1) hAncestorCut
  have hPrev : LevelTree.lev q + 1 = LevelTree.lev a := by
    rw [hqLevel, ha]
    omega
  have hQlt : LevelTree.lev q < LevelTree.lev a := by omega
  have hFlt : LevelTree.lev (F q) < LevelTree.lev (F a) :=
    F.level_lt_of_level_lt hQlt
  have hGap : LevelTree.lev (F q) + 1 < LevelTree.lev (F a) := by
    by_contra hNotGap
    have hFq : LevelTree.lev (F q) = LevelTree.lev (F a)-1 := by
      omega
    have hAttained : LevelTree.lev (F a)-1 ∈ F.levelRange := ⟨q,hFq⟩
    exact hSkipped hAttained
  exact ⟨q,hPrev,hGap⟩

/-- M2 for the actual normalized Kpt monoid, with the exact
quantifier order and skipped-level hypothesis of SMTree.m2.

This endpoint is unconditional once the preceding actual-boundary
CompatibleB3 theorem is kernel-checked; it does not invoke SMTree.m2. -/
theorem kptM2
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    ∀ (n : Nat)
      (F : SuccessorTree.ShapeMap (admissibleKptSTree family)),
      F ∈ KptM family →
      ∀ (a : AdmissibleKptNode family),
        LevelTree.lev a = n →
        0 < LevelTree.lev (F a) →
        F.Skips (LevelTree.lev (F a) - 1) →
        ∃ F1 F2 : SuccessorTree.ShapeMap (admissibleKptSTree family),
          F1 ∈ KptM family ∧
          F2 ∈ KptM family ∧
          F2.SkipsOnly (LevelTree.lev (F a) - 1) ∧
          ∀ x : AdmissibleKptNode family,
            LevelTree.lev x ≤ n → F2 (F1 x) = F x := by
  intro n F hFM a ha hFpositive hSkipped
  obtain ⟨q,hPrev,hGap⟩ :=
    kpt_predecessor_gap_of_skipped family F hFM n a
      ha hFpositive hSkipped
  simpa only [ha] using
    (m2_actual_first_gap_factorization
      family F hFM q a hPrev hGap)

end SuccessorTree.V10

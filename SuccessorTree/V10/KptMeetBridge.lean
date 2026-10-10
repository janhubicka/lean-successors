import SuccessorTree.V10.AdmissibleKptLevelTree
import SuccessorTree.V10.CommonSocleType
import SuccessorTree.V10.FirstFullPrefix
import Mathlib.Tactic

/-!
# From complete partial-type records to the genuine admissible Kpt meet

This is the missing structural part of the v10 Lemma 6.49 adapter.
The normalized forbidden-free Kpt tree has ALREADY been constructed as
an actual LevelTree, with a proved order, ancestors and meets.
The following theorems now identify the ancestor of an original type
extracted from a given ambient partial structure with its literal
induced prefix, including all E/unary/diagonal/binary facts.

Consequently an earliest directed binary difference occurring below
both E free levels determines the level of the actual admissible-Kpt
meet. We do not assume a tree/meet interface on arbitrary traces.

The H-specific numerical classification and its fake vertices remain
separate; the exact sharp free-cut guard must be used when instantiating
this theorem with H originals.
-/

namespace SuccessorTree.V10

/-- Ancestors of two genuine Kpt types extracted from ONE ambient
partial structure agree at cut d exactly when the corresponding
complete extracted L+ records agree at d.

The admissibility witnesses can be arbitrary; their proof fields are
irrelevant to the equality of normalized Kpt nodes. -/
theorem admissibleKpt_original_ancestors_eq_iff
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (v w d : Nat)
    (hAdV : IsAdmissibleRawType family (A.rawTypeAtFree v))
    (hAdW : IsAdmissibleRawType family (A.rawTypeAtFree w))
    (hdv : d ≤ A.freeLevel v)
    (hdw : d ≤ A.freeLevel w) :
    LevelTree.ancestor
        (⟨A.rawTypeAtFree v, hAdV⟩ : AdmissibleKptNode family) d hdv =
      LevelTree.ancestor
        (⟨A.rawTypeAtFree w, hAdW⟩ : AdmissibleKptNode family) d hdw
      ↔ A.partialTypeAt d v = A.partialTypeAt d w := by
  rw [admissibleKpt_levelTree_ancestor_eq,
      admissibleKpt_levelTree_ancestor_eq]
  constructor
  · intro h
    have hRaw := congrArg Subtype.val h
    change
      (⟨d, (A.partialTypeAt (A.freeLevel v) v).restrict hdv⟩ :
        RawPartialTypeNode db du dd) =
      (⟨d, (A.partialTypeAt (A.freeLevel w) w).restrict hdw⟩ :
        RawPartialTypeNode db du dd) at hRaw
    rw [A.partialTypeAt_restrict d (A.freeLevel v) v hdv,
        A.partialTypeAt_restrict d (A.freeLevel w) w hdw] at hRaw
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hRaw
  · intro h
    apply Subtype.ext
    change
      (⟨d, (A.partialTypeAt (A.freeLevel v) v).restrict hdv⟩ :
        RawPartialTypeNode db du dd) =
      (⟨d, (A.partialTypeAt (A.freeLevel w) w).restrict hdw⟩ :
        RawPartialTypeNode db du dd)
    rw [A.partialTypeAt_restrict d (A.freeLevel v) v hdv,
        A.partialTypeAt_restrict d (A.freeLevel w) w hdw]
    exact congrArg (Sigma.mk d) h

/-- First binary discrepancy below both E free levels gives the
MEET LEVEL IN THE ACTUAL NORMALIZED FORBIDDEN-FREE Kpt TREE.
This is stronger than the raw greatest-prefix result: the ambient
admissibility and LevelTree instance are not merely assumed. -/
theorem admissibleKpt_meet_level_of_first_binary_difference
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (v w d : Nat)
    (hAdV : IsAdmissibleRawType family (A.rawTypeAtFree v))
    (hAdW : IsAdmissibleRawType family (A.rawTypeAtFree w))
    (hv : d + 1 ≤ A.freeLevel v)
    (hw : d + 1 ≤ A.freeLevel w)
    (hRoot : A.partialTypeAt 0 v = A.partialTypeAt 0 w)
    (hBefore : SameAmbientCrossType A v w d)
    (hDiff :
      (∃ r : Fin db, A.L.binary d v r ≠ A.L.binary d w r) ∨
      (∃ r : Fin db, A.L.binary v d r ≠ A.L.binary w d r)) :
    LevelTree.lev (LevelTree.meet
      (⟨A.rawTypeAtFree v, hAdV⟩ : AdmissibleKptNode family)
      (⟨A.rawTypeAtFree w, hAdW⟩ : AdmissibleKptNode family)) = d := by
  let av : AdmissibleKptNode family := ⟨A.rawTypeAtFree v, hAdV⟩
  let aw : AdmissibleKptNode family := ⟨A.rawTypeAtFree w, hAdW⟩
  have hdv : d ≤ LevelTree.lev av := by
    change d ≤ A.freeLevel v
    omega
  have hdw : d ≤ LevelTree.lev aw := by
    change d ≤ A.freeLevel w
    omega
  have hnv : d + 1 ≤ LevelTree.lev av := by
    change d + 1 ≤ A.freeLevel v
    exact hv
  have hnw : d + 1 ≤ LevelTree.lev aw := by
    change d + 1 ≤ A.freeLevel w
    exact hw
  obtain ⟨hPrev, hNext⟩ :=
    sameAmbient_first_fullType_difference
      A v w d hv hw hRoot hBefore hDiff
  have hAtD :
      LevelTree.ancestor av d hdv =
        LevelTree.ancestor aw d hdw := by
    exact (admissibleKpt_original_ancestors_eq_iff
      family A v w d hAdV hAdW (by omega) (by omega)).2 hPrev
  have hAtNext :
      LevelTree.ancestor av (d + 1) hnv ≠
        LevelTree.ancestor aw (d + 1) hnw := by
    intro h
    exact hNext ((admissibleKpt_original_ancestors_eq_iff
      family A v w (d + 1) hAdV hAdW hv hw).1 h)
  exact meet_level_of_adjacent_ancestors av aw d
    hdv hdw hnv hnw hAtD hAtNext

/-- A paper-facing version: forbidden-freeness of the common ambient
directly supplies the two admissibility witnesses, so the Kpt meet
theorem does NOT assume an independent pair of arbitrary Kpt nodes. -/
theorem forbiddenFreeKpt_meet_level_of_first_binary_difference
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (v w d : Nat)
    (hvA : v < A.size) (hwA : w < A.size)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hv : d + 1 ≤ A.freeLevel v)
    (hw : d + 1 ≤ A.freeLevel w)
    (hRoot : A.partialTypeAt 0 v = A.partialTypeAt 0 w)
    (hBefore : SameAmbientCrossType A v w d)
    (hDiff :
      (∃ r : Fin db, A.L.binary d v r ≠ A.L.binary d w r) ∨
      (∃ r : Fin db, A.L.binary v d r ≠ A.L.binary w d r)) :
    LevelTree.lev (LevelTree.meet
      (⟨A.rawTypeAtFree v, ⟨A, v, hvA, hAvoid, rfl⟩⟩ :
        AdmissibleKptNode family)
      (⟨A.rawTypeAtFree w, ⟨A, w, hwA, hAvoid, rfl⟩⟩ :
        AdmissibleKptNode family)) = d := by
  exact admissibleKpt_meet_level_of_first_binary_difference
    family A v w d
    ⟨A, v, hvA, hAvoid, rfl⟩
    ⟨A, w, hwA, hAvoid, rfl⟩
    hv hw hRoot hBefore hDiff

end SuccessorTree.V10

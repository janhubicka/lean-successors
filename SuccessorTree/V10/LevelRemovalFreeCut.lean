import SuccessorTree.V10.LevelRemovalPartial
import Mathlib.Tactic

/-!
# Exact free-level transport through a guarded vertex deletion

Removing the old coordinate m changes a vertex's E-socle by
deleting that coordinate, if the free socle contained it.
Consequently the new free level is f-1 when m<f, and f
otherwise. This is not just a cardinality estimate: we prove
the complete E-column equivalence, and then identify the
canonical first-missing E-coordinate in the new partial
structure using uniqueness from Definition 6.28.

The original vertex corresponding to a new coordinate v is
deleteAt m v. Thus the correct formula is:

  fl_(A\m)(v) = deleteAtCut m (fl_A(deleteAt m v)).

In particular there is no arbitrary choice of E cuts in
Lemma 6.34's deletion operation, and the sharp strict guard
on fl_A(m+1) remains necessary to preserve spacing.

This is a local structural theorem; the uniform shape-map
deletion and its M2 factorization are not asserted here.
-/

namespace SuccessorTree.V10

/-- Length of an old initial E-socle after the deletion of
coordinate m. It drops by one exactly when that initial
segment includes m. -/
def deleteAtCut (m f : Nat) : Nat :=
  if m < f then f - 1 else f

/-- The old/new coordinate inclusion maps initial segments
onto their shortened initial segments. This arithmetic fact
underlies all E free-level transport after deletion. -/
theorem deleteAt_lt_iff_lt_deleteAtCut
    (m f u : Nat) :
    deleteAt m u < f ↔ u < deleteAtCut m f := by
  unfold deleteAt deleteAtCut
  by_cases hm : m < f
  · by_cases hu : u < m
    · simp only [if_pos hm, if_pos hu]
      omega
    · simp only [if_pos hm, if_neg hu]
      omega
  · by_cases hu : u < m
    · simp only [if_neg hm, if_pos hu]
      omega
    · simp only [if_neg hm, if_neg hu]
      omega

/-- Every remaining E-column is exactly the initial segment
obtained by deleting coordinate m from its original E-socle. -/
theorem deleteAtE_iff_cut
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (m u v : Nat) :
    deleteAtE A m u v = true ↔
      u < deleteAtCut m (A.freeLevel (deleteAt m v)) := by
  exact (A.E_iff_freeLevel
    (deleteAt m u) (deleteAt m v)).trans
    (deleteAt_lt_iff_lt_deleteAtCut m
      (A.freeLevel (deleteAt m v)) u)

/-- The transported free cut is genuinely the FIRST missing E
coordinate in the induced shortened E relation. -/
theorem deleteAtE_isFreeCut
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (m v : Nat) :
    IsFreeCut (deleteAtE A m) v
      (deleteAtCut m (A.freeLevel (deleteAt m v))) := by
  let c := deleteAtCut m (A.freeLevel (deleteAt m v))
  have hiff : ∀ u, deleteAtE A m u v = true ↔ u < c := by
    intro u
    exact deleteAtE_iff_cut A m u v
  constructor
  · intro u hu
    exact (hiff u).2 hu
  · cases he : deleteAtE A m c v with
    | false => rfl
    | true =>
        have bad : c < c := (hiff c).1 he
        exact False.elim ((Nat.lt_irrefl c) bad)

/-- Under the sharp spacing guard, the canonical free level
inside the new partial structure equals its exact transported
initial-segment cut. -/
theorem deleteAtPartial_freeLevel_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (m : Nat)
    (hnext : m + 1 < A.size)
    (hfree : A.freeLevel (m + 1) < m)
    (v : Nat) :
    (deleteAtPartial A m hnext hfree).freeLevel v =
      deleteAtCut m (A.freeLevel (deleteAt m v)) := by
  let B := deleteAtPartial A m hnext hfree
  let c := deleteAtCut m (A.freeLevel (deleteAt m v))
  have hCut : IsFreeCut B.E v c := by
    change IsFreeCut (deleteAtE A m) v
      (deleteAtCut m (A.freeLevel (deleteAt m v)))
    exact deleteAtE_isFreeCut A m v
  exact freeCut_unique B.E v (B.freeLevel v) c
    (canonicalFreeLevel_isFreeCut B.E B.spaced B.downward v)
    hCut

/-- Free level can decrease by at most one when deleting a
single old coordinate; the exact value is already above. -/
theorem deleteAtPartial_freeLevel_bounds
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (m : Nat)
    (hnext : m + 1 < A.size)
    (hfree : A.freeLevel (m + 1) < m)
    (v : Nat) :
    A.freeLevel (deleteAt m v) - 1 ≤
        (deleteAtPartial A m hnext hfree).freeLevel v ∧
      (deleteAtPartial A m hnext hfree).freeLevel v ≤
        A.freeLevel (deleteAt m v) := by
  rw [deleteAtPartial_freeLevel_eq]
  unfold deleteAtCut
  split_ifs <;> omega

end SuccessorTree.V10

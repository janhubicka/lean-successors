import SuccessorTree.V10.LocalAgeNeutralIndependence
import Mathlib.Tactic

/-!
# Every admissible Kpt type above ell admits an inserted neutral image

We now bridge from literal finite partial structures to the actual
normalized admissible Kpt family. Starting with a forbidden-free witness
of a type at level cut>=ell>0, insert the neutral ordinary vertex ell.
The new partial structure is forbidden-free; the shifted original has
canonical free level cut+1; hence its complete type is an admissible Kpt
node at exactly that new level.

A noncomputable witness-based selector supplies a TOTAL operation on the
admissible nodes above ell. This file establishes existence and exact
level transport, but does NOT yet assert that this selector is
representation-independent, prefix-preserving or shape-preserving.
The separate full-record uniqueness theorem is available in the imported
LocalAgeNeutralIndependence module for the next step.
-/

namespace SuccessorTree.V10

/-- Canonical E free levels on all retained vertices are exactly transported
through a neutral coordinate insertion. -/
theorem neutralInsert_freeLevel_old
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (v : Nat) (hv : v < A.size) :
    (neutralInsert A ell hell hellPos).freeLevel (insertAddress ell v) =
      if A.freeLevel v < ell then A.freeLevel v else A.freeLevel v + 1 := by
  have hBelow :
      ∀ x, x < ell →
        (∃ r : Fin db,
          (neutralInsertedLData db du dd).incoming x r = true ∨
          (neutralInsertedLData db du dd).outgoing x r = true) →
        x < 0 := by
    intro x hx ⟨r, hr⟩
    simp [neutralInsertedLData] at hr
  have hAbove :
      ∀ y, ell ≤ y → y < A.size →
        (∃ r : Fin db,
          (neutralInsertedLData db du dd).outgoing y r = true ∨
          (neutralInsertedLData db du dd).incoming y r = true) →
        ell ≤ A.freeLevel y := by
    intro y hy hsize ⟨r, hr⟩
    simp [neutralInsertedLData] at hr
  exact insertPartial_freeLevel_old A ell 0
    (neutralInsertedLData db du dd)
    hell hellPos (Nat.zero_le ell) (Or.inl rfl)
    hBelow hAbove v hv

/-- A concrete neutral image of an admissible node is represented by
shifting an original vertex in a forbidden-free neutral insertion of a
witnessing finite partial structure. -/
def IsNeutralKptImage
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a b : AdmissibleKptNode family) : Prop :=
  ∃ (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (hell : ell ≤ A.size),
    v < A.size ∧
    (∀ bad, bad ∈ family → bad.Avoids A.L) ∧
    a.1 = A.rawTypeAtFree v ∧
    b.1 = (neutralInsert A ell hell hellPos).rawTypeAtFree
      (insertAddress ell v)

/-- A genuine type at level at least ell has a forbidden-free neutral image
at level exactly one higher. No new admissibility axiom is imposed. -/
theorem neutralKptImage_exists
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a : AdmissibleKptNode family)
    (hlev : ell ≤ a.1.1) :
    ∃ b : AdmissibleKptNode family,
      IsNeutralKptImage family ell hellPos a b ∧
      b.1.1 = a.1.1 + 1 := by
  obtain ⟨A, v, hv, hAvoid, hRaw⟩ := a.2
  have hSourceLev : a.1.1 = A.freeLevel v :=
    congrArg Sigma.fst hRaw
  have hOldCut : ell ≤ A.freeLevel v := by omega
  have hell : ell ≤ A.size := by
    have hf := A.freeLevel_le v
    omega
  let B := neutralInsert A ell hell hellPos
  have hvGE : ell ≤ v := le_trans hOldCut (A.freeLevel_le v)
  have hvB : insertAddress ell v < B.size := by
    change insertAddress ell v < A.size + 1
    rw [insertAddress_above ell v hvGE]
    omega
  have hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L :=
    neutralInsert_preserves_avoidance family A ell hell hellPos hAvoid
  have hAdB : IsAdmissibleRawType family
      (B.rawTypeAtFree (insertAddress ell v)) :=
    ⟨B, insertAddress ell v, hvB, hAvoidB, rfl⟩
  let b : AdmissibleKptNode family :=
    ⟨B.rawTypeAtFree (insertAddress ell v), hAdB⟩
  refine ⟨b, ?_, ?_⟩
  · exact ⟨A, v, hell, hv, hAvoid, hRaw, rfl⟩
  · change B.freeLevel (insertAddress ell v) = a.1.1 + 1
    have hEq : B.freeLevel (insertAddress ell v) =
        A.freeLevel v + 1 := by
      have h := neutralInsert_freeLevel_old A ell hell hellPos v hv
      simpa [B, Nat.not_lt.mpr hOldCut] using h
    omega

/-- A selected neutral image of a Kpt node above ell. The next theorem
will prove that its value is independent of its chosen ambient witness. -/
noncomputable def neutralKptImage
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a : AdmissibleKptNode family) (hlev : ell ≤ a.1.1) :
    AdmissibleKptNode family :=
  Classical.choose (neutralKptImage_exists family ell hellPos a hlev)

/-- The chosen image is genuinely represented by a forbidden-free inserted
structure; this does not merely assert a level in a raw type tree. -/
theorem neutralKptImage_isImage
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a : AdmissibleKptNode family) (hlev : ell ≤ a.1.1) :
    IsNeutralKptImage family ell hellPos a
      (neutralKptImage family ell hellPos a hlev) :=
  (Classical.choose_spec (neutralKptImage_exists family ell hellPos a hlev)).1

/-- The new Kpt node lies at the strictly next source level, with the
insertion's single omitted target level accounted for. -/
theorem neutralKptImage_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a : AdmissibleKptNode family) (hlev : ell ≤ a.1.1) :
    (neutralKptImage family ell hellPos a hlev).1.1 = a.1.1 + 1 :=
  (Classical.choose_spec (neutralKptImage_exists family ell hellPos a hlev)).2

end SuccessorTree.V10

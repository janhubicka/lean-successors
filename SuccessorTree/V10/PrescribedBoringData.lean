import SuccessorTree.V10.PrescribedAdmissibleCut
import Mathlib.Tactic

/-!
# The prescribed B1/B2 extension data on actual finite partial-type records

Lemma 6.51 supplies a partial function f on a family of level-ell Kpt
types, preserving its old predecessor (B1) and ordinary-socle
compatibility (B2).

This module formalizes EXACTLY those two conditions on the complete L+
records, with the distinguished type vertex excluded from compatibility.
No stronger equality of the type vertices is assumed.

The key conclusion: for any source type T at level ell, if one or more
prescribed types are compatible with T, the inserted ordinary L-column
chosen from a matching f(S) is INDEPENDENT of the representative S.
If none is compatible, the selection is absent (the permitted neutral
fallback will be used by the full boring-extension construction).

This is the real type-safe source of choice independence in Step 2 of the
printed boring-extension proof, as opposed to assuming an arbitrary
preselected lower column is consistent.
-/

namespace SuccessorTree.V10

/-- Ordinary-only L+ compatibility at a given socle length. Unlike equality
of full partial-type records, it ignores the distinguished type vertex t. -/
def SameOrdinaryAtCut
    {n db du dd : Nat}
    (Q R : PartialTypeWithE n db du dd) : Prop :=
  (∀ i j : Fin n, ∀ t : Fin db,
    Q.lReduct.binary (some i) (some j) t =
      R.lReduct.binary (some i) (some j) t) ∧
  (∀ i : Fin n, ∀ t : Fin du,
    Q.lReduct.unary (some i) t =
      R.lReduct.unary (some i) t) ∧
  (∀ i : Fin n, ∀ t : Fin dd,
    Q.lReduct.diagonal (some i) t =
      R.lReduct.diagonal (some i) t) ∧
  (∀ i j : Fin n,
    Q.eRelation (some i) (some j) =
      R.eRelation (some i) (some j))

theorem sameOrdinaryAtCut_refl
    {n db du dd : Nat}
    (Q : PartialTypeWithE n db du dd) :
    SameOrdinaryAtCut Q Q := by
  exact ⟨by intros; rfl, by intros; rfl,
    by intros; rfl, by intros; rfl⟩

theorem sameOrdinaryAtCut_symm
    {n db du dd : Nat}
    {Q R : PartialTypeWithE n db du dd}
    (h : SameOrdinaryAtCut Q R) :
    SameOrdinaryAtCut R Q := by
  exact ⟨fun i j t => (h.1 i j t).symm,
    fun i t => (h.2.1 i t).symm,
    fun i t => (h.2.2.1 i t).symm,
    fun i j => (h.2.2.2 i j).symm⟩

theorem sameOrdinaryAtCut_trans
    {n db du dd : Nat}
    {Q R S : PartialTypeWithE n db du dd}
    (hQR : SameOrdinaryAtCut Q R)
    (hRS : SameOrdinaryAtCut R S) :
    SameOrdinaryAtCut Q S := by
  exact ⟨fun i j t => (hQR.1 i j t).trans (hRS.1 i j t),
    fun i t => (hQR.2.1 i t).trans (hRS.2.1 i t),
    fun i t => (hQR.2.2.1 i t).trans (hRS.2.2.1 i t),
    fun i j => (hQR.2.2.2 i j).trans (hRS.2.2.2 i j)⟩

/-- A genuine B1/B2 system on level-ell full L+ records.
The source is a SET (possibly empty); f is total outside it only for
coding convenience. No condition on values outside source is used. -/
structure PrescribedBoringData (ell db du dd : Nat) where
  source : Set (PartialTypeWithE ell db du dd)
  target : PartialTypeWithE ell db du dd →
    PartialTypeWithE (ell + 1) db du dd
  extends : ∀ T, T ∈ source →
    (target T).restrict (Nat.le_succ ell) = T
  preservesCompatibility :
    ∀ T U, T ∈ source → U ∈ source →
    SameOrdinaryAtCut T U →
      SameOrdinarySocle (target T) (target U)

/-- Two prescribed inputs compatible with the SAME original lower type
must have compatible output socles by B2, even if their distinguished
type vertices and terminal letters differ. -/
theorem PrescribedBoringData.outputs_compatible
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (T U V : PartialTypeWithE ell db du dd)
    (hT : T ∈ F.source) (hU : U ∈ F.source)
    (hTV : SameOrdinaryAtCut T V)
    (hUV : SameOrdinaryAtCut U V) :
    SameOrdinarySocle (F.target T) (F.target U) := by
  have hTU := sameOrdinaryAtCut_trans hTV
    (sameOrdinaryAtCut_symm hUV)
  exact F.preservesCompatibility T U hT hU hTU

/-- Choice of matching prescribed source cannot affect the complete
lower L-column; this includes every positive and negative directed bit
plus the unary, diagonal and loop information. -/
theorem PrescribedBoringData.lower_column_unique
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (T U V : PartialTypeWithE ell db du dd)
    (hT : T ∈ F.source) (hU : U ∈ F.source)
    (hTV : SameOrdinaryAtCut T V)
    (hUV : SameOrdinaryAtCut U V) :
    lowerInsertedColumn (F.target T) =
      lowerInsertedColumn (F.target U) := by
  exact lowerInsertedColumn_eq_of_sameSocle
    (F.outputs_compatible T U V hT hU hTV hUV)

/-- There is a prescribed source compatible with the ordinary initial
socle of T. This existential is about the source FAMILY, not all possible
raw types in Kpt. -/
def PrescribedBoringData.HasCompatibleSource
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (T : PartialTypeWithE ell db du dd) : Prop :=
  ∃ S, S ∈ F.source ∧ SameOrdinaryAtCut S T

/-- The canonical LOWER column chosen from a compatible prescribed source,
or none if no such source exists. Only the lower ordinary column is chosen,
not the whole upper type (which can genuinely depend on S). -/
noncomputable def PrescribedBoringData.selectedLowerColumn
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (T : PartialTypeWithE ell db du dd) :
    Option (LowerInsertedColumn ell db du dd) :=
  if h : F.HasCompatibleSource T then
    some (lowerInsertedColumn (F.target (Classical.choose h)))
  else none

/-- The selected lower column is literally the column of ANY compatible
prescribed output. This removes the choice of witness from the statement
of Step 2 of Lemma 6.51. -/
theorem PrescribedBoringData.selectedLowerColumn_eq
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (T S : PartialTypeWithE ell db du dd)
    (hS : S ∈ F.source) (hComp : SameOrdinaryAtCut S T) :
    F.selectedLowerColumn T =
      some (lowerInsertedColumn (F.target S)) := by
  classical
  have hExists : F.HasCompatibleSource T := ⟨S,hS,hComp⟩
  have hChosen := Classical.choose_spec hExists
  have hLowEq := F.lower_column_unique
    (Classical.choose hExists) S T
    hChosen.1 hS hChosen.2 hComp
  unfold PrescribedBoringData.selectedLowerColumn
  rw [dif_pos hExists]
  exact congrArg Option.some hLowEq

/-- If no prescribed source is compatible with the ordinary socle,
Step 2 makes no new ordinary L-column; the subsequent neutral case
is mandatory rather than an arbitrary choice. -/
theorem PrescribedBoringData.selectedLowerColumn_none
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (T : PartialTypeWithE ell db du dd)
    (hNone : ¬ F.HasCompatibleSource T) :
    F.selectedLowerColumn T = none := by
  simp [PrescribedBoringData.selectedLowerColumn, hNone]

end SuccessorTree.V10

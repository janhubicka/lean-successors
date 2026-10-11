import SuccessorTree.V10.ExtractedSuccessorS2
import Mathlib.Tactic

/-!
# Eliminate the spurious level-zero successor parameter

Definition 6.30 insists the successor parameter list is either empty or
a singleton whose type has POSITIVE level. This is necessary for S2:
a level-zero parameter contains no socle and duplicates the empty
parameter representation.

The previous complete-record S2 theorem compared a parameter record
even when the cut f=0. Here we remove that artificial hypothesis:
for f=0, equality of the terminal Sigma letters itself implies
equality of the level-zero 'last ordinary vertex' record. The actual
canonical input is an Option:
  * none for free level 0;
  * some (f, complete type) for f>0.

We also prove uniqueness of a free E cut from the exact old-to-new
E column. Thus the finite S2 uniqueness theorem uses exactly the
empty-or-positive-singleton convention of the manuscript, without
an unverified level-zero parameter or a new structural axiom.

A separate link to the actual forward S is still needed to convert
this into the published unconditional S-tree statement.
-/

namespace SuccessorTree.V10

/-- At free cut zero, the new vertex's entire singleton type is
already recorded in its terminal Sigma-letter. There is no extra
parameter information to compare. -/
theorem zero_parameter_eq_of_terminal_letter
    {ell db du dd : Nat}
    (Q R : PartialTypeWithE (ell + 1) db du dd)
    (hLetter : Q.terminalLetter = R.terminalLetter) :
    Q.lastOrdinaryParameter 0 (Nat.zero_le ell) =
      R.lastOrdinaryParameter 0 (Nat.zero_le ell) := by
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y r
      cases x with
      | none =>
        cases y with
        | none =>
          exact congrArg
            (fun T : PartialTypeWithE 1 db du dd =>
              T.lReduct.binary (some 0) (some 0) r) hLetter
        | some y => exact y.elim0
      | some x => exact x.elim0
    · intro x r
      cases x with
      | none =>
        exact congrArg
          (fun T : PartialTypeWithE 1 db du dd =>
            T.lReduct.unary (some 0) r) hLetter
      | some x => exact x.elim0
    · intro x r
      cases x with
      | none =>
        exact congrArg
          (fun T : PartialTypeWithE 1 db du dd =>
            T.lReduct.diagonal (some 0) r) hLetter
      | some x => exact x.elim0
  · intro x y
    cases x with
    | none =>
      cases y with
      | none =>
        exact congrArg
          (fun T : PartialTypeWithE 1 db du dd =>
            T.eRelation (some 0) (some 0)) hLetter
      | some y => exact y.elim0
    | some x => exact x.elim0

/-- The precise parameter convention of Definition 6.30, as a list
of length at most one. The singleton case has strictly positive cut. -/
def PartialTypeWithE.canonicalParameterRecord
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (f : Nat) (hf : f ≤ ell) :
    Option (RawPartialTypeNode db du dd) :=
  if f = 0 then none else
    some ⟨f, Q.lastOrdinaryParameter f hf⟩

/-- For f=0 the canonical parameter is empty, regardless of the
otherwise redundant level-zero type. -/
theorem canonicalParameterRecord_zero
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd) :
    Q.canonicalParameterRecord 0 (Nat.zero_le ell) = none := by
  simp [PartialTypeWithE.canonicalParameterRecord]

/-- The canonical record is present precisely at positive free cut. -/
theorem canonicalParameterRecord_some_iff_pos
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (f : Nat) (hf : f ≤ ell) :
    Q.canonicalParameterRecord f hf ≠ none ↔ 0 < f := by
  by_cases h : f = 0
  · simp [PartialTypeWithE.canonicalParameterRecord, h]
  · have hp : 0 < f := by omega
    simp [PartialTypeWithE.canonicalParameterRecord, h, hp]

/-- Equality of canonical EMPTY-or-POSITIVE-SINGLETON parameters and
terminal letters yields equality of the underlying full parameter
records, including when the parameter was empty. -/
theorem full_parameter_eq_of_canonical_option
    {ell db du dd : Nat}
    (Q R : PartialTypeWithE (ell + 1) db du dd)
    (f : Nat) (hf : f ≤ ell)
    (hOption :
      Q.canonicalParameterRecord f hf =
        R.canonicalParameterRecord f hf)
    (hLetter : Q.terminalLetter = R.terminalLetter) :
    Q.lastOrdinaryParameter f hf =
      R.lastOrdinaryParameter f hf := by
  by_cases h : f = 0
  · subst f
    exact zero_parameter_eq_of_terminal_letter Q R hLetter
  · have hSome : (⟨f, Q.lastOrdinaryParameter f hf⟩ :
        RawPartialTypeNode db du dd) =
      (⟨f, R.lastOrdinaryParameter f hf⟩ :
        RawPartialTypeNode db du dd) := by
      have hh := hOption
      simp only [PartialTypeWithE.canonicalParameterRecord,
        if_neg h] at hh
      exact Option.some.inj hh
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hSome

/-- The free cut of a new ordinary vertex is uniquely determined
by its complete E column. Positive and empty parameter cases
cannot have the same complete successor record. -/
theorem validNewColumn_freeCut_unique
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (f g : Nat) (hf : f ≤ ell) (hg : g ≤ ell)
    (hF : ValidNewOrdinaryColumn Q f)
    (hG : ValidNewOrdinaryColumn Q g) :
    f = g := by
  by_contra hne
  have hCases : f < g ∨ g < f := by omega
  rcases hCases with hfg | hgf
  · let i : Fin ell := ⟨f, by omega⟩
    have hh := (hF.oldToNewE i).symm.trans (hG.oldToNewE i)
    have hfFalse : decide (i.val < f) = false := by simp [i]
    have hgTrue : decide (i.val < g) = true := by simp [i, hfg]
    rw [hfFalse, hgTrue] at hh
    contradiction
  · let i : Fin ell := ⟨g, by omega⟩
    have hh := (hF.oldToNewE i).symm.trans (hG.oldToNewE i)
    have hfTrue : decide (i.val < f) = true := by simp [i, hgf]
    have hgFalse : decide (i.val < g) = false := by simp [i]
    rw [hfTrue, hgFalse] at hh
    contradiction

/-- Complete finite S2 uniqueness in the exact convention of the
paper: a zero free cut means NO parameter; a positive cut carries
a singleton parameter. The predecessor and Sigma-letter uniquely
determine the entire complete successor L+ type. -/
theorem complete_successor_unique_of_option_parameter
    {ell db du dd : Nat}
    (Q R : PartialTypeWithE (ell + 1) db du dd)
    (f : Nat) (hf : f ≤ ell)
    (hOld : Q.restrict (Nat.le_succ ell) =
      R.restrict (Nat.le_succ ell))
    (hQ : ValidNewOrdinaryColumn Q f)
    (hR : ValidNewOrdinaryColumn R f)
    (hParamOption :
      Q.canonicalParameterRecord f hf =
        R.canonicalParameterRecord f hf)
    (hLetter : Q.terminalLetter = R.terminalLetter) :
    Q = R := by
  exact complete_successor_unique_of_canonical_inputs
    Q R f hf hOld hQ hR
    (full_parameter_eq_of_canonical_option
      Q R f hf hParamOption hLetter) hLetter

end SuccessorTree.V10

import SuccessorTree.V10.PrescribedUpperLType
import Mathlib.Tactic

/-!
# All linked upper vertices have prescribed f-types, with no extra choice

Every old upper vertex u has the complete source type type_A^ell(u).
The prescribed partial function f is applied to precisely those source
types in its domain; all other terminal relations to the inserted vertex
are zero. Independently, B2 chooses ONE ordinary lower L-column common
to compatible f outputs.

All ordinary types extracted from the SAME ambient A share precisely the
same original first ell vertices. Therefore if the selected lower column
came from a prescribed type compatible with A, the lower column agrees
with EVERY upper f(type_A^ell(u)) for which the latter is defined.

This module proves:
* upper directed bits are genuinely those of the prescribed target f(T);
* if an upper vertex is L-linked to the inserted coordinate, its source
  type T lies in f's prescribed domain (otherwise both links are zero);
* the newly inserted finite L model realizes exactly f(T)'s COMPLETE
  L-type through ell+1, including absent directed atoms and singleton
  data, using B1 and the finite reconstruction theorem.

These facts discharge the nontrivial upper-type selection input of the
three-clause finite age test. The common initial socle and construction
of the final global Kpt shape map remain separate obligations.
-/

namespace SuccessorTree.V10

/-- The ordinary socle of type_A^ell(u) is independent of u. Every
Boolean L-atom, including absent tuples, and every E-pair is identical
because the distinguished type vertex does not appear in them. -/
theorem sameOrdinaryAtCut_sameAmbient
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell u v : Nat) :
    SameOrdinaryAtCut (A.partialTypeAt ell u)
      (A.partialTypeAt ell v) := by
  exact ⟨by intros; rfl, by intros; rfl,
    by intros; rfl, by intros; rfl⟩

/-- The prescribed upper-to-new binary bit for an old vertex u; zero when
its complete source type is outside the prescribed domain. -/
noncomputable def PrescribedBoringData.upperIncoming
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (u : Nat) (t : Fin db) : Bool := by
  classical
  exact if h : A.partialTypeAt ell u ∈ F.source then
    (F.target (A.partialTypeAt ell u)).lReduct.binary
      none (some (Fin.last ell)) t
  else false

/-- The prescribed new-to-upper binary bit, with the opposite direction
retained independently (the relational language need not be symmetric). -/
noncomputable def PrescribedBoringData.upperOutgoing
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (u : Nat) (t : Fin db) : Bool := by
  classical
  exact if h : A.partialTypeAt ell u ∈ F.source then
    (F.target (A.partialTypeAt ell u)).lReduct.binary
      (some (Fin.last ell)) none t
  else false

/-- Gated insertion data with the lower column chosen once and all upper
terminal bits canonically read from f on their actual source types. -/
noncomputable def PrescribedBoringData.insertedLData
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (P : LowerInsertedColumn ell db du dd) :
    InsertedLData db du dd :=
  gatedInsertedLData A P (F.upperIncoming A) (F.upperOutgoing A)

/-- If an upper vertex is linked to the newly inserted vertex, its old
level-ell type lies IN the prescribed source domain. A type absent from
that domain cannot have either incident directed binary relation. -/
theorem PrescribedBoringData.linked_upper_in_source
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (P : LowerInsertedColumn ell db du dd)
    (u : Nat) (hu : ell ≤ u)
    (hLink : ∃ t : Fin db,
      (F.insertedLData A P).outgoing u t = true ∨
      (F.insertedLData A P).incoming u t = true) :
    A.partialTypeAt ell u ∈ F.source := by
  by_contra hn
  have hnot : ¬ u < ell := Nat.not_lt.mpr hu
  have hZero : ∀ t : Fin db,
      (F.insertedLData A P).outgoing u t = false ∧
      (F.insertedLData A P).incoming u t = false := by
    intro t
    by_cases hGate : ell ≤ A.freeLevel u
    · simp [PrescribedBoringData.insertedLData,
        gatedInsertedLData, hnot, hGate,
        PrescribedBoringData.upperOutgoing,
        PrescribedBoringData.upperIncoming, hn]
    · simp [PrescribedBoringData.insertedLData,
        gatedInsertedLData, hnot, hGate]
  obtain ⟨t, hb⟩ := hLink
  rcases hb with hb | hb
  · exact Bool.false_ne_true ((hZero t).1.symm.trans hb)
  · exact Bool.false_ne_true ((hZero t).2.symm.trans hb)

/-- The chosen lower column from any matching f-input is automatically
the lower column required by every other prescribed input T from the
same ambient partial structure, by EXACTLY compatibility condition B2. -/
theorem PrescribedBoringData.lowerColumn_of_matchedAmbient
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (base u : Nat)
    (P : LowerInsertedColumn ell db du dd)
    (hSelected :
      F.selectedLowerColumn (A.partialTypeAt ell base) = some P)
    (hU : A.partialTypeAt ell u ∈ F.source) :
    P = lowerInsertedColumn (F.target (A.partialTypeAt ell u)) := by
  have hEq := F.selectedLowerColumn_eq
    (A.partialTypeAt ell base) (A.partialTypeAt ell u)
    hU (sameOrdinaryAtCut_sameAmbient A ell u base)
  rw [hSelected] at hEq
  exact Option.some.inj hEq

/-- Given a matching selected ordinary lower column, and an upper type
on which f is defined whose original E-cut reaches ell, ALL seven data
fields required for the prescribed upper type reconstruction follow
from the actual f-output and the gated inserted column. -/
theorem PrescribedBoringData.insertedLData_matches_upper
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (base u : Nat)
    (P : LowerInsertedColumn ell db du dd)
    (hu : ell ≤ u)
    (hFree : ell ≤ A.freeLevel u)
    (hSelected :
      F.selectedLowerColumn (A.partialTypeAt ell base) = some P)
    (hU : A.partialTypeAt ell u ∈ F.source) :
    (F.insertedLData A P).MatchesPrescribedUpper
      (F.target (A.partialTypeAt ell u)) u := by
  have hP := F.lowerColumn_of_matchedAmbient A base u P hSelected hU
  unfold InsertedLData.MatchesPrescribedUpper
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    simpa [PrescribedBoringData.insertedLData,
      gatedInsertedLData, hP, lowerInsertedColumn]
  · intro t
    simpa [PrescribedBoringData.insertedLData,
      gatedInsertedLData, hP, lowerInsertedColumn]
  · intro t
    simpa [PrescribedBoringData.insertedLData,
      gatedInsertedLData, hP, lowerInsertedColumn]
  · intro i t
    simp [PrescribedBoringData.insertedLData,
      gatedInsertedLData, i.isLt, hP, lowerInsertedColumn]
    congr 2
  · intro i t
    simp [PrescribedBoringData.insertedLData,
      gatedInsertedLData, i.isLt, hP, lowerInsertedColumn]
    congr 2
  · intro t
    have hn : ¬ u < ell := Nat.not_lt.mpr hu
    simp [PrescribedBoringData.insertedLData, gatedInsertedLData,
      hn, hFree, PrescribedBoringData.upperIncoming, hU]
  · intro t
    have hn : ¬ u < ell := Nat.not_lt.mpr hu
    simp [PrescribedBoringData.insertedLData, gatedInsertedLData,
      hn, hFree, PrescribedBoringData.upperOutgoing, hU]

/-- B1 and B2 together establish actual complete L-type realization of
EVERY upper vertex whose source type belongs to f's domain, provided the
selected lower column matches this ambient socle and its E-cut reaches ell. -/
theorem PrescribedBoringData.upper_realizes_target_L
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (base u : Nat)
    (P : LowerInsertedColumn ell db du dd)
    (hu : ell ≤ u) (hFree : ell ≤ A.freeLevel u)
    (hSelected :
      F.selectedLowerColumn (A.partialTypeAt ell base) = some P)
    (hU : A.partialTypeAt ell u ∈ F.source) :
    RelationalPrefixType.ofAgeModel (insertL A ell (F.insertedLData A P))
      (ell + 1) (insertAddress ell u) =
      (F.target (A.partialTypeAt ell u)).lReduct := by
  let T := A.partialTypeAt ell u
  have hOld :
      (F.target T).lReduct.restrict (Nat.le_succ ell) =
        (A.partialTypeAt ell u).lReduct := by
    have h := congrArg PartialTypeWithE.lReduct
      (F.extendsSource T hU)
    simpa [T, PartialTypeWithE.restrict] using h
  exact insertL_realizes_prescribed_upper_L_type A
    (F.insertedLData A P) u hu (F.target T) hOld
    (F.insertedLData_matches_upper A base u P hu hFree hSelected hU)

/-- The PRECISE B3 premise is now derived: if an upper vertex is linked
to the inserted coordinate in either direction, its complete L-type
through ell+1 belongs to the L-reducts of the prescribed f[S] outputs.
There is no E relation in this age-test conclusion. -/
theorem PrescribedBoringData.linked_upper_has_prescribed_L_type
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (base u : Nat)
    (P : LowerInsertedColumn ell db du dd)
    (hu : ell ≤ u) (huSize : u < A.size)
    (hSelected :
      F.selectedLowerColumn (A.partialTypeAt ell base) = some P)
    (hLink : ∃ t : Fin db,
      (F.insertedLData A P).outgoing u t = true ∨
      (F.insertedLData A P).incoming u t = true) :
    ∃ T, T ∈ F.source ∧
      RelationalPrefixType.ofAgeModel
        (insertL A ell (F.insertedLData A P))
        (ell + 1) (insertAddress ell u) =
        (F.target T).lReduct := by
  have hMem : A.partialTypeAt ell u ∈ F.source :=
    F.linked_upper_in_source A P u hu hLink
  have hGate : ell ≤ A.freeLevel u :=
    gatedInsertedLData_above A P
      (F.upperIncoming A) (F.upperOutgoing A)
      u hu huSize hLink
  exact ⟨A.partialTypeAt ell u, hMem,
    F.upper_realizes_target_L A base u P hu hGate hSelected hMem⟩

end SuccessorTree.V10

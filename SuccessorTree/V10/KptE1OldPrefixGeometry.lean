import SuccessorTree.V10.KptE1OldNewColumnConsequences
import SuccessorTree.V10.M2SourceTypeAge
import SuccessorTree.V10.PartialTypeRestriction
import Mathlib.Tactic

/-!
# The inherited old Kpt E columns come from a genuine admissible source

In the concrete E1 reconstruction, the old predecessor a is a genuine
admissible Kpt type: it has an actual enumerated L+ partial-structure
witness A, not merely an arbitrary finite L/E table. If the candidate
new type Q restricts *literally* to A.partialTypeAt n w, the complete
old-old L and E atoms of Q are those of A on the initial n vertices.

Consequently the canonical free-cut function v ↦ A.freeLevel v
supplies (i) strict spacing for every old column, (ii) exact old E
bits, including negative bits and (iii) linkedness of every old-old
directed L pair. Together with the real ValidNewOrdinaryColumn from
KptE1ShapeLevelCut these facts discharge the ENTIRE padded E1
ordinary-column linkedness and E-matrix premises.

The remaining nontrivial source-E1 obligation is to prove that a
target shape map's canonical successor really has the required
literal source predecessor restriction; no new E1 axiom is used here.
-/

namespace SuccessorTree.V10

/-- The actual restricted complete predecessor preserves every old
L binary bit (positive and absent) as a literal statement on the
finite initial carrier. -/
theorem e1OldPrefix_binary_from_witness
    {db du dd : Nat} {n : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (w : Nat)
    (Q : PartialTypeWithE (n + 1) db du dd)
    (hPrefix :
      Q.restrict (Nat.le_succ n) = A.partialTypeAt n w)
    (u v : Nat) (hu : u < n) (hv : v < n)
    (r : Fin db) :
    Q.ageModel.binary u v r = A.L.binary u v r := by
  have h := congrArg
    (fun T : PartialTypeWithE n db du dd =>
      T.lReduct.binary
        (some (⟨u, hu⟩ : Fin n)) (some (⟨v, hv⟩ : Fin n)) r)
    hPrefix
  have hU : typeAgeIndex (n + 1) u =
      some (⟨u, Nat.lt_succ_of_lt hu⟩ : Fin (n + 1)) := by
    simp [typeAgeIndex, Nat.lt_succ_of_lt hu]
  have hV : typeAgeIndex (n + 1) v =
      some (⟨v, Nat.lt_succ_of_lt hv⟩ : Fin (n + 1)) := by
    simp [typeAgeIndex, Nat.lt_succ_of_lt hv]
  change Q.lReduct.binary (typeAgeIndex (n + 1) u)
    (typeAgeIndex (n + 1) v) r = A.L.binary u v r
  rw [hU, hV]
  simpa [PartialTypeWithE.restrict, RelationalPrefixType.restrict,
    liftTypeCoordinate, EnumeratedPartialStructure.partialTypeAt,
    RelationalPrefixType.ofAgeModel, prefixVertexIndex] using h

/-- The inherited source E bits agree *exactly* with the actual
E relation of the admissibility witness, not merely the positive
pairs or its L-only forbidden-age reduction. -/
theorem e1OldPrefix_E_from_witness
    {db du dd : Nat} {n : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (w : Nat)
    (Q : PartialTypeWithE (n + 1) db du dd)
    (hPrefix :
      Q.restrict (Nat.le_succ n) = A.partialTypeAt n w)
    (i j : Fin n) :
    Q.eRelation (some i.castSucc) (some j.castSucc) =
      A.E i.val j.val := by
  have h := congrArg
    (fun T : PartialTypeWithE n db du dd =>
      T.eRelation (some i) (some j)) hPrefix
  change Q.eRelation (some i.castSucc) (some j.castSucc) =
    A.E i.val j.val at h
  exact h

/-- Every genuine old free-level column of an enumerated partial
structure is empty or has its first free coordinate STRICTLY
earlier than its vertex. -/
theorem e1OldPrefix_freeCut_spaced
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n : Nat) :
    ∀ v, v < n →
      A.freeLevel v = 0 ∨ A.freeLevel v < v := by
  intro v hv
  by_cases hz : A.freeLevel v = 0
  · exact Or.inl hz
  · right
    exact freeLevel_pos_lt_vertex A v (Nat.pos_of_ne_zero hz)

/-- The canonical actual cuts of the old source witness provide the
whole inherited ordinary E submatrix, with both true/false values. -/
theorem e1OldPrefix_E_profile
    {db du dd : Nat} {n : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (w : Nat)
    (Q : PartialTypeWithE (n + 1) db du dd)
    (hPrefix :
      Q.restrict (Nat.le_succ n) = A.partialTypeAt n w) :
    ∀ i j : Fin n,
      Q.eRelation (some i.castSucc) (some j.castSucc) =
        decide (i.val < A.freeLevel j.val) := by
  intro i j
  have hE := e1OldPrefix_E_from_witness A w Q hPrefix i j
  have hIff := A.E_iff_freeLevel i.val j.val
  by_cases h : i.val < A.freeLevel j.val
  · have hYes : A.E i.val j.val = true := hIff.mpr h
    simpa [hYes,h] using hE
  · have hNo : A.E i.val j.val = false := by
      cases hx : A.E i.val j.val with
      | false => rfl
      | true => exact False.elim (h (hIff.mp hx))
    simpa [hNo,h] using hE

/-- Old-old L-linkedness is inherited from the genuine E3 axiom
of the source witness A. It is NOT asserted for an arbitrary
L-only forbidden-age structure. -/
theorem e1OldPrefix_linked
    {db du dd : Nat} {n : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (w : Nat) (hw : w < A.size)
    (hFree : n ≤ A.freeLevel w)
    (Q : PartialTypeWithE (n + 1) db du dd)
    (hPrefix :
      Q.restrict (Nat.le_succ n) = A.partialTypeAt n w) :
    ∀ u v : Nat, u < v → v < n →
      (∃ r : Fin db,
        Q.ageModel.binary u v r = true ∨
        Q.ageModel.binary v u r = true) →
      u < A.freeLevel v := by
  intro u v huv hv hLink
  have hnSize : n ≤ w :=
    hFree.trans (A.freeLevel_le w)
  have hu : u < n := huv.trans hv
  have hvSize : v < A.size := by omega
  have huSize : u < A.size := by omega
  have hLinkA : ∃ r : Fin db,
      A.L.binary u v r = true ∨
      A.L.binary v u r = true := by
    obtain ⟨r, h⟩ := hLink
    refine ⟨r, ?_⟩
    rcases h with h | h
    · left
      rw [e1OldPrefix_binary_from_witness A w Q hPrefix u v hu hv r] at h
      exact h
    · right
      rw [e1OldPrefix_binary_from_witness A w Q hPrefix v u hv hu r] at h
      exact h
  have hE := A.linked_E u v huv huSize hvSize hLinkA
  exact (A.E_iff_freeLevel u v).mp hE

/-- The two remaining ordinary-source conditions are discharged
together: all columns from the actual source A, and the new one
from the real canonical successor's ValidNewOrdinaryColumn. -/
theorem e1PaddedOldNew_from_admissible_prefix
    {db du dd : Nat} {n : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (w : Nat) (hw : w < A.size)
    (hFree : n ≤ A.freeLevel w)
    (Q : PartialTypeWithE (n + 1) db du dd)
    (hPrefix :
      Q.restrict (Nat.le_succ n) = A.partialTypeAt n w)
    (f : Nat) (hGate : f = 0 ∨ f < n)
    (hValid : ValidNewOrdinaryColumn Q f)
    (hNewLoop :
      Q.eRelation (some (Fin.last n)) (some (Fin.last n)) = false) :
    E1PaddedOrdinaryLinked Q A.freeLevel f ∧
    (∀ i j : Fin (n + 1),
      Q.eRelation (some i) (some j) =
        decide (i.val < paddedE1FreeCutProfile
          n A.freeLevel f j.val)) := by
  have hOld : ∀ v, v < n →
      A.freeLevel v = 0 ∨ A.freeLevel v < v :=
    e1OldPrefix_freeCut_spaced A n
  constructor
  · exact e1PaddedOrdinaryLinked_of_old_and_validNew
      Q A.freeLevel f
      (e1OldPrefix_linked A w hw hFree Q hPrefix) hValid
  · exact e1PaddedColumns_of_oldE_and_validNew
      Q A.freeLevel f hOld hGate
      (e1OldPrefix_E_profile A w Q hPrefix)
      hValid hNewLoop

end SuccessorTree.V10

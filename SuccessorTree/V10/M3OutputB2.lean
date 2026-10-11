import SuccessorTree.V10.M3OrdinaryCoherence
import SuccessorTree.V10.PrescribedSocleColumn
import SuccessorTree.V10.PrescribedETransport
import Mathlib.Tactic

/-!
# M3 output B2: the complete ordinary L+ socle is choice-independent

The old ordinary L+ socle determines the copied old n free E-cut and
every new lower L atom (including both absent directed tuples and
singleton data). The actual gated middle insertion copies all old
ordinary L+ atoms and uses the same new E column given this cut.

Consequently two compatible source types, even when represented by
DIFFERENT finite partial structures and different distinguished type
vertices, produce outputs with the same entire ordinary L+ socle.
This is precisely the nontrivial B2 requirement for the eventual
source-defined M3 prescription, but does not yet construct that
prescription as a total function on admissible types.
-/

namespace SuccessorTree.V10

/-- The ordinary L+ output socle of the actual middle insertion is
independent of the finite representative and distinguished vertex
when the old ordinary level-ell source socles are compatible. -/
theorem middleCloneInsertPartial_sameOrdinarySocle
    {db du dd : Nat}
    (A C : EnumeratedPartialStructure db du dd)
    (ell n v w : Nat)
    (hellA : ell ≤ A.size) (hellC : ell ≤ C.size)
    (hn : n < ell)
    (hComp : SameOrdinaryAtCut
      (A.partialTypeAt ell v) (C.partialTypeAt ell w)) :
    SameOrdinarySocle
      ((middleCloneInsertPartial A ell n hellA hn).partialTypeAt
        (ell+1) (insertAddress ell v))
      ((middleCloneInsertPartial C ell n hellC hn).partialTypeAt
        (ell+1) (insertAddress ell w)) := by
  let B := middleCloneInsertPartial A ell n hellA hn
  let H := middleCloneInsertPartial C ell n hellC hn
  let DA := middleCloneInsertedLData A ell n
  let DC := middleCloneInsertedLData C ell n
  have hInsB : IsLInsertion A B ell :=
    middleCloneInsertPartial_isLInsertion A ell n hellA hn
  have hInsH : IsLInsertion C H ell :=
    middleCloneInsertPartial_isLInsertion C ell n hellC hn
  have hLB : B.L = insertL A ell DA := rfl
  have hLH : H.L = insertL C ell DC := rfl
  have hEB : B.E = insertE A ell (A.freeLevel n) :=
    middleCloneInsertPartial_E_eq A ell n hellA hn
  have hEH : H.E = insertE C ell (C.freeLevel n) :=
    middleCloneInsertPartial_E_eq C ell n hellC hn
  have hCut : A.freeLevel n = C.freeLevel n :=
    sameOrdinaryAtCut_oldFreeLevel_eq A C v w n hn hComp
  have hData := middleCloneInsertedLData_lower_eq_of_ordinaryCompatibility
    A C v w n hn hComp
  have hOldBinB (i j : Fin ell) (r : Fin db) :
      B.L.binary i.val j.val r = A.L.binary i.val j.val r := by
    have hh := hInsB.binary i.val j.val
      (lt_of_lt_of_le i.isLt hellA)
      (lt_of_lt_of_le j.isLt hellA) r
    simpa [insertAddress_below ell i.val i.isLt,
      insertAddress_below ell j.val j.isLt] using hh
  have hOldBinH (i j : Fin ell) (r : Fin db) :
      H.L.binary i.val j.val r = C.L.binary i.val j.val r := by
    have hh := hInsH.binary i.val j.val
      (lt_of_lt_of_le i.isLt hellC)
      (lt_of_lt_of_le j.isLt hellC) r
    simpa [insertAddress_below ell i.val i.isLt,
      insertAddress_below ell j.val j.isLt] using hh
  have hOldUnB (i : Fin ell) (r : Fin du) :
      B.L.unary i.val r = A.L.unary i.val r := by
    have hh := hInsB.unary i.val
      (lt_of_lt_of_le i.isLt hellA) r
    simpa [insertAddress_below ell i.val i.isLt] using hh
  have hOldUnH (i : Fin ell) (r : Fin du) :
      H.L.unary i.val r = C.L.unary i.val r := by
    have hh := hInsH.unary i.val
      (lt_of_lt_of_le i.isLt hellC) r
    simpa [insertAddress_below ell i.val i.isLt] using hh
  have hOldDiagB (i : Fin ell) (r : Fin dd) :
      B.L.diagonal i.val r = A.L.diagonal i.val r := by
    have hh := hInsB.diagonal i.val
      (lt_of_lt_of_le i.isLt hellA) r
    simpa [insertAddress_below ell i.val i.isLt] using hh
  have hOldDiagH (i : Fin ell) (r : Fin dd) :
      H.L.diagonal i.val r = C.L.diagonal i.val r := by
    have hh := hInsH.diagonal i.val
      (lt_of_lt_of_le i.isLt hellC) r
    simpa [insertAddress_below ell i.val i.isLt] using hh
  have hLoopB (r : Fin db) : B.L.binary ell ell r = DA.loop r := by
    rw [hLB]; simp [insertL]
  have hLoopH (r : Fin db) : H.L.binary ell ell r = DC.loop r := by
    rw [hLH]; simp [insertL]
  have hOutB (i : Fin ell) (r : Fin db) :
      B.L.binary ell i.val r = DA.outgoing i.val r := by
    rw [hLB]
    simp [insertL, removeInserted, Nat.ne_of_lt i.isLt, i.isLt]
  have hOutH (i : Fin ell) (r : Fin db) :
      H.L.binary ell i.val r = DC.outgoing i.val r := by
    rw [hLH]
    simp [insertL, removeInserted, Nat.ne_of_lt i.isLt, i.isLt]
  have hInB (i : Fin ell) (r : Fin db) :
      B.L.binary i.val ell r = DA.incoming i.val r := by
    rw [hLB]
    simp [insertL, removeInserted, Nat.ne_of_lt i.isLt, i.isLt]
  have hInH (i : Fin ell) (r : Fin db) :
      H.L.binary i.val ell r = DC.incoming i.val r := by
    rw [hLH]
    simp [insertL, removeInserted, Nat.ne_of_lt i.isLt, i.isLt]
  have hNewUnB (r : Fin du) : B.L.unary ell r = DA.unary r := by
    rw [hLB]; simp [insertL]
  have hNewUnH (r : Fin du) : H.L.unary ell r = DC.unary r := by
    rw [hLH]; simp [insertL]
  have hNewDiagB (r : Fin dd) :
      B.L.diagonal ell r = DA.diagonal r := by
    rw [hLB]; simp [insertL]
  have hNewDiagH (r : Fin dd) :
      H.L.diagonal ell r = DC.diagonal r := by
    rw [hLH]; simp [insertL]
  have hOldEB (i j : Fin ell) :
      B.E i.val j.val = A.E i.val j.val := by
    rw [hEB]
    have hh := insertE_old_pair_eq A ell (A.freeLevel n)
      hellA (by omega) i.val j.val
      (lt_of_lt_of_le i.isLt hellA)
      (lt_of_lt_of_le j.isLt hellA)
    simpa [insertAddress_below ell i.val i.isLt,
      insertAddress_below ell j.val j.isLt] using hh
  have hOldEH (i j : Fin ell) :
      H.E i.val j.val = C.E i.val j.val := by
    rw [hEH]
    have hh := insertE_old_pair_eq C ell (C.freeLevel n)
      hellC (by omega) i.val j.val
      (lt_of_lt_of_le i.isLt hellC)
      (lt_of_lt_of_le j.isLt hellC)
    simpa [insertAddress_below ell i.val i.isLt,
      insertAddress_below ell j.val j.isLt] using hh
  have hToNewB (i : Fin ell) :
      B.E i.val ell = decide (i.val < A.freeLevel n) := by
    rw [hEB]
    have hh := insertE_new_column_eq A ell (A.freeLevel n)
      hellA ((A.freeLevel_le n).trans (Nat.le_of_lt hn)) i.val
    simpa [insertAddress_below ell i.val i.isLt] using hh
  have hToNewH (i : Fin ell) :
      H.E i.val ell = decide (i.val < C.freeLevel n) := by
    rw [hEH]
    have hh := insertE_new_column_eq C ell (C.freeLevel n)
      hellC ((C.freeLevel_le n).trans (Nat.le_of_lt hn)) i.val
    simpa [insertAddress_below ell i.val i.isLt] using hh
  have hFromNewB (i : Fin ell) : B.E ell i.val = false := by
    cases hh : B.E ell i.val with
    | false => rfl
    | true =>
      have hs := B.spaced ell i.val hh
      omega
  have hFromNewH (i : Fin ell) : H.E ell i.val = false := by
    cases hh : H.E ell i.val with
    | false => rfl
    | true =>
      have hs := H.spaced ell i.val hh
      omega
  have hLoopEB : B.E ell ell = false := by
    cases hh : B.E ell ell with
    | false => rfl
    | true => exact False.elim (Nat.lt_irrefl _ (B.spaced ell ell hh))
  have hLoopEH : H.E ell ell = false := by
    cases hh : H.E ell ell with
    | false => rfl
    | true => exact False.elim (Nat.lt_irrefl _ (H.spaced ell ell hh))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j r
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        change B.L.binary ell ell r = H.L.binary ell ell r
        calc
          _ = DA.loop r := hLoopB r
          _ = DC.loop r := hData.1 r
          _ = _ := (hLoopH r).symm
      | cast j =>
        change B.L.binary ell j.val r = H.L.binary ell j.val r
        calc
          _ = DA.outgoing j.val r := hOutB j r
          _ = DC.outgoing j.val r := hData.2.2.2.2 j.val j.isLt r
          _ = _ := (hOutH j r).symm
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        change B.L.binary i.val ell r = H.L.binary i.val ell r
        calc
          _ = DA.incoming i.val r := hInB i r
          _ = DC.incoming i.val r := hData.2.2.2.1 i.val i.isLt r
          _ = _ := (hInH i r).symm
      | cast j =>
        change B.L.binary i.val j.val r = H.L.binary i.val j.val r
        calc
          _ = A.L.binary i.val j.val r := hOldBinB i j r
          _ = C.L.binary i.val j.val r := hComp.1 i j r
          _ = _ := (hOldBinH i j r).symm
  · intro i r
    induction i using Fin.lastCases with
    | last =>
      change B.L.unary ell r = H.L.unary ell r
      calc
        _ = DA.unary r := hNewUnB r
        _ = DC.unary r := hData.2.1 r
        _ = _ := (hNewUnH r).symm
    | cast i =>
      change B.L.unary i.val r = H.L.unary i.val r
      calc
        _ = A.L.unary i.val r := hOldUnB i r
        _ = C.L.unary i.val r := hComp.2.1 i r
        _ = _ := (hOldUnH i r).symm
  · intro i r
    induction i using Fin.lastCases with
    | last =>
      change B.L.diagonal ell r = H.L.diagonal ell r
      calc
        _ = DA.diagonal r := hNewDiagB r
        _ = DC.diagonal r := hData.2.2.1 r
        _ = _ := (hNewDiagH r).symm
    | cast i =>
      change B.L.diagonal i.val r = H.L.diagonal i.val r
      calc
        _ = A.L.diagonal i.val r := hOldDiagB i r
        _ = C.L.diagonal i.val r := hComp.2.2.1 i r
        _ = _ := (hOldDiagH i r).symm
  · intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        change B.E ell ell = H.E ell ell
        exact hLoopEB.trans hLoopEH.symm
      | cast j =>
        change B.E ell j.val = H.E ell j.val
        exact (hFromNewB j).trans (hFromNewH j).symm
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        change B.E i.val ell = H.E i.val ell
        calc
          _ = decide (i.val < A.freeLevel n) := hToNewB i
          _ = decide (i.val < C.freeLevel n) := by rw [hCut]
          _ = _ := (hToNewH i).symm
      | cast j =>
        change B.E i.val j.val = H.E i.val j.val
        calc
          _ = A.E i.val j.val := hOldEB i j
          _ = C.E i.val j.val := hComp.2.2.2 i j
          _ = _ := (hOldEH i j).symm

end SuccessorTree.V10

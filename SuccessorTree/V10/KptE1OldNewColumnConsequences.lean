import SuccessorTree.V10.KptE1TargetParameterCut
import SuccessorTree.V10.KptE1CompleteERecord
import Mathlib.Tactic

/-!
# Derive all padded E1 ordinary-column conditions from genuine Kpt data

The padded finite E1 source constructor previously exposed
E1PaddedOrdinaryLinked and full ordinary E-column equality as separate
finite hypotheses. These are not extra axioms: old columns inherit the
actual source predecessor's E and linked-L conditions, while the NEW
column obeys ValidNewOrdinaryColumn of the real target successor after
shape-level reindexing.

This file proves the resulting two finite reduction lemmas using the
genuine complete L+ type Q. Both directed binary orientations and
the absence of a link beyond the new free cut are respected.
The old prefix's linkedness and E-column profile remain explicit here:
the next E1 step must derive them from the actual admissible source
predecessor and the verified retained-record theorem.
-/

namespace SuccessorTree.V10

/-- The only additional L-linkedness needed by the padded source,
beyond inherited old-column linkedness, is discharged by the
*actual* valid one-step new column. In particular a nonzero
old-new binary L atom beyond the new free cut is impossible in
either direction. -/
theorem e1PaddedOrdinaryLinked_of_old_and_validNew
    {db du dd : Nat} {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (oldCut : Nat → Nat) (f : Nat)
    (hOldLinked :
      ∀ u v : Nat, u < v → v < n →
        (∃ r : Fin db,
          Q.ageModel.binary u v r = true ∨
          Q.ageModel.binary v u r = true) →
        u < oldCut v)
    (hNew : ValidNewOrdinaryColumn Q f) :
    E1PaddedOrdinaryLinked Q oldCut f := by
  intro u v huv hv hLink
  by_cases hvOld : v < n
  · have h := hOldLinked u v huv hvOld hLink
    simpa [paddedE1FreeCutProfile, hvOld] using h
  · have hvEq : v = n := by omega
    subst v
    have hu : u < n := huv
    have hUF : u < f := by
      by_contra huNot
      have hfU : f ≤ u := Nat.le_of_not_gt huNot
      obtain ⟨r, hRel⟩ := hLink
      have hNo := hNew.noNewBinaryBeyondCut
        (⟨u,hu⟩ : Fin n) hfU r
      have hNoAge :
          Q.ageModel.binary u n r = false ∧
          Q.ageModel.binary n u r = false := by
        simpa [PartialTypeWithE.ageModel, typeAgeIndex,
          Nat.le_of_lt hu] using hNo
      rcases hRel with hRel | hRel
      · simp [hNoAge.1] at hRel
      · simp [hNoAge.2] at hRel
    simpa [paddedE1FreeCutProfile] using hUF

/-- The complete ordinary E matrix is determined by the actual old
columns, their strict spacing, the source new free cut and the
canonical no-reverse-E new column. No extra E1 assumption is needed
for the OLD-NEW or NEW-OLD parts of this equality. -/
theorem e1PaddedColumns_of_oldE_and_validNew
    {db du dd : Nat} {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (oldCut : Nat → Nat) (f : Nat)
    (hOld : ∀ v, v < n → oldCut v = 0 ∨ oldCut v < v)
    (hNewGate : f = 0 ∨ f < n)
    (hOldE : ∀ i j : Fin n,
      Q.eRelation (some i.castSucc) (some j.castSucc) =
        decide (i.val < oldCut j.val))
    (hValid : ValidNewOrdinaryColumn Q f)
    (hNewLoop :
      Q.eRelation (some (Fin.last n)) (some (Fin.last n)) = false) :
    ∀ i j : Fin (n + 1),
      Q.eRelation (some i) (some j) =
        decide (i.val < paddedE1FreeCutProfile n oldCut f j.val) := by
  intro i j
  induction j using Fin.lastCases with
  | last =>
      induction i using Fin.lastCases with
      | last =>
          have hnF : ¬ n < f := by
            rcases hNewGate with hz | hlt <;> omega
          simpa [paddedE1FreeCutProfile, hnF] using hNewLoop
      | cast i =>
          simpa [paddedE1FreeCutProfile] using hValid.oldToNewE i
  | cast j =>
      induction i using Fin.lastCases with
      | last =>
          have hCut : oldCut j.val = 0 ∨ oldCut j.val < j.val :=
            hOld j.val j.isLt
          have hNot : ¬ n < oldCut j.val := by
            rcases hCut with hz | hlt <;> omega
          simpa [paddedE1FreeCutProfile, j.isLt, hNot]
            using hValid.newToOldE j
      | cast i =>
          simpa [paddedE1FreeCutProfile, j.isLt] using hOldE i j

end SuccessorTree.V10

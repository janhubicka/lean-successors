import SuccessorTree.V10.EmptyKptPartialType
import SuccessorTree.V10.AdmissibleKptPrefix
import Mathlib.Tactic

/-!
# Realizing empty-language cut histories as admissible Kpt types

For every finite one-parameter history, place its ordinary E-column record
on positions 0,...,n and add a neutral spacer at n+1 followed by a type
vertex at n+2. The type vertex has free cut n+1. This exhibits the
encoded record as an actual admissible Kpt node, not just a raw record.

Only the *forward* realization is proved here. Surjectivity on all
admissible empty-language Kpt nodes, correspondence of canonical
successors and shape-map transport remain independent obligations.
-/

namespace SuccessorTree.V10.EmptyKpt

/-- Extend the finite sequence of ordinary E cuts by a neutral spacer
and a final type vertex whose full free socle is the original record. -/
def ambientCut {n : Nat} (h : CutHistory n) (v : Nat) : Nat :=
  if hv : v < n + 1 then ordinaryCutAt h ⟨v, hv⟩
  else if v = n + 2 then n + 1 else 0

theorem ambientCut_old {n : Nat} (h : CutHistory n)
    (v : Nat) (hv : v < n + 1) :
    ambientCut h v = ordinaryCutAt h ⟨v, hv⟩ := by
  simp [ambientCut, hv]

@[simp] theorem ambientCut_cap {n : Nat} (h : CutHistory n) :
    ambientCut h (n + 2) = n + 1 := by
  have hv : ¬ n + 2 < n + 1 := by omega
  simp [ambientCut, hv]

@[simp] theorem ambientCut_spacer {n : Nat} (h : CutHistory n) :
    ambientCut h (n + 1) = 0 := by
  have hv : ¬ n + 1 < n + 1 := by omega
  have hw : n + 1 ≠ n + 2 := by omega
  simp [ambientCut, hv, hw]

theorem ordinaryCutAt_le {n : Nat} (h : CutHistory n)
    (j : Fin (n + 1)) :
    ordinaryCutAt h j ≤ j.val := by
  by_cases hj : 0 < j.val
  · exact Nat.le_of_lt (ordinaryCutAt_lt_of_pos h j hj)
  · have hz : j.val = 0 := by omega
    have heq : j = ⟨0, by omega⟩ := Fin.ext hz
    simpa [heq] using (ordinaryCutAt_zero h).le

theorem ambientCut_le {n : Nat} (h : CutHistory n) (v : Nat) :
    ambientCut h v ≤ v := by
  by_cases hv : v < n + 1
  · rw [ambientCut_old h v hv]
    exact ordinaryCutAt_le h ⟨v, hv⟩
  · by_cases hcap : v = n + 2
    · simp [ambientCut, hv, hcap]
    · simp [ambientCut, hv, hcap]

theorem ambientCut_lt_of_pos {n : Nat}
    (h : CutHistory n) (v : Nat)
    (hpos : 0 < ambientCut h v) :
    ambientCut h v < v := by
  by_cases hv : v < n + 1
  · rw [ambientCut_old h v hv] at hpos ⊢
    have hle : ordinaryCutAt h ⟨v, hv⟩ ≤ v := by
      simpa using (ordinaryCutAt_le h ⟨v, hv⟩)
    have hvpos : 0 < v := by omega
    exact ordinaryCutAt_lt_of_pos h ⟨v,hv⟩ hvpos
  · by_cases hcap : v = n + 2
    · simp only [hcap, ambientCut_cap]
      omega
    · simp [ambientCut, hv, hcap] at hpos

theorem ambientCut_supported {n : Nat}
    (h : CutHistory n) (v : Nat)
    (hpos : 0 < ambientCut h v) :
    v < n + 3 := by
  by_cases hv : v < n + 1
  · omega
  · by_cases hcap : v = n + 2
    · omega
    · simp [ambientCut, hv, hcap] at hpos

/-- The ambient E relation is simply its downward-closed column cuts. -/
def ambientE {n : Nat} (h : CutHistory n) (u v : Nat) : Bool :=
  decide (u < ambientCut h v)

/-- All L symbols are absent; the carrier consists of the first n+3
numbered positions, including a neutral spacer and a final type vertex. -/
def ambientL {n : Nat} (_h : CutHistory n) :
    AgeTestModel 0 0 0 where
  carrier := {v | v < n + 3}
  binary := fun _ _ t => Fin.elim0 t
  unary := fun _ t => Fin.elim0 t
  diagonal := fun _ t => Fin.elim0 t

/-- The genuine finite partial structure witnessing admissibility. -/
def ambientPartial {n : Nat} (h : CutHistory n) :
    EnumeratedPartialStructure 0 0 0 where
  size := n + 3
  L := ambientL h
  carrier_iff := by
    intro v
    rfl
  E := ambientE h
  E_inside := by
    intro u v hE
    have hu : u < ambientCut h v := by
      simpa [ambientE, decide_eq_true_eq] using hE
    have hvpos : 0 < ambientCut h v := by omega
    have hv : v < n + 3 := ambientCut_supported h v hvpos
    have hcut := ambientCut_le h v
    omega
  spaced := by
    intro u v hE
    have hu : u < ambientCut h v := by
      simpa [ambientE, decide_eq_true_eq] using hE
    have hvpos : 0 < ambientCut h v := by omega
    have hcut := ambientCut_lt_of_pos h v hvpos
    omega
  downward := by
    intro u v hE w hw
    have hu : u < ambientCut h v := by
      simpa [ambientE, decide_eq_true_eq] using hE
    change decide (w < ambientCut h v) = true
    simp only [decide_eq_true_eq]
    omega
  linked_E := by
    intro u v _ _ _ hlink
    obtain ⟨t, _⟩ := hlink
    exact Fin.elim0 t

/-- The final vertex's first missing E coordinate is exactly n+1. -/
theorem ambientPartial_cap_freeLevel {n : Nat}
    (h : CutHistory n) :
    (ambientPartial h).freeLevel (n + 2) = n + 1 := by
  have hcut : IsFreeCut (ambientPartial h).E (n + 2) (n + 1) := by
    constructor
    · intro u hu
      change decide (u < ambientCut h (n + 2)) = true
      simp [hu]
    · change decide (n + 1 < ambientCut h (n + 2)) = false
      simp
  exact freeCut_unique (ambientPartial h).E (n + 2)
    ((ambientPartial h).freeLevel (n + 2)) (n + 1)
    (canonicalFreeLevel_isFreeCut _ (ambientPartial h).spaced
      (ambientPartial h).downward (n + 2)) hcut

/-- The type of the final vertex, over all first n+1 ordinary
coordinates, is exactly the record coded by the given history. -/
theorem ambientPartial_cap_type {n : Nat}
    (h : CutHistory n) :
    (ambientPartial h).partialTypeAt (n + 1) (n + 2) =
      emptyPartialType h := by
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b t
      exact Fin.elim0 t
    · intro a t
      exact Fin.elim0 t
    · intro a t
      exact Fin.elim0 t
  · intro a b
    cases a with
    | none =>
      cases b with
      | none =>
        change decide (n + 2 < ambientCut h (n + 2)) = false
        simp
      | some j =>
        change decide (n + 2 < ambientCut h j.val) = false
        have hj : j.val < n + 1 := j.isLt
        have hc := ambientCut_le h j.val
        simp [show ¬ n + 2 < ambientCut h j.val by omega]
    | some i =>
      cases b with
      | none =>
        change decide (i.val < ambientCut h (n + 2)) = true
        simp [i.isLt]
      | some j =>
        change decide (i.val < ambientCut h j.val) =
          decide (i.val < ordinaryCutAt h j)
        rw [ambientCut_old h j.val j.isLt]

/-- Every cut history is realized by a genuinely admissible empty-language
partial type. The empty forbidden family needs no forbidden-age check. -/
theorem rawEmptyNode_admissible {n : Nat} (h : CutHistory n) :
    IsAdmissibleRawType ([] : List (NormalizedForbidden 0 0 0))
      (rawEmptyNode h) := by
  refine ⟨ambientPartial h, n + 2, by change n + 2 < n + 3; omega, ?_, ?_⟩
  · intro bad hbad
    simp at hbad
  · change rawEmptyNode h = (ambientPartial h).rawTypeAtFree (n + 2)
    unfold rawEmptyNode EnumeratedPartialStructure.rawTypeAtFree
    rw [ambientPartial_cap_freeLevel]
    exact congrArg (Sigma.mk (n + 1)) (ambientPartial_cap_type h).symm

end SuccessorTree.V10.EmptyKpt

import SuccessorTree.V10.KptE1PaddedLTypeEquality
import SuccessorTree.V10.KptE1PaddedFreeCutProfile
import Mathlib.Tactic

/-!
# Assemble the genuine Kpt E1 source partial structure

Combine the proven finite L age source, its exact complete L-reduct,
and the prescribed spaced E profile into one ACTUAL
EnumeratedPartialStructure. The only extra finite obligation here is
linked_E for old/new ordinary columns: every linked pair with second
coordinate at most n must lie below that column's specified E cut.

The neutral spacer n+1 cannot have any incident positive binary L
atom; for the last type witness n+2, all real previous ordinary
vertices lie strictly below its E cut n+1. Thus these two portions
of linked_E require no extra assumption.

This theorem still does not prove the actual abstract E1 rule:
the ordinary linked premise and literal correspondence of all E
atoms and the canonical successor parameter must be extracted from
the genuine target successor and its ShapeMap.
-/

namespace SuccessorTree.V10

/-- Precisely the remaining ordinary-column linked-E obligation
for the finite pulled-back L type. The linked pattern is read from
the genuine Q.ageModel rather than an invented E expansion. -/
def E1PaddedOrdinaryLinked
    {db du dd : Nat} {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (oldCut : Nat → Nat) (f : Nat) : Prop :=
  ∀ u v, u < v → v ≤ n →
    (∃ r : Fin db,
      Q.ageModel.binary u v r = true ∨
      Q.ageModel.binary v u r = true) →
    u < paddedE1FreeCutProfile n oldCut f v

/-- Old ordinary-ordinary L atoms in the neutral-padded source
coincide with those of the actual complete Q type-age model. -/
theorem e1PaddedSourceAge_binary_ordinary
    {db du dd : Nat} {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (u v : Nat) (t : Fin db)
    (hu : u ≤ n) (hv : v ≤ n) :
    (e1PaddedSourceAge Q).binary u v t =
      Q.ageModel.binary u v t := by
  have hu' : u < n + 1 := by omega
  have hv' : v < n + 1 := by omega
  let i : Fin (n + 1) := ⟨u,hu'⟩
  let j : Fin (n + 1) := ⟨v,hv'⟩
  have h :=
    e1PaddedSourceAge_binary_type Q (some i) (some j) t
  simpa [i,j,PartialTypeWithE.ageModel,typeAgeIndex,
    prefixVertexIndex,hu',hv'] using h

/-- The combined model's linked E condition follows from
linked old/new Q-columns, absence of L atoms at the neutral spacer,
and the final type witness's exact n+1 free cut. -/
theorem e1PaddedSourceAge_linked_profile
    {db du dd : Nat} {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (oldCut : Nat → Nat) (f : Nat)
    (hOrd : E1PaddedOrdinaryLinked Q oldCut f) :
    ∀ u v, u < v → u < n + 3 → v < n + 3 →
      (∃ r : Fin db,
        (e1PaddedSourceAge Q).binary u v r = true ∨
        (e1PaddedSourceAge Q).binary v u r = true) →
      u < paddedE1FreeCutProfile n oldCut f v := by
  intro u v huv hu hv hLinked
  by_cases hvOrd : v ≤ n
  · have huOrd : u ≤ n := by omega
    have hQ : ∃ r : Fin db,
        Q.ageModel.binary u v r = true ∨
        Q.ageModel.binary v u r = true := by
      obtain ⟨r,hr⟩ := hLinked
      refine ⟨r, ?_⟩
      rcases hr with hr | hr
      · left
        rw [e1PaddedSourceAge_binary_ordinary Q u v r huOrd hvOrd] at hr
        exact hr
      · right
        rw [e1PaddedSourceAge_binary_ordinary Q v u r hvOrd huOrd] at hr
        exact hr
    exact hOrd u v huv hvOrd hQ
  · by_cases hvSpacer : v = n + 1
    · subst v
      obtain ⟨r, hr⟩ := hLinked
      rcases hr with hr | hr
      · rw [e1PaddedSourceAge_spacer_right Q u r] at hr
        cases hr
      · rw [e1PaddedSourceAge_spacer_left Q u r] at hr
        cases hr
    · have hvType : v = n + 2 := by omega
      subst v
      have huNotSpacer : u ≠ n + 1 := by
        intro hSpacer
        subst u
        obtain ⟨r,hr⟩ := hLinked
        rcases hr with hr | hr
        · rw [e1PaddedSourceAge_spacer_left Q (n + 2) r] at hr
          cases hr
        · rw [e1PaddedSourceAge_spacer_right Q (n + 2) r] at hr
          cases hr
      have huBound : u < n + 1 := by omega
      rw [paddedE1FreeCutProfile_type n oldCut f]
      exact huBound

/-- An actual partial structure from the exact padded source L model,
with no arbitrary E on forbidden witnesses and the literal cut profile. -/
noncomputable def e1PaddedSourceStructure
    {db du dd : Nat} {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (oldCut : Nat → Nat) (f : Nat)
    (hOld : ∀ v, v < n → oldCut v = 0 ∨ oldCut v < v)
    (hNew : f = 0 ∨ f < n)
    (hOrd : E1PaddedOrdinaryLinked Q oldCut f) :
    EnumeratedPartialStructure db du dd :=
  paddedE1PartialStructure n (e1PaddedSourceAge Q)
    (by intro v; exact e1PaddedSourceAge_carrier Q v)
    oldCut f hOld hNew
    (e1PaddedSourceAge_linked_profile Q oldCut f hOrd)

/-- The actual E cut of the final type witness is n+1. -/
theorem e1PaddedSourceStructure_freeLevel
    {db du dd : Nat} {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (oldCut : Nat → Nat) (f : Nat)
    (hOld : ∀ v, v < n → oldCut v = 0 ∨ oldCut v < v)
    (hNew : f = 0 ∨ f < n)
    (hOrd : E1PaddedOrdinaryLinked Q oldCut f) :
    (e1PaddedSourceStructure Q oldCut f hOld hNew hOrd).freeLevel
      (n + 2) = n + 1 := by
  exact paddedE1PartialStructure_type_freeLevel
    n (e1PaddedSourceAge Q)
    (by intro v; exact e1PaddedSourceAge_carrier Q v)
    oldCut f hOld hNew
    (e1PaddedSourceAge_linked_profile Q oldCut f hOrd)

/-- Complete L-reduct extracted from the actual structure is
literally Q.lReduct, with all directions and absences preserved. -/
theorem e1PaddedSourceStructure_L_type
    {db du dd : Nat} {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (oldCut : Nat → Nat) (f : Nat)
    (hOld : ∀ v, v < n → oldCut v = 0 ∨ oldCut v < v)
    (hNew : f = 0 ∨ f < n)
    (hOrd : E1PaddedOrdinaryLinked Q oldCut f) :
    ((e1PaddedSourceStructure Q oldCut f hOld hNew hOrd).partialTypeAt
      (n + 1) (n + 2)).lReduct = Q.lReduct := by
  change RelationalPrefixType.ofAgeModel
    (e1PaddedSourceAge Q) (n + 1) (n + 2) = Q.lReduct
  exact e1PaddedSourceAge_complete_L_type Q

/-- The witness has forbidden-free finite L-age whenever the
original complete type age does; no E-age assumption is made. -/
theorem e1PaddedSourceStructure_avoids
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (oldCut : Nat → Nat) (f : Nat)
    (hOld : ∀ v, v < n → oldCut v = 0 ∨ oldCut v < v)
    (hNew : f = 0 ∨ f < n)
    (hOrd : E1PaddedOrdinaryLinked Q oldCut f)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids Q.ageModel) :
    ∀ bad, bad ∈ family →
      bad.Avoids (e1PaddedSourceStructure
        Q oldCut f hOld hNew hOrd).L := by
  exact e1PaddedSourceAge_avoids family Q hAvoid

/-- Pack the proved source witness, with honest L-age and actual E
spacing/downward/linked axioms, and its exact level and L-type.
Only the old/new E-record equality to Q and canonical parameter
reconstruction remain before full one-level pullback. -/
theorem exists_e1PaddedSourceStructure
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (oldCut : Nat → Nat) (f : Nat)
    (hOld : ∀ v, v < n → oldCut v = 0 ∨ oldCut v < v)
    (hNew : f = 0 ∨ f < n)
    (hOrd : E1PaddedOrdinaryLinked Q oldCut f)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids Q.ageModel) :
    ∃ A : EnumeratedPartialStructure db du dd,
      A.size = n + 3 ∧
      (∀ bad, bad ∈ family → bad.Avoids A.L) ∧
      A.freeLevel (n + 2) = n + 1 ∧
      (A.partialTypeAt (n + 1) (n + 2)).lReduct = Q.lReduct := by
  let A := e1PaddedSourceStructure Q oldCut f hOld hNew hOrd
  refine ⟨A, rfl, ?_, ?_, ?_⟩
  · exact e1PaddedSourceStructure_avoids family
      Q oldCut f hOld hNew hOrd hAvoid
  · exact e1PaddedSourceStructure_freeLevel
      Q oldCut f hOld hNew hOrd
  · exact e1PaddedSourceStructure_L_type
      Q oldCut f hOld hNew hOrd

end SuccessorTree.V10

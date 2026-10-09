import SuccessorTree.V10.CanonicalCoverS3
import Mathlib.Tactic

/-!
# Canonical successor graph is functional and injective in all inputs

Given the exact predecessor, canonical empty-or-singleton parameter,
and terminal Sigma letter, there is AT MOST ONE admissible successor.
Conversely, given an output, its predecessor, parameter and letter
are unique, hence the graph meets the S2 input-injectivity requirement.

This proof is not an abstract STree axiom. The forward direction
uses full predecessor/column reconstruction from S2's verified
finite record lemmas, with the same free cut read from the
parameter list. Reverse injectivity uses uniqueness of the
free E cut from the actual E-column and the induced prefix
forest's unique ancestors.

The remaining STree step is to totalize the partial graph by
classical choice, use S3 existence for every cover, and check
the exact Sigma alphabet rather than the larger raw letter type.
-/

namespace SuccessorTree.V10

private theorem rawValues_map_injective
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    Function.Injective
      (List.map (fun x : AdmissibleKptNode family => x.1)) := by
  intro xs ys h
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hxy : x = y := Subtype.ext h.1
      subst y
      have ht : xs = ys := ih h.2
      subst ys
      rfl

private theorem optionList_injective {α : Type*} :
    Function.Injective (Option.toList : Option α → List α) := by
  intro a b h
  cases a <;> cases b <;> simp_all [Option.toList]

/-- The levels f and g of canonical (possibly empty) parameters
coincide whenever their raw list representations coincide.
The empty list encodes f=0; otherwise the unique singleton
encodes the positive level as the first Sigma coordinate. -/
theorem canonical_parameter_cut_unique
    {ell db du dd : Nat}
    (Q R : PartialTypeWithE (ell + 1) db du dd)
    (f g : Nat) (hf : f ≤ ell) (hg : g ≤ ell)
    (p : List (RawPartialTypeNode db du dd))
    (hP : p = (Q.canonicalParameterRecord f hf).toList)
    (hP' : p = (R.canonicalParameterRecord g hg).toList) :
    f = g := by
  have hList : (Q.canonicalParameterRecord f hf).toList =
      (R.canonicalParameterRecord g hg).toList :=
    hP.symm.trans hP'
  by_cases hZeroF : f = 0
  · by_cases hZeroG : g = 0
    · omega
    · have : False := by
        simpa [PartialTypeWithE.canonicalParameterRecord,
          hZeroF, hZeroG] using hList
      exact this.elim
  · by_cases hZeroG : g = 0
    · have : False := by
        simpa [PartialTypeWithE.canonicalParameterRecord,
          hZeroF, hZeroG] using hList
      exact this.elim
    · have hEq :
        (⟨f, Q.lastOrdinaryParameter f hf⟩ :
          RawPartialTypeNode db du dd) =
        (⟨g, R.lastOrdinaryParameter g hg⟩ :
          RawPartialTypeNode db du dd) := by
        have hLists :
            [(⟨f, Q.lastOrdinaryParameter f hf⟩ :
                RawPartialTypeNode db du dd)] =
              [(⟨g, R.lastOrdinaryParameter g hg⟩ :
                RawPartialTypeNode db du dd)] := by
          simpa [PartialTypeWithE.canonicalParameterRecord,
            hZeroF, hZeroG] using hList
        simpa only [List.cons.injEq, and_true] using hLists
      exact congrArg Sigma.fst hEq

/-- The complete canonical successor output is unique for
fixed (base, parameter list, letter); this is functionality of
the forward graph before it is installed as an Option-valued map. -/
theorem canonicalKptStep_target_unique
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {a b b' : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : RawKptLetter db du dd}
    (hB : IsCanonicalKptStep family a p c b)
    (hB' : IsCanonicalKptStep family a p c b') :
    b = b' := by
  obtain ⟨ell, f, hf, Q, hBase, hTarget, hLetter, hValid,
    hParam, hGate⟩ := hB
  obtain ⟨ell', g, hg, R, hBase', hTarget', hLetter',
    hValid', hParam', hGate'⟩ := hB'
  have hLevel : ell = ell' := by
    have h1 := congrArg Sigma.fst hBase
    have h2 := congrArg Sigma.fst hBase'
    change a.1.1 = ell at h1
    change a.1.1 = ell' at h2
    omega
  subst ell'
  have hOld : Q.restrict (Nat.le_succ ell) =
      R.restrict (Nat.le_succ ell) := by
    have hRaw : (⟨ell, Q.restrict (Nat.le_succ ell)⟩ :
        RawPartialTypeNode db du dd) =
        (⟨ell, R.restrict (Nat.le_succ ell)⟩ :
          RawPartialTypeNode db du dd) :=
      hBase.symm.trans hBase'
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
      using hRaw
  have hList :
      (Q.canonicalParameterRecord f hf).toList =
        (R.canonicalParameterRecord g hg).toList :=
    hParam.symm.trans hParam'
  have hCutEq : f = g :=
    canonical_parameter_cut_unique Q R f g hf hg
      (p.map (fun x => x.1)) hParam hParam'
  subst g
  have hParamEq : Q.canonicalParameterRecord f hf =
      R.canonicalParameterRecord f hf :=
    optionList_injective (by
      simpa only using hList)
  have hQeq : Q = R :=
    complete_successor_unique_of_option_parameter Q R f hf
      hOld hValid hValid' hParamEq
      (hLetter.symm.trans hLetter')
  apply Subtype.ext
  calc
    b.1 = (⟨ell + 1, Q⟩ : RawPartialTypeNode db du dd) := hTarget
    _ = (⟨ell + 1, R⟩ : RawPartialTypeNode db du dd) := by rw [hQeq]
    _ = b'.1 := hTarget'.symm

/-- The inverse canonical decomposition is unique: identical
successor target implies equal immediate predecessors, parameter
lists and terminal letters. This is the input-injectivity
axiom S2 at the level of the proved successor GRAPH. -/
theorem canonicalKptStep_inputs_unique
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {a a' b : AdmissibleKptNode family}
    {p p' : List (AdmissibleKptNode family)}
    {c c' : RawKptLetter db du dd}
    (h : IsCanonicalKptStep family a p c b)
    (h' : IsCanonicalKptStep family a' p' c' b) :
    a = a' ∧ p = p' ∧ c = c' := by
  obtain ⟨ell, f, hf, Q, hBase, hTarget, hLetter,
    hValid, hParam, _⟩ := h
  obtain ⟨ell', g, hg, R, hBase', hTarget', hLetter',
    hValid', hParam', _⟩ := h'
  have hRaw : (⟨ell + 1, Q⟩ :
      RawPartialTypeNode db du dd) =
        (⟨ell' + 1, R⟩ : RawPartialTypeNode db du dd) :=
    hTarget.symm.trans hTarget'
  have hLevel : ell = ell' := by
    have h := congrArg Sigma.fst hRaw
    change ell + 1 = ell' + 1 at h
    omega
  subst ell'
  have hQr : Q = R := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hRaw
  subst R
  have hCut : f = g :=
    validNewColumn_freeCut_unique Q f g hf hg
      hValid hValid'
  subst g
  have hA : a = a' := Subtype.ext (hBase.trans hBase'.symm)
  have hPraw : p.map (fun x => x.1) =
      p'.map (fun x => x.1) := by
    calc
      p.map (fun x => x.1) =
        (Q.canonicalParameterRecord f hf).toList := hParam
      _ = (Q.canonicalParameterRecord f hg).toList := rfl
      _ = p'.map (fun x => x.1) := hParam'.symm
  have hP : p = p' :=
    (rawValues_map_injective family) hPraw
  exact ⟨hA, hP, hLetter.trans hLetter'.symm⟩

end SuccessorTree.V10

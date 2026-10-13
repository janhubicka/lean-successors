import SuccessorTree.V10.CanonicalPrefixStep
import SuccessorTree.V10.AdmissibleSigmaSTree
import Mathlib.Tactic

/-!
# Genuine canonical parameters under one containing type

Do not postulate an arbitrary parameter realization in the proof of M2.
At every ordinary coordinate j below a larger genuine E free cut,
the canonical source step has the actual admissible type extracted from
that coordinate, and lies below the one ambient Kpt node. The precise
level inequality uses E spacing, not an M2 assumption.
-/

namespace SuccessorTree.V10

/-- An actual upper ordinary vertex with positive E free cut appears as
the genuine canonical parameter of one STree successor below the
containing type. The parameter may have a different distinguished
type from the containing type; no mistaken tree-prefix claim is made. -/
theorem ambient_prefix_actual_parameter_below
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (v j : Nat) (hv : v < A.size)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hCut : j + 1 ≤ A.freeLevel v)
    (hPos : 0 < A.freeLevel j) :
    ∃ (a b : AdmissibleKptNode family)
      (p : List (AdmissibleKptNode family))
      (c : AdmissibleKptSigma family)
      (q : AdmissibleKptNode family),
      (admissibleKptSTree family).succ a p c = some b ∧
      b ≤ (⟨A.rawTypeAtFree v, ⟨A,v,hv,hAvoid,rfl⟩⟩ :
        AdmissibleKptNode family) ∧
      q ∈ p ∧ q.1 = A.rawTypeAtFree j ∧
      LevelTree.lev a = j := by
  obtain ⟨a,b,p,c,hStep,_hCover,hB,hParam⟩ :=
    exists_canonical_step_from_ambient_prefix
      family A v j hv hAvoid hCut
  obtain ⟨q,hMem,hQ⟩ := hParam hPos
  let c' : AdmissibleKptSigma family :=
    ⟨c,canonicalKptStep_letter_admissible family hStep⟩
  have hSucc : (admissibleKptSTree family).succ a p c' = some b :=
    canonicalKptSucc_eq_some_of_step family hStep
  have hPrefix :
      (⟨j+1,A.partialTypeAt (j+1) v⟩ :
        RawPartialTypeNode db du dd) ≤ A.rawTypeAtFree v := by
    refine ⟨hCut,?_⟩
    exact (A.partialTypeAt_restrict (j+1) (A.freeLevel v) v hCut).symm
  have hBelow : b ≤ (⟨A.rawTypeAtFree v,
      ⟨A,v,hv,hAvoid,rfl⟩⟩ : AdmissibleKptNode family) := by
    change b.1 ≤ A.rawTypeAtFree v
    rw [hB]
    exact hPrefix
  refine ⟨a,b,p,c',q,hSucc,hBelow,hMem,hQ,?_⟩
  obtain ⟨ell,f,hf,Q,hA,hTarget,hLetter,hValid,hParamEq,hGate⟩ := hStep
  have hLevel := congrArg Sigma.fst hA
  exact hLevel

end SuccessorTree.V10

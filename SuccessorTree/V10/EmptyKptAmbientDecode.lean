import SuccessorTree.V10.EmptyKptDecode
import Mathlib.Tactic

/-!
# Decoding every genuine empty-language admissible Kpt type

The complete ordinary E-columns of a valid source partial structure
determine a unique ancestral history. This is the converse to the
finite admissibility witness in EmptyKptAdmissible. Both positive and
negative E atoms, including the special type-vertex column, are checked.

The correspondence of the full canonical successor graphs and the
induced monoids is not assumed in this module.
-/

namespace SuccessorTree.V10.EmptyKpt

/-- Every positive numbered E column has its first missing entry
strictly before that column, from the literal spacing axiom. -/
theorem freeLevel_lt_positive
    (A : EnumeratedPartialStructure 0 0 0)
    (j : Nat) (hj : 0 < j) :
    A.freeLevel j < j := by
  have hle := A.freeLevel_le j
  by_contra hn
  have hlast : j - 1 < A.freeLevel j := by omega
  have he : A.E (j - 1) j = true :=
    (A.E_iff_freeLevel (j - 1) j).2 hlast
  have hspace := A.spaced (j - 1) j he
  omega

/-- Recover the unique free-ancestral successor parameter from an
actual ordinary E-column. -/
def ambientStepParam
    (A : EnumeratedPartialStructure 0 0 0) (n : Nat) :
    SuccessorTree.FreeAncestral.ParamTuple 1 n :=
  parameterOfCut ⟨A.freeLevel (n + 1), by
    have h := freeLevel_lt_positive A (n + 1) (by omega)
    omega⟩

/-- Read every ordinary E-column as a finite ancestral history. -/
def historyOfAmbient
    (A : EnumeratedPartialStructure 0 0 0) :
    (n : Nat) → CutHistory n
  | 0 => CutHistory.root
  | n + 1 => CutHistory.step (historyOfAmbient A n) (ambientStepParam A n)

/-- The reconstructed ordinary free cuts are equal at every coordinate. -/
theorem decodedCut_correct
    (A : EnumeratedPartialStructure 0 0 0) :
    ∀ (n : Nat) (j : Fin (n + 1)),
      ordinaryCutAt (historyOfAmbient A n) j = A.freeLevel j.val := by
  intro n
  induction n with
  | zero =>
      intro j
      have hj : j.val = 0 := by have := j.isLt; omega
      have hzero : A.freeLevel 0 = 0 := by
        have := A.freeLevel_le 0
        omega
      have hj0 : j = (0 : Fin 1) := Fin.ext hj
      subst j
      simpa [historyOfAmbient, ordinaryCutAt, hzero]
  | succ n ih =>
      intro j
      by_cases hj : j.val = n + 1
      · simp [historyOfAmbient, ordinaryCutAt, hj, ambientStepParam,
              parameterCut_parameterOfCut]
      · have hlt : j.val < n + 1 := by
          have := j.isLt
          omega
        change (if hlast : j.val = n + 1 then parameterCut (ambientStepParam A n)
          else ordinaryCutAt (historyOfAmbient A n) ⟨j.val, by omega⟩) =
            A.freeLevel j.val
        simp [hj, ih ⟨j.val, hlt⟩]

/-- The decoded complete partial type matches the genuine one, including
its full incoming E-column and all absent reverse E-entries. -/
theorem decodedType_correct
    (A : EnumeratedPartialStructure 0 0 0)
    (n v : Nat) (hcut : n + 1 ≤ A.freeLevel v) :
    emptyPartialType (historyOfAmbient A n) =
      A.partialTypeAt (n + 1) v := by
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      exact Fin.elim0 r
    · intro a r
      exact Fin.elim0 r
    · intro a r
      exact Fin.elim0 r
  · intro a b
    cases a with
    | none =>
      cases b with
      | none =>
        simpa [emptyPartialType] using
          (A.partialTypeAt_no_typeE_loop (n + 1) v).symm
      | some j =>
        simpa [emptyPartialType] using
          (A.partialTypeAt_no_reverseE (n + 1) v hcut j).symm
    | some i =>
      cases b with
      | none =>
        simpa [emptyPartialType] using
          (A.partialTypeAt_fullESocle (n + 1) v hcut i).symm
      | some j =>
        change decide (i.val < ordinaryCutAt
          (historyOfAmbient A n) j) = A.E i.val j.val
        rw [decodedCut_correct A n j]
        by_cases h : i.val < A.freeLevel j.val
        · have ht := (A.E_iff_freeLevel i.val j.val).2 h
          simp [h, ht]
        · have hf : A.E i.val j.val = false := by
            cases he : A.E i.val j.val with
            | false => rfl
            | true =>
                exact False.elim (h ((A.E_iff_freeLevel i.val j.val).1 he))
          simp [h, hf]

/-- Surjectivity on every genuine admissible positive-level Kpt node. -/
theorem admissible_positive_has_history {n : Nat}
    (T : PartialTypeWithE (n + 1) 0 0 0)
    (hAd : IsAdmissibleRawType
      ([] : List (NormalizedForbidden 0 0 0))
      (⟨n + 1, T⟩ : RawPartialTypeNode 0 0 0)) :
    ∃ h : CutHistory n, T = emptyPartialType h := by
  rcases hAd with ⟨A, v, hv, _, hEq⟩
  have hCut : A.freeLevel v = n + 1 := by
    have hh := congrArg Sigma.fst hEq
    simpa [EnumeratedPartialStructure.rawTypeAtFree] using hh.symm
  have hPart : T = A.partialTypeAt (n + 1) v := by
    have hh : (⟨n + 1, T⟩ : RawPartialTypeNode 0 0 0) =
        (⟨n + 1, A.partialTypeAt (n + 1) v⟩ :
          RawPartialTypeNode 0 0 0) := by
      simpa [EnumeratedPartialStructure.rawTypeAtFree, hCut] using hEq
    cases hh
    rfl
  refine ⟨historyOfAmbient A n, ?_⟩
  exact hPart.trans (decodedType_correct A n v (by omega)).symm

/-- The extra fixed Kpt root, one level below the free-history root. -/
def emptyRootType : PartialTypeWithE 0 0 0 0 where
  lReduct :=
    { binary := fun _ _ t => Fin.elim0 t
      unary := fun _ t => Fin.elim0 t
      diagonal := fun _ t => Fin.elim0 t }
  eRelation := fun _ _ => false

/-- A zero-level empty-language Kpt node has no L facts or E facts. -/
theorem ambientRootType_unique
    (A : EnumeratedPartialStructure 0 0 0) (v : Nat) :
    A.partialTypeAt 0 v = emptyRootType := by
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
    | some i => exact Fin.elim0 i
    | none =>
      cases b with
      | some j => exact Fin.elim0 j
      | none =>
        simpa [emptyRootType] using
          (A.partialTypeAt_no_typeE_loop 0 v)

end SuccessorTree.V10.EmptyKpt

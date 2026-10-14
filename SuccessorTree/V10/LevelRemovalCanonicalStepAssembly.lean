import SuccessorTree.V10.LevelRemovalUnifiedParameter
import SuccessorTree.V10.LevelRemovalColumnTransport
import SuccessorTree.V10.LevelRemovalTerminalLetter
import SuccessorTree.V10.CanonicalStepGraph
import Mathlib.Tactic

/-!
# Assemble an actual canonical Kpt successor after ordinary deletion

The finite record calculations for predecessor restriction, terminal
Sigma letter, empty/singleton canonical parameter, and valid new
ordinary E column are now checked separately. Here we combine them
into the genuine IsCanonicalKptStep graph whenever the resulting
source/target and parameter nodes are admissible.

The sole remaining input is an explicit pointwise identification of
the mapped parameter list with the raw optional-parameter transport.
This is exactly the interface provided separately by the intrinsic
M2 candidate, not a new age/successor axiom.

The strict M2 gap is needed when the removed coordinate is
immediately before the new ordinary vertex; the guard prevents the
new positive free cut from equalling the shortened predecessor level.
-/

namespace SuccessorTree.V10

/-- A complete canonical successor record remains a genuine
canonical successor after deleting an earlier ordinary coordinate,
provided its admissible source/target and mapped parameters are named.

The proof DERIVES all the remaining graph fields: the full terminal
letter, the valid shortened E/free-cut column, and the strict
zero-or-below-source canonical gate. No IsCanonicalKptStep hypothesis
is added for the shortened target. -/
theorem canonicalKptStep_of_deleted_record
    {k db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Q : PartialTypeWithE (k + 2) db du dd)
    (f : Nat) (hf : f ≤ k + 1)
    (hValid : ValidNewOrdinaryColumn Q f)
    (hOldGate : f = 0 ∨ f < k + 1)
    (m : Nat) (hm : m < k + 1) (hmPos : 0 < m)
    (hSafe : m < k ∨ f < m)
    (a' b' : AdmissibleKptNode family)
    (pOld pNew : List (AdmissibleKptNode family))
    (c : RawKptLetter db du dd)
    (hA : a'.1 =
      (⟨k,
        (Q.deleteOrdinary m (by omega)).restrict (Nat.le_succ k)⟩ :
        RawPartialTypeNode db du dd))
    (hB : b'.1 =
      (⟨k + 1,Q.deleteOrdinary m (by omega)⟩ :
        RawPartialTypeNode db du dd))
    (hLetter : c = Q.terminalLetter)
    (hOldParam : pOld.map (fun x => x.1) =
      (Q.canonicalParameterRecord f hf).toList)
    (hNewParam : pNew.map (fun x => x.1) =
      (pOld.map (fun x => x.1)).map
        (rawPartialTypeDeleteIfAbove m)) :
    IsCanonicalKptStep family a' pNew c b' := by
  classical
  let Q' : PartialTypeWithE (k + 1) db du dd :=
    Q.deleteOrdinary m (by omega)
  let f' : Nat := deleteAtCut m f
  have hf' : f' ≤ k := deleteAtCut_le_shorter k m f hm hf
  have hLetter' : c = Q'.terminalLetter := by
    calc
      c = Q.terminalLetter := hLetter
      _ = Q'.terminalLetter :=
        (Q.deleteOrdinary_terminalLetter m hm).symm
  have hValid' : ValidNewOrdinaryColumn Q' f' :=
    validNewOrdinaryColumn_deleteOrdinary Q m f hm hf hValid
  have hOption :
      Q'.canonicalParameterRecord f' hf' =
        (Q.canonicalParameterRecord f hf).map
          (rawPartialTypeDeleteIfAbove m) := by
    exact Q.canonicalParameterRecord_delete_unified m f hm hf hmPos
  have hParam' :
      pNew.map (fun x => x.1) =
        (Q'.canonicalParameterRecord f' hf').toList := by
    calc
      pNew.map (fun x => x.1) =
          (pOld.map (fun x => x.1)).map
            (rawPartialTypeDeleteIfAbove m) := hNewParam
      _ = (Q.canonicalParameterRecord f hf).toList.map
            (rawPartialTypeDeleteIfAbove m) := by rw [hOldParam]
      _ = ((Q.canonicalParameterRecord f hf).map
            (rawPartialTypeDeleteIfAbove m)).toList := by
          cases h : Q.canonicalParameterRecord f hf <;> simp [h]
      _ = (Q'.canonicalParameterRecord f' hf').toList :=
        congrArg Option.toList hOption.symm
  have hGate' : f' = 0 ∨ f' < k := by
    by_cases hmf : m < f
    · have hCut : f' = f - 1 := by
        simp [f', deleteAtCut, hmf]
      have hOldLt : f < k + 1 := by
        rcases hOldGate with hz | hh
        · omega
        · exact hh
      right
      omega
    · have hCut : f' = f := by
        simp [f', deleteAtCut, hmf]
      rcases hOldGate with hz | hh
      · left
        omega
      · right
        rcases hSafe with hmk | hfm <;> omega
  exact ⟨k, f', hf', Q', hA, hB, hLetter',
    hValid', hParam', hGate'⟩

end SuccessorTree.V10

import SuccessorTree.V10.LocalAgeNeutralGapSucc
import SuccessorTree.V10.LocalAgeCanonicalInputs
import SuccessorTree.V10.LocalAgeNeutralParameter
import SuccessorTree.V10.LocalAgeNeutralLetter
import Mathlib.Tactic

/-!
# The actual successor commutes with neutral insertion above the gap

For a successor edge of the actual admissible Kpt S-tree based at level
n>=ell>0, the neutral map shifts its levels to n+1 and n+2.
Prefix preservation therefore makes the mapped pair another genuine cover.

Every admissible cover admits its EXACT canonical successor inputs. We
identify the source inputs from a forbidden-free ambient representative of
the source target, and the target inputs from its neutral insertion.
The earlier finite-record results prove these inputs are literally the
same after mapping the parameter list, while the terminal Sigma letter is
unchanged. Uniqueness of the canonical decomposition therefore forces

  succ (D a) (p.map D) c = some (D b).

There is no extra weakness in this above-gap case. The below-gap/crossing
edge is handled separately in LocalAgeNeutralGapSucc.
-/

namespace SuccessorTree.V10

/-- The actual admissible-Sigma successor commutes *exactly* with the
total neutral insertion whenever its source level is at/above the gap. -/
theorem neutralKptSkip_weak_succ_above_gap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : AdmissibleKptSigma family}
    (hSucc : (admissibleKptSTree family).succ a p c = some b)
    (hBaseHigh : ell ≤ a.1.1) :
    (admissibleKptSTree family).succ
      (neutralKptSkip family ell hellPos a)
      (p.map (neutralKptSkip family ell hellPos)) c =
      some (neutralKptSkip family ell hellPos b) := by
  let n : Nat := a.1.1
  have hSource : IsCanonicalKptStep family a p c.1 b :=
    canonicalKptSucc_spec family (by
      change canonicalKptSucc family a p c.1 = some b
      exact hSucc)
  have hOldCover : a ⋖ b :=
    (admissibleKptSTree family).covBy_of_succ_eq_some hSucc
  have hbLev : b.1.1 = n + 1 := by
    have h := LevelTree.covBy_level_eq hOldCover
    change b.1.1 = a.1.1 + 1 at h
    exact h
  have hBHigh : ell ≤ b.1.1 := by omega
  obtain ⟨A, v, hell, hv, hAvoid, hRaw, hImage⟩ :=
    neutralKptImage_isImage family ell hellPos b hBHigh
  have hFree : A.freeLevel v = n + 1 := by
    have h := congrArg Sigma.fst hRaw
    change b.1.1 = A.freeLevel v at h
    omega
  have hn : n < A.size := by
    have h := A.freeLevel_le v
    omega
  have hnGE : ell ≤ n := hBaseHigh
  have hNShift : insertAddress ell n = n + 1 :=
    insertAddress_above ell n hnGE
  let B := neutralInsert A ell hell hellPos
  have hBSize : B.size = A.size + 1 := rfl
  have hvB : insertAddress ell v < B.size := by
    have hVG : ell ≤ v := by
      have h := A.freeLevel_le v
      omega
    rw [insertAddress_above ell v hVG, hBSize]
    omega
  have hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L :=
    neutralInsert_preserves_avoidance family A ell hell hellPos hAvoid
  have hBFree : B.freeLevel (insertAddress ell v) = n + 2 := by
    have h := neutralInsert_freeLevel_old A ell hell hellPos v hv
    have hncut : ¬ A.freeLevel v < ell := by omega
    have hh : B.freeLevel (insertAddress ell v) =
        A.freeLevel v + 1 := by
      simpa only [B, if_neg hncut] using h
    omega
  have hImageEq :
      (neutralKptSkip family ell hellPos b).1 =
        B.rawTypeAtFree (insertAddress ell v) := by
    rw [neutralKptSkip_above family ell hellPos b hBHigh]
    exact hImage
  have hMappedPrefix :
      neutralKptSkip family ell hellPos a ≤
        neutralKptSkip family ell hellPos b :=
    neutralKptSkip_prefix family ell hellPos b a hOldCover.le
  have hMappedCover :
      neutralKptSkip family ell hellPos a ⋖
        neutralKptSkip family ell hellPos b := by
    apply LevelTree.covBy_of_le_level_succ hMappedPrefix
    change
      (neutralKptSkip family ell hellPos b).1.1 =
        (neutralKptSkip family ell hellPos a).1.1 + 1
    rw [neutralKptSkip_level, neutralKptSkip_level]
    simp [hBaseHigh, hBHigh]
    omega
  obtain ⟨p', c', hStepB⟩ :=
    canonicalKptStep_exists_of_covBy family hMappedCover
  have hInputA :=
    canonicalKptStep_inputs_of_ambient family A v n hv hAvoid
      hFree hSource hRaw
  have hInputB :=
    canonicalKptStep_inputs_of_ambient family B (insertAddress ell v)
      (n + 1) hvB hAvoidB hBFree hStepB hImageEq
  let parA : AdmissibleKptNode family :=
    ⟨A.rawTypeAtFree n, ⟨A,n,hn,hAvoid,rfl⟩⟩
  have hnB : n + 1 < B.size := by
    rw [hBSize]
    omega
  let parB : AdmissibleKptNode family :=
    ⟨B.rawTypeAtFree (n+1), ⟨B,n+1,hnB,hAvoidB,rfl⟩⟩
  have hLetterA :
      c.1 = (A.partialTypeAt (n+1) v).terminalLetter := hInputA.1
  have hLetterB :
      c' = (B.partialTypeAt (n+2) (insertAddress ell v)).terminalLetter :=
    hInputB.1
  have hLetterTransport :
      (B.partialTypeAt (n+2) (insertAddress ell v)).terminalLetter =
        (A.partialTypeAt (n+1) v).terminalLetter := by
    have hh := neutralInsert_terminalLetter_eq A ell hell hellPos
      n v hn hv
    simpa only [B, hNShift, Nat.add_assoc] using hh
  have hLetter : c' = c.1 :=
    hLetterB.trans (hLetterTransport.trans hLetterA.symm)
  have hParamA :
      p = (if A.freeLevel n = 0 then [] else [parA]) := hInputA.2
  have hParamB :
      p' = (if B.freeLevel (n+1) = 0 then [] else [parB]) := hInputB.2
  have hParamTransport :
      (if B.freeLevel (n+1) = 0 then [] else [parB]) =
        (if A.freeLevel n = 0 then [] else [parA]).map
          (neutralKptSkip family ell hellPos) := by
    have hh := neutralInsert_canonicalParameterList_map
      family A ell hell hellPos n hn hAvoid
    simpa only [B, parA, parB, hNShift] using hh
  have hParam : p' = p.map (neutralKptSkip family ell hellPos) := by
    calc
      p' = (if B.freeLevel (n+1) = 0 then [] else [parB]) := hParamB
      _ = (if A.freeLevel n = 0 then [] else [parA]).map
          (neutralKptSkip family ell hellPos) := hParamTransport
      _ = p.map (neutralKptSkip family ell hellPos) := by rw [hParamA]
  have hStepImage : IsCanonicalKptStep family
      (neutralKptSkip family ell hellPos a)
      (p.map (neutralKptSkip family ell hellPos))
      c.1 (neutralKptSkip family ell hellPos b) := by
    rw [←hParam, ←hLetter]
    exact hStepB
  change canonicalKptSucc family
    (neutralKptSkip family ell hellPos a)
    (p.map (neutralKptSkip family ell hellPos))
    c.1 = some (neutralKptSkip family ell hellPos b)
  exact canonicalKptSucc_eq_some_of_step family hStepImage

end SuccessorTree.V10

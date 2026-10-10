import SuccessorTree.V10.PrescribedB3Upper
import Mathlib.Tactic

/-!
# The prescribed inserted ordinary L-socle is the actual output socle

The B3 age-test of Lemma 6.51 also needs its INITIAL socle to agree
literally with a forbidden-free witness of the chosen prescribed target
f(S0). The present module proves that agreement on ALL unary, diagonal
and directed binary atoms.

B1 supplies the old ordinary L-socle through ell; matching compatibility
identifies it with the original finite partial structure A. The lower
column selected from f(S0) supplies the new coordinate ell and every
incident old-L pair, including negative facts. Thus the inserted L model
has exactly f(S0)'s complete ordinary socle through ell+1, regardless of
the distinguished type vertex.

Given a genuine forbidden-free witness W of f(S0), this equality is
precisely the SameInitialL premise of the finite three-clause age test.
Auxiliary E atoms of the age-test model are irrelevant: B3 concerns L.
-/

namespace SuccessorTree.V10

/-- The complete prescribed ordinary L-socle on first ell+1 vertices is
literally the inserted L-socle when one compatible f(S0) supplies the
selected lower column. In particular no directed nonrelation is lost. -/
theorem PrescribedBoringData.insertedData_ordinary_L_agrees
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (S0 : PartialTypeWithE ell db du dd)
    (hS0 : S0 ∈ F.source)
    (base : Nat)
    (hCompatible : SameOrdinaryAtCut S0 (A.partialTypeAt ell base)) :
    (∀ i j : Fin (ell+1), ∀ t : Fin db,
      (insertL A ell (F.insertedLData A
          (lowerInsertedColumn (F.target S0)))).binary
        i.val j.val t =
      (F.target S0).lReduct.binary (some i) (some j) t) ∧
    (∀ i : Fin (ell+1), ∀ t : Fin du,
      (insertL A ell (F.insertedLData A
          (lowerInsertedColumn (F.target S0)))).unary
        i.val t =
      (F.target S0).lReduct.unary (some i) t) ∧
    (∀ i : Fin (ell+1), ∀ t : Fin dd,
      (insertL A ell (F.insertedLData A
          (lowerInsertedColumn (F.target S0)))).diagonal
        i.val t =
      (F.target S0).lReduct.diagonal (some i) t) := by
  let Q := F.target S0
  have hExt := F.extendsSource S0 hS0
  have hOldBinary (i j : Fin ell) (t : Fin db) :
      Q.lReduct.binary (some i.castSucc) (some j.castSucc) t =
        A.L.binary i.val j.val t := by
    have hh := congrArg
      (fun T : PartialTypeWithE ell db du dd =>
        T.lReduct.binary (some i) (some j) t) hExt
    change Q.lReduct.binary (some i.castSucc) (some j.castSucc) t =
      S0.lReduct.binary (some i) (some j) t at hh
    exact hh.trans (hCompatible.1 i j t)
  have hOldUnary (i : Fin ell) (t : Fin du) :
      Q.lReduct.unary (some i.castSucc) t =
        A.L.unary i.val t := by
    have hh := congrArg
      (fun T : PartialTypeWithE ell db du dd =>
        T.lReduct.unary (some i) t) hExt
    change Q.lReduct.unary (some i.castSucc) t =
      S0.lReduct.unary (some i) t at hh
    exact hh.trans (hCompatible.2.1 i t)
  have hOldDiagonal (i : Fin ell) (t : Fin dd) :
      Q.lReduct.diagonal (some i.castSucc) t =
        A.L.diagonal i.val t := by
    have hh := congrArg
      (fun T : PartialTypeWithE ell db du dd =>
        T.lReduct.diagonal (some i) t) hExt
    change Q.lReduct.diagonal (some i.castSucc) t =
      S0.lReduct.diagonal (some i) t at hh
    exact hh.trans (hCompatible.2.2.1 i t)
  refine ⟨?_, ?_, ?_⟩
  · intro i j t
    induction i using Fin.lastCases with
    | last =>
        induction j using Fin.lastCases with
        | last =>
            simp [insertL, PrescribedBoringData.insertedLData,
              gatedInsertedLData, lowerInsertedColumn, Q]
        | cast j =>
            have hjlt : j.val < ell := j.isLt
            have hjne : j.val ≠ ell := Nat.ne_of_lt hjlt
            simp [insertL, PrescribedBoringData.insertedLData,
              gatedInsertedLData, lowerInsertedColumn, removeInserted,
              hjlt, hjne, Q] <;> congr 2
    | cast i =>
        induction j using Fin.lastCases with
        | last =>
            have hilt : i.val < ell := i.isLt
            have hi : i.val ≠ ell := Nat.ne_of_lt hilt
            simp [insertL, PrescribedBoringData.insertedLData,
              gatedInsertedLData, lowerInsertedColumn, removeInserted,
              hilt, hi, Q] <;> congr 2
        | cast j =>
            have hi : i.val ≠ ell := by omega
            have hj : j.val ≠ ell := by omega
            simpa [insertL, hi, hj, removeInserted, i.isLt, j.isLt]
              using (hOldBinary i j t).symm
  · intro i t
    induction i using Fin.lastCases with
    | last =>
        simp [insertL, PrescribedBoringData.insertedLData,
          gatedInsertedLData, lowerInsertedColumn, Q]
    | cast i =>
        have hi : i.val ≠ ell := by omega
        simpa [insertL, hi, removeInserted, i.isLt]
          using (hOldUnary i t).symm
  · intro i t
    induction i using Fin.lastCases with
    | last =>
        simp [insertL, PrescribedBoringData.insertedLData,
          gatedInsertedLData, lowerInsertedColumn, Q]
    | cast i =>
        have hi : i.val ≠ ell := by omega
        simpa [insertL, hi, removeInserted, i.isLt]
          using (hOldDiagonal i t).symm

/-- A finite forbidden-free witness W of f(S0) provides the actual
common initial L-socle used in B3. This is equality of all ordinary
L relations and their negative values, with no E-age hypothesis. -/
theorem PrescribedBoringData.insertedData_common_initial_L
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A W : EnumeratedPartialStructure db du dd)
    (S0 : PartialTypeWithE ell db du dd)
    (hS0 : S0 ∈ F.source)
    (base w : Nat)
    (hCompatible : SameOrdinaryAtCut S0 (A.partialTypeAt ell base))
    (hellA : ell ≤ A.size)
    (hellW : ell < W.size)
    (hWitness : F.target S0 = W.partialTypeAt (ell + 1) w) :
    SameInitialL
      (insertL A ell
        (F.insertedLData A (lowerInsertedColumn (F.target S0))))
      W.L ell := by
  have hData := F.insertedData_ordinary_L_agrees
    A S0 hS0 base hCompatible
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    constructor
    · intro _
      exact (W.carrier_iff x).2 (by omega)
    · intro _
      change x < A.size + 1
      omega
  · intro x y hx hy t
    let i : Fin (ell+1) := ⟨x, by omega⟩
    let j : Fin (ell+1) := ⟨y, by omega⟩
    have hW : (F.target S0).lReduct.binary (some i) (some j) t =
        W.L.binary x y t := by
      rw [hWitness]
      rfl
    exact (hData.1 i j t).trans hW
  · intro x hx t
    let i : Fin (ell+1) := ⟨x, by omega⟩
    have hW : (F.target S0).lReduct.unary (some i) t =
        W.L.unary x t := by
      rw [hWitness]
      rfl
    exact (hData.2.1 i t).trans hW
  · intro x hx t
    let i : Fin (ell+1) := ⟨x, by omega⟩
    have hW : (F.target S0).lReduct.diagonal (some i) t =
        W.L.diagonal x t := by
      rw [hWitness]
      rfl
    exact (hData.2.2 i t).trans hW

end SuccessorTree.V10

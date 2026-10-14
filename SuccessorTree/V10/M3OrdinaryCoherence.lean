import SuccessorTree.V10.M3MiddleCanonicalStep
import SuccessorTree.V10.PrescribedBoringData
import Mathlib.Tactic

/-!
# M3's earlier free cut and lower clone column depend only on the ordinary socle

Two source complete L+ types at the same level ell may have different
distinguished type vertices. M3 duplicates one fixed ordinary
coordinate n<ell, so its free cut must be independent of the
representative and of the distinguished vertex whenever the two
source types are compatible on their OLD ordinary socles.

The old ordinary E column determines the free cut of n uniquely.
All singleton facts and two directed L pairs with lower coordinates
are likewise in the old ordinary L-socle. Thus the clone's new
ordinary lower column is choice-independent, including absent atoms.

This is the atomic B2 input; full output SameOrdinarySocle requires
the separate E insertion and retained old-column transport lemmas.
-/

namespace SuccessorTree.V10

/-- Ordinary L+ compatibility of two extracted source types fixes
the canonical E-free cut of any old ordinary coordinate n<ell,
regardless of their ambient representatives and type vertices. -/
theorem sameOrdinaryAtCut_oldFreeLevel_eq
    {ell db du dd : Nat}
    (A C : EnumeratedPartialStructure db du dd)
    (v w n : Nat) (hn : n < ell)
    (hComp : SameOrdinaryAtCut
      (A.partialTypeAt ell v) (C.partialTypeAt ell w)) :
    A.freeLevel n = C.freeLevel n := by
  have hE (x : Nat) (hx : x < ell) :
      A.E x n = C.E x n := by
    let i : Fin ell := ⟨x,hx⟩
    let j : Fin ell := ⟨n,hn⟩
    have hh := hComp.2.2.2 i j
    change A.E x n = C.E x n at hh
    exact hh
  have hAF : A.E (A.freeLevel n) n = false :=
    (canonicalFreeLevel_isFreeCut A.E A.spaced A.downward n).2
  have hCF : C.E (C.freeLevel n) n = false :=
    (canonicalFreeLevel_isFreeCut C.E C.spaced C.downward n).2
  by_contra hneq
  have hCases :
      A.freeLevel n < C.freeLevel n ∨
        C.freeLevel n < A.freeLevel n := by omega
  rcases hCases with hAC | hCA
  · have hCTrue : C.E (A.freeLevel n) n = true :=
      (C.E_iff_freeLevel (A.freeLevel n) n).2 hAC
    have hEq := hE (A.freeLevel n)
      (lt_of_le_of_lt (A.freeLevel_le n) hn)
    rw [hAF,hCTrue] at hEq
    cases hEq
  · have hATrue : A.E (C.freeLevel n) n = true :=
      (A.E_iff_freeLevel (C.freeLevel n) n).2 hCA
    have hEq := hE (C.freeLevel n)
      (lt_of_le_of_lt (C.freeLevel_le n) hn)
    rw [hATrue,hCF] at hEq
    cases hEq

/-- The COMPLETE new lower L-column for a middle duplicate depends
only on the ordinary source socle: clone loops, unary, diagonal and
both directed new/lower pairs are equal for compatible sources.
There is no same-type-vertex or identical ambient-representative
hypothesis. -/
theorem middleCloneInsertedLData_lower_eq_of_ordinaryCompatibility
    {ell db du dd : Nat}
    (A C : EnumeratedPartialStructure db du dd)
    (v w n : Nat) (hn : n < ell)
    (hComp : SameOrdinaryAtCut
      (A.partialTypeAt ell v) (C.partialTypeAt ell w)) :
    ((∀ r : Fin db,
      (middleCloneInsertedLData A ell n).loop r =
        (middleCloneInsertedLData C ell n).loop r) ∧
     (∀ r : Fin du,
      (middleCloneInsertedLData A ell n).unary r =
        (middleCloneInsertedLData C ell n).unary r) ∧
     (∀ r : Fin dd,
      (middleCloneInsertedLData A ell n).diagonal r =
        (middleCloneInsertedLData C ell n).diagonal r) ∧
     (∀ x, x < ell → ∀ r : Fin db,
      (middleCloneInsertedLData A ell n).incoming x r =
        (middleCloneInsertedLData C ell n).incoming x r) ∧
     (∀ x, x < ell → ∀ r : Fin db,
      (middleCloneInsertedLData A ell n).outgoing x r =
        (middleCloneInsertedLData C ell n).outgoing x r)) := by
  have hCut :=
    sameOrdinaryAtCut_oldFreeLevel_eq A C v w n hn hComp
  have hB (x y : Nat) (hx : x < ell) (hy : y < ell)
      (r : Fin db) : A.L.binary x y r = C.L.binary x y r := by
    let i : Fin ell := ⟨x,hx⟩
    let j : Fin ell := ⟨y,hy⟩
    have hh := hComp.1 i j r
    change A.L.binary x y r = C.L.binary x y r at hh
    exact hh
  have hU (x : Nat) (hx : x < ell) (r : Fin du) :
      A.L.unary x r = C.L.unary x r := by
    let i : Fin ell := ⟨x,hx⟩
    have hh := hComp.2.1 i r
    change A.L.unary x r = C.L.unary x r at hh
    exact hh
  have hD (x : Nat) (hx : x < ell) (r : Fin dd) :
      A.L.diagonal x r = C.L.diagonal x r := by
    let i : Fin ell := ⟨x,hx⟩
    have hh := hComp.2.2.1 i r
    change A.L.diagonal x r = C.L.diagonal x r at hh
    exact hh
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r
    change A.L.binary n n r = C.L.binary n n r
    exact hB n n hn hn r
  · intro r
    change A.L.unary n r = C.L.unary n r
    exact hU n hn r
  · intro r
    change A.L.diagonal n r = C.L.diagonal n r
    exact hD n hn r
  · intro x hx r
    by_cases hc : x < A.freeLevel n
    · have hcC : x < C.freeLevel n := by
        rw [←hCut]
        exact hc
      simp [middleCloneInsertedLData, hx, hc, hcC]
      exact hB x n hx hn r
    · have hcC : ¬ x < C.freeLevel n := by
        rw [←hCut]
        exact hc
      simp [middleCloneInsertedLData, hx, hc, hcC]
  · intro x hx r
    by_cases hc : x < A.freeLevel n
    · have hcC : x < C.freeLevel n := by
        rw [←hCut]
        exact hc
      simp [middleCloneInsertedLData, hx, hc, hcC]
      exact hB n x hn hx r
    · have hcC : ¬ x < C.freeLevel n := by
        rw [←hCut]
        exact hc
      simp [middleCloneInsertedLData, hx, hc, hcC]

end SuccessorTree.V10

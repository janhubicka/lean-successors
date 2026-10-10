import SuccessorTree.V10.LocalAgeNeutralLetter
import SuccessorTree.V10.LocalAgeNeutralFullPrefix
import Mathlib.Tactic

/-!
# The actual canonical successor parameter commutes with neutral insertion

Every ordinary vertex n of a forbidden-free finite partial structure A
represents a genuine admissible Kpt type at its unique free E-cut f.

The neutral inserted ambient B contains the shifted old vertex
insertAddress ell n. Its free cut is f when f<ell and f+1 otherwise.
The induced complete type is exactly the image of the source type under
the TOTAL neutralKptSkip function, even when the source type is level 0
and hence unchanged.

Therefore the canonical parameter list (empty at cut zero, otherwise
exactly the one type of the newly introduced ordinary vertex) is
transported by List.map neutralKptSkip. This is a genuine equality of
admissible Kpt nodes, not only of raw L-traces.

Together with LocalAgeNeutralLetter these are the two atomic components
needed for the weak-successor condition. The global ShapeMap proof
remains a separate step, especially the source edge crossing ell.
-/

namespace SuccessorTree.V10

/-- A retained old vertex has canonical free cut zero after neutral
insertion iff it had cut zero before insertion. -/
theorem neutralInsert_freeCut_zero_iff
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (n : Nat) (hn : n < A.size) :
    (neutralInsert A ell hell hellPos).freeLevel (insertAddress ell n) = 0 ↔
      A.freeLevel n = 0 := by
  rw [neutralInsert_freeLevel_old A ell hell hellPos n hn]
  by_cases h : A.freeLevel n < ell
  · simp [h]
  · simp [h]
    omega

/-- The actual selected neutral image of an old vertex's admissible Kpt
type equals the type extracted from the shifted old vertex in the same
neutral-inserted ambient structure. There are no additional hypotheses
on f=fl_A(n), and no hidden witness choice. -/
theorem neutralKptSkip_original_type_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (n : Nat) (hn : n < A.size)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    (neutralKptSkip family ell hellPos
      (⟨A.rawTypeAtFree n, ⟨A, n, hn, hAvoid, rfl⟩⟩ :
        AdmissibleKptNode family)).1 =
      (neutralInsert A ell hell hellPos).rawTypeAtFree
        (insertAddress ell n) := by
  let a : AdmissibleKptNode family :=
    ⟨A.rawTypeAtFree n, ⟨A, n, hn, hAvoid, rfl⟩⟩
  let B := neutralInsert A ell hell hellPos
  by_cases hf : A.freeLevel n < ell
  · have ha : a.1.1 < ell := hf
    have hFix := neutralKptSkip_fixed_below family ell hellPos a ha
    have hBFree : B.freeLevel (insertAddress ell n) = A.freeLevel n := by
      have h := neutralInsert_freeLevel_old A ell hell hellPos n hn
      simpa only [B, if_pos hf] using h
    have hBType : B.partialTypeAt (A.freeLevel n) (insertAddress ell n) =
        A.partialTypeAt (A.freeLevel n) n :=
      neutralInsert_type_below_gap A ell hell hellPos n (A.freeLevel n)
        hn (Nat.le_of_lt hf)
    calc
      (neutralKptSkip family ell hellPos a).1 = a.1 :=
        congrArg Subtype.val hFix
      _ = A.rawTypeAtFree n := rfl
      _ = B.rawTypeAtFree (insertAddress ell n) := by
        change
          (⟨A.freeLevel n, A.partialTypeAt (A.freeLevel n) n⟩ :
            RawPartialTypeNode db du dd) =
          (⟨B.freeLevel (insertAddress ell n),
             B.partialTypeAt (B.freeLevel (insertAddress ell n))
               (insertAddress ell n)⟩ : RawPartialTypeNode db du dd)
        rw [hBFree]
        exact congrArg (Sigma.mk (A.freeLevel n)) hBType.symm
  · have ha : ell ≤ a.1.1 := by
      change ell ≤ A.freeLevel n
      omega
    have hAbove := neutralKptSkip_above family ell hellPos a ha
    have hEq := neutralKptImage_eq_of_representation family ell
      hellPos a ha A n hn hAvoid rfl hell
    change (neutralKptSkip family ell hellPos a).1 =
      B.rawTypeAtFree (insertAddress ell n)
    rw [hAbove]
    exact hEq

/-- The SOURCE and TARGET canonical parameter lists of a retained old
ordinary vertex agree after the total neutral Kpt insertion map. The
empty parameter remains empty; the positive singleton is mapped to the
exact new admissible type. -/
theorem neutralInsert_canonicalParameterList_map
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (n : Nat) (hn : n < A.size)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    let B := neutralInsert A ell hell hellPos
    let src : AdmissibleKptNode family :=
      ⟨A.rawTypeAtFree n, ⟨A,n,hn,hAvoid,rfl⟩⟩
    let hBn : insertAddress ell n < B.size := by
      change insertAddress ell n < A.size + 1
      by_cases hlt : n < ell
      · rw [insertAddress_below ell n hlt]
        omega
      · rw [insertAddress_above ell n (by omega)]
        omega
    let hBAvoid : ∀ bad, bad ∈ family → bad.Avoids B.L :=
      neutralInsert_preserves_avoidance family A ell hell hellPos hAvoid
    let dst : AdmissibleKptNode family :=
      ⟨B.rawTypeAtFree (insertAddress ell n),
        ⟨B, insertAddress ell n, hBn, hBAvoid, rfl⟩⟩
    (if B.freeLevel (insertAddress ell n) = 0 then [] else [dst]) =
      (if A.freeLevel n = 0 then [] else [src]).map
        (neutralKptSkip family ell hellPos) := by
  dsimp
  let src : AdmissibleKptNode family :=
    ⟨A.rawTypeAtFree n, ⟨A,n,hn,hAvoid,rfl⟩⟩
  let B := neutralInsert A ell hell hellPos
  have hZero := neutralInsert_freeCut_zero_iff A ell hell hellPos n hn
  have hRaw : (neutralKptSkip family ell hellPos src).1 =
      B.rawTypeAtFree (insertAddress ell n) :=
    neutralKptSkip_original_type_eq family A ell hell hellPos n hn hAvoid
  by_cases hz : A.freeLevel n = 0
  · have hzB : B.freeLevel (insertAddress ell n) = 0 :=
      hZero.mpr hz
    simp [hz, hzB]
  · have hzB : B.freeLevel (insertAddress ell n) ≠ 0 := by
      intro h
      exact hz (hZero.mp h)
    simp only [if_neg hz, if_neg hzB, List.map_cons, List.map_nil]
    congr 1
    exact Subtype.ext hRaw

end SuccessorTree.V10

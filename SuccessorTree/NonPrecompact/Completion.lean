import SuccessorTree.NonPrecompact.BananaStructure

/-!
# Completion of finite BANANA pairings

Every finite bilinear pairing embeds into a standard perfect pairing.
In chosen coordinates there is a direct construction: for a pairing matrix
`A : F₂^r → F₂^l`, send
`x ↦ (x,0)` on the left and `y ↦ (Ay,y)` on the right.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

namespace BananaMatrixStructure

variable {l r : ℕ} (A : BananaMatrixStructure l r)

/-- Left map of the explicit perfect completion. -/
def completionLeft (A : BananaMatrixStructure l r) :
    (Fin l → F2) →ₗ[F2] (Fin (l + r) → F2) where
  toFun x := Fin.append x 0
  map_add' x y := by
    funext i
    change
      Fin.append (fun j => x j + y j) 0 i =
        Fin.append x 0 i + Fin.append y 0 i
    simpa [Fin.append] using
      (Fin.addCases_castAdd_natAdd
        (v := fun j : Fin (l + r) =>
          Fin.append x 0 j + Fin.append y 0 j) i)
  map_smul' c x := by
    funext i
    change
      Fin.append (fun j => c * x j) 0 i =
        c * Fin.append x 0 i
    simpa [Fin.append] using
      (Fin.addCases_castAdd_natAdd
        (v := fun j : Fin (l + r) => c * Fin.append x 0 j) i)

/-- Right map of the explicit perfect completion. -/
def completionRight (A : BananaMatrixStructure l r) :
    (Fin r → F2) →ₗ[F2] (Fin (l + r) → F2) where
  toFun y := Fin.append (A.pairing *ᵥ y) y
  map_add' x y := by
    funext i
    change
      Fin.append
          (fun j => (A.pairing *ᵥ x) j + (A.pairing *ᵥ y) j)
          (fun j => x j + y j) i =
        Fin.append (A.pairing *ᵥ x) x i +
          Fin.append (A.pairing *ᵥ y) y i
    simpa [Fin.append] using
      (Fin.addCases_castAdd_natAdd
        (v := fun j : Fin (l + r) =>
          Fin.append (A.pairing *ᵥ x) x j +
            Fin.append (A.pairing *ᵥ y) y j) i)
  map_smul' c x := by
    funext i
    change
      Fin.append
          (fun j => c * (A.pairing *ᵥ x) j)
          (fun j => c * x j) i =
        c * Fin.append (A.pairing *ᵥ x) x i
    simpa [Fin.append] using
      (Fin.addCases_castAdd_natAdd
        (v := fun j : Fin (l + r) =>
          c * Fin.append (A.pairing *ᵥ x) x j) i)

theorem completionLeft_injective :
    Function.Injective A.completionLeft := by
  intro x y h
  funext i
  have hi := congrFun h (Fin.castAdd r i)
  simpa [completionLeft] using hi

theorem completionRight_injective :
    Function.Injective A.completionRight := by
  intro x y h
  funext i
  have hi := congrFun h (Fin.natAdd l i)
  simpa [completionRight] using hi

/-- The explicit completion preserves the arbitrary source pairing. -/
theorem completion_pairing_apply
    (x : Fin l → F2) (y : Fin r → F2) :
    (perfectBanana (l + r)).eval
        (A.completionLeft x) (A.completionRight y) =
      A.eval x y := by
  rw [perfectBanana_eval]
  unfold completionLeft completionRight eval
  change
    (∑ i : Fin (l + r),
      Fin.append x 0 i * Fin.append (A.pairing *ᵥ y) y i) =
      x ⬝ᵥ (A.pairing *ᵥ y)
  rw [Fin.sum_univ_add]
  simp [dotProduct]

/-- Every finite BANANA pairing embeds into the standard perfect pairing
of dimension `l+r`.  This is the coordinate version of the manuscript's
completion lemma. -/
def completionEmbedding :
    BananaMatrixEmbedding A (perfectBanana (l + r)) where
  left := A.completionLeft
  right := A.completionRight
  left_injective := A.completionLeft_injective
  right_injective := A.completionRight_injective
  pairing_apply := A.completion_pairing_apply

end BananaMatrixStructure

end SuccessorTree.NonPrecompact

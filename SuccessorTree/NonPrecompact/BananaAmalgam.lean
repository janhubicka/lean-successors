import SuccessorTree.NonPrecompact.BananaStructure

/-!
# Standard block amalgams for BANANA pairings

This file formalises the finite coordinate construction used in the
circulation proof that the BANANA class is a strong amalgamation class.

After choosing complements, the two extensions of a common two-sorted
substructure have coordinate types
  L_A ⊕ U_B, R_A ⊕ V_B
and
  L_A ⊕ U_C, R_A ⊕ V_C.
The amalgam uses coordinates
  L_A ⊕ (U_B ⊕ U_C), R_A ⊕ (V_B ⊕ V_C),
keeps both old pairing matrices, and sets the two new cross blocks to zero.
-/

namespace SuccessorTree.NonPrecompact

/-- Coordinate inclusion of A ⊕ X into A ⊕ (X ⊕ Y). -/
def sumAmalgamIndexLeft {A X Y : Type*} :
    Sum A X → Sum A (Sum X Y)
  | .inl a => .inl a
  | .inr x => .inr (.inl x)

/-- Coordinate inclusion of A ⊕ Y into A ⊕ (X ⊕ Y). -/
def sumAmalgamIndexRight {A X Y : Type*} :
    Sum A Y → Sum A (Sum X Y)
  | .inl a => .inl a
  | .inr y => .inr (.inr y)

theorem sumAmalgamIndexLeft_injective {A X Y : Type*} :
    Function.Injective
      (sumAmalgamIndexLeft : Sum A X → Sum A (Sum X Y)) := by
  intro i j h
  cases i <;> cases j <;> simp [sumAmalgamIndexLeft] at h ⊢
  · exact h
  · exact h

theorem sumAmalgamIndexRight_injective {A X Y : Type*} :
    Function.Injective
      (sumAmalgamIndexRight : Sum A Y → Sum A (Sum X Y)) := by
  intro i j h
  cases i <;> cases j <;> simp [sumAmalgamIndexRight] at h ⊢
  · exact h
  · exact h

/-- Extend a coordinate vector on A ⊕ X by zero on the new Y-block. -/
def sumAmalgamLinearLeft
    {A X Y : Type*} :
    (Sum A X → F2) →ₗ[F2] (Sum A (Sum X Y) → F2) where
  toFun v
    | .inl a => v (.inl a)
    | .inr (.inl x) => v (.inr x)
    | .inr (.inr _) => 0
  map_add' v w := by
    funext i
    cases i with
    | inl a => rfl
    | inr z =>
        cases z <;> simp
  map_smul' c v := by
    funext i
    cases i with
    | inl a => rfl
    | inr z =>
        cases z <;> simp

/-- Extend a coordinate vector on A ⊕ Y by zero on the X-block. -/
def sumAmalgamLinearRight
    {A X Y : Type*} :
    (Sum A Y → F2) →ₗ[F2] (Sum A (Sum X Y) → F2) where
  toFun v
    | .inl a => v (.inl a)
    | .inr (.inl _) => 0
    | .inr (.inr y) => v (.inr y)
  map_add' v w := by
    funext i
    cases i with
    | inl a => rfl
    | inr z =>
        cases z <;> simp
  map_smul' c v := by
    funext i
    cases i with
    | inl a => rfl
    | inr z =>
        cases z <;> simp

/-- Common-coordinate inclusion A → A ⊕ X. -/
def sumCommonLinear
    {A X : Type*} :
    (A → F2) →ₗ[F2] (Sum A X → F2) where
  toFun v
    | .inl a => v a
    | .inr _ => 0
  map_add' v w := by
    funext i
    cases i <;> simp
  map_smul' c v := by
    funext i
    cases i <;> simp

theorem sumAmalgamLinearLeft_injective
    {A X Y : Type*} :
    Function.Injective
      (sumAmalgamLinearLeft :
        (Sum A X → F2) →ₗ[F2] (Sum A (Sum X Y) → F2)) := by
  intro v w h
  funext i
  cases i with
  | inl a =>
      exact congrFun h (.inl a)
  | inr x =>
      exact congrFun h (.inr (.inl x))

theorem sumAmalgamLinearRight_injective
    {A X Y : Type*} :
    Function.Injective
      (sumAmalgamLinearRight :
        (Sum A Y → F2) →ₗ[F2] (Sum A (Sum X Y) → F2)) := by
  intro v w h
  funext i
  cases i with
  | inl a =>
      exact congrFun h (.inl a)
  | inr y =>
      exact congrFun h (.inr (.inr y))

/-- The two coordinate embeddings meet exactly in the common A-summand. -/
theorem sumAmalgam_eq_iff_common
    {A X Y : Type*}
    (v : Sum A X → F2)
    (w : Sum A Y → F2) :
    sumAmalgamLinearLeft v = sumAmalgamLinearRight w ↔
      ∃ a : A → F2,
        v = sumCommonLinear a ∧
        w = sumCommonLinear a := by
  constructor
  · intro h
    let a : A → F2 := fun i => v (.inl i)
    refine ⟨a, ?_, ?_⟩
    · funext i
      cases i with
      | inl i =>
          rfl
      | inr x =>
          have hx := congrFun h (.inr (.inl x))
          simpa [sumAmalgamLinearLeft, sumAmalgamLinearRight,
            sumCommonLinear] using hx
    · funext i
      cases i with
      | inl i =>
          have hi := congrFun h (.inl i)
          simpa [a, sumAmalgamLinearLeft, sumAmalgamLinearRight,
            sumCommonLinear] using hi.symm
      | inr y =>
          have hy := congrFun h (.inr (.inr y))
          simpa [sumAmalgamLinearLeft, sumAmalgamLinearRight,
            sumCommonLinear] using hy.symm
  · rintro ⟨a, rfl, rfl⟩
    funext i
    cases i with
    | inl i =>
        rfl
    | inr z =>
        cases z <;> rfl

/-- Zero-cross block amalgam of two rectangular pairing matrices over a
common A_L × A_R block. -/
def bananaBlockAmalgam
    {LA RA UB VB UC VC : Type*}
    (B : Matrix (Sum LA UB) (Sum RA VB) F2)
    (C : Matrix (Sum LA UC) (Sum RA VC) F2) :
    Matrix
      (Sum LA (Sum UB UC))
      (Sum RA (Sum VB VC))
      F2
  | .inl a, .inl r => B (.inl a) (.inl r)
  | .inl a, .inr (.inl v) => B (.inl a) (.inr v)
  | .inr (.inl u), .inl r => B (.inr u) (.inl r)
  | .inr (.inl u), .inr (.inl v) => B (.inr u) (.inr v)
  | .inl a, .inr (.inr v) => C (.inl a) (.inr v)
  | .inr (.inr u), .inl r => C (.inr u) (.inl r)
  | .inr (.inr u), .inr (.inr v) => C (.inr u) (.inr v)
  | .inr (.inl _), .inr (.inr _) => 0
  | .inr (.inr _), .inr (.inl _) => 0

/-- Restriction of the amalgam to the B-coordinate blocks is B. -/
theorem bananaBlockAmalgam_left
    {LA RA UB VB UC VC : Type*}
    (B : Matrix (Sum LA UB) (Sum RA VB) F2)
    (C : Matrix (Sum LA UC) (Sum RA VC) F2) :
    (bananaBlockAmalgam B C).submatrix
      (sumAmalgamIndexLeft : Sum LA UB → Sum LA (Sum UB UC))
      (sumAmalgamIndexLeft : Sum RA VB → Sum RA (Sum VB VC)) = B := by
  ext i j
  cases i <;> cases j <;> rfl

/-- Restriction to C is C when the two old pairings agree on the common
L_A × R_A block. -/
theorem bananaBlockAmalgam_right
    {LA RA UB VB UC VC : Type*}
    (B : Matrix (Sum LA UB) (Sum RA VB) F2)
    (C : Matrix (Sum LA UC) (Sum RA VC) F2)
    (hcommon :
      ∀ a r,
        B (.inl a) (.inl r) =
          C (.inl a) (.inl r)) :
    (bananaBlockAmalgam B C).submatrix
      (sumAmalgamIndexRight : Sum LA UC → Sum LA (Sum UB UC))
      (sumAmalgamIndexRight : Sum RA VC → Sum RA (Sum VB VC)) = C := by
  ext i j
  cases i with
  | inl a =>
      cases j with
      | inl r =>
          exact hcommon a r
      | inr v =>
          rfl
  | inr u =>
      cases j <;> rfl

end SuccessorTree.NonPrecompact

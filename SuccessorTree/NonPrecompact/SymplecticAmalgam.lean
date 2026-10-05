import SuccessorTree.NonPrecompact.SymplecticSlice

/-!
# Standard block amalgams of binary alternating forms

This file formalises the finite matrix construction used in the circulation
proof that finite symplectic spaces form an amalgamation class.

After choosing complements, two extensions of a common space have coordinate
types A ⊕ X and A ⊕ Y.  Their amalgam has coordinate type A ⊕ (X ⊕ Y),
retains both old forms, and gives the new X--Y cross-pairings value zero.
-/

namespace SuccessorTree.NonPrecompact

/-- Inclusion of the left extension A ⊕ X into A ⊕ (X ⊕ Y). -/
def symplecticAmalgamLeft
    {A X Y : Type*} :
    Sum A X → Sum A (Sum X Y)
  | .inl a => .inl a
  | .inr x => .inr (.inl x)

/-- Inclusion of the right extension A ⊕ Y into A ⊕ (X ⊕ Y). -/
def symplecticAmalgamRight
    {A X Y : Type*} :
    Sum A Y → Sum A (Sum X Y)
  | .inl a => .inl a
  | .inr y => .inr (.inr y)

theorem symplecticAmalgamLeft_injective
    {A X Y : Type*} :
    Function.Injective
      (symplecticAmalgamLeft : Sum A X → Sum A (Sum X Y)) := by
  intro i j h
  cases i <;> cases j <;> simp [symplecticAmalgamLeft] at h ⊢
  · exact h
  · exact h

theorem symplecticAmalgamRight_injective
    {A X Y : Type*} :
    Function.Injective
      (symplecticAmalgamRight : Sum A Y → Sum A (Sum X Y)) := by
  intro i j h
  cases i <;> cases j <;> simp [symplecticAmalgamRight] at h ⊢
  · exact h
  · exact h

/-- Zero-cross block amalgam of two matrices over a common A-block.

On the common A×A block we use B; recovery of C assumes agreement there.
-/
def symplecticBlockAmalgam
    {A X Y : Type*}
    (B : Matrix (Sum A X) (Sum A X) F2)
    (C : Matrix (Sum A Y) (Sum A Y) F2) :
    Matrix (Sum A (Sum X Y)) (Sum A (Sum X Y)) F2
  | .inl a, .inl a' => B (.inl a) (.inl a')
  | .inl a, .inr (.inl x) => B (.inl a) (.inr x)
  | .inr (.inl x), .inl a => B (.inr x) (.inl a)
  | .inr (.inl x), .inr (.inl x') => B (.inr x) (.inr x')
  | .inl a, .inr (.inr y) => C (.inl a) (.inr y)
  | .inr (.inr y), .inl a => C (.inr y) (.inl a)
  | .inr (.inr y), .inr (.inr y') => C (.inr y) (.inr y')
  | .inr (.inl _), .inr (.inr _) => 0
  | .inr (.inr _), .inr (.inl _) => 0

/-- The left extension is recovered exactly by restriction. -/
theorem symplecticBlockAmalgam_left
    {A X Y : Type*}
    (B : Matrix (Sum A X) (Sum A X) F2)
    (C : Matrix (Sum A Y) (Sum A Y) F2) :
    (symplecticBlockAmalgam B C).submatrix
      (symplecticAmalgamLeft : Sum A X → Sum A (Sum X Y))
      (symplecticAmalgamLeft : Sum A X → Sum A (Sum X Y)) = B := by
  ext i j
  cases i <;> cases j <;> rfl

/-- The right extension is recovered when the two old forms agree on the
common A-block. -/
theorem symplecticBlockAmalgam_right
    {A X Y : Type*}
    (B : Matrix (Sum A X) (Sum A X) F2)
    (C : Matrix (Sum A Y) (Sum A Y) F2)
    (hcommon :
      ∀ a a',
        B (.inl a) (.inl a') =
          C (.inl a) (.inl a')) :
    (symplecticBlockAmalgam B C).submatrix
      (symplecticAmalgamRight : Sum A Y → Sum A (Sum X Y))
      (symplecticAmalgamRight : Sum A Y → Sum A (Sum X Y)) = C := by
  ext i j
  cases i with
  | inl a =>
      cases j with
      | inl a' =>
          exact hcommon a a'
      | inr y =>
          rfl
  | inr y =>
      cases j <;> rfl

/-- Zero diagonal is preserved by the block amalgam. -/
theorem symplecticBlockAmalgam_diag_zero
    {A X Y : Type*}
    (B : Matrix (Sum A X) (Sum A X) F2)
    (C : Matrix (Sum A Y) (Sum A Y) F2)
    (hB : ∀ i, B i i = 0)
    (hC : ∀ i, C i i = 0) :
    ∀ i, symplecticBlockAmalgam B C i i = 0 := by
  intro i
  cases i with
  | inl a =>
      exact hB (.inl a)
  | inr z =>
      cases z with
      | inl x =>
          exact hB (.inr x)
      | inr y =>
          exact hC (.inr y)

/-- Symmetry is preserved by the zero-cross block amalgam. -/
theorem symplecticBlockAmalgam_symmetric
    {A X Y : Type*}
    (B : Matrix (Sum A X) (Sum A X) F2)
    (C : Matrix (Sum A Y) (Sum A Y) F2)
    (hB : ∀ i j, B i j = B j i)
    (hC : ∀ i j, C i j = C j i) :
    ∀ i j,
      symplecticBlockAmalgam B C i j =
        symplecticBlockAmalgam B C j i := by
  intro i j
  cases i with
  | inl a =>
      cases j with
      | inl a' =>
          exact hB (.inl a) (.inl a')
      | inr z =>
          cases z with
          | inl x =>
              exact hB (.inl a) (.inr x)
          | inr y =>
              exact hC (.inl a) (.inr y)
  | inr z =>
      cases z with
      | inl x =>
          cases j with
          | inl a =>
              exact hB (.inr x) (.inl a)
          | inr z' =>
              cases z' with
              | inl x' =>
                  exact hB (.inr x) (.inr x')
              | inr y =>
                  rfl
      | inr y =>
          cases j with
          | inl a =>
              exact hC (.inr y) (.inl a)
          | inr z' =>
              cases z' with
              | inl x =>
                  rfl
              | inr y' =>
                  exact hC (.inr y) (.inr y')

end SuccessorTree.NonPrecompact

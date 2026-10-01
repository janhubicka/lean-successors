import Mathlib

namespace SuccessorTree.BANANA

open Matrix

/-- A finite bilinear pairing in coordinates.  The row index is the left sort
and the column index is the right sort. -/
abbrev PairingMatrix (l r : Type*) (R : Type*) := Matrix l r R

/-- A rectangular matrix is perfect when it has a two-sided matrix inverse.
The two index types need not literally coincide; this is the convenient
coordinate formulation for a perfect pairing between two spaces of the same
finite dimension. -/
def IsPerfect {R l r : Type*} [Semiring R] [Fintype l] [Fintype r]
    [DecidableEq l] [DecidableEq r] (A : Matrix l r R) : Prop :=
  ∃ B : Matrix r l R, A * B = 1 ∧ B * A = 1

/-- The standard perfect completion of a matrix `A`.

If `A` represents `β : L × R → 𝔽`, this is the matrix of
`β̂((x, α), (y, φ)) = β(x,y) + α(y) + φ(x)` after choosing coordinate
identifications of the two dual spaces. -/
def perfectCompletion {R l r : Type*} [Zero R] [One R]
    [DecidableEq l] [DecidableEq r]
    (A : Matrix l r R) : Matrix (l ⊕ r) (r ⊕ l) R :=
  Matrix.fromBlocks A 1 1 0

/-- Explicit inverse of `perfectCompletion`. -/
def perfectCompletionInv {R l r : Type*} [Ring R]
    [DecidableEq l] [DecidableEq r]
    (A : Matrix l r R) : Matrix (r ⊕ l) (l ⊕ r) R :=
  Matrix.fromBlocks 0 1 1 (-A)

@[simp] theorem perfectCompletion_apply₁₁ {R l r : Type*}
    [Zero R] [One R] [DecidableEq l] [DecidableEq r]
    (A : Matrix l r R) (i : l) (j : r) :
    perfectCompletion A (Sum.inl i) (Sum.inl j) = A i j := by
  rfl

@[simp] theorem perfectCompletion_apply₁₂ {R l r : Type*}
    [Zero R] [One R] [DecidableEq l] [DecidableEq r]
    (A : Matrix l r R) (i : l) (j : l) :
    perfectCompletion A (Sum.inl i) (Sum.inr j) = (1 : Matrix l l R) i j := by
  rfl

@[simp] theorem perfectCompletion_apply₂₁ {R l r : Type*}
    [Zero R] [One R] [DecidableEq l] [DecidableEq r]
    (A : Matrix l r R) (i : r) (j : r) :
    perfectCompletion A (Sum.inr i) (Sum.inl j) = (1 : Matrix r r R) i j := by
  rfl

@[simp] theorem perfectCompletion_apply₂₂ {R l r : Type*}
    [Zero R] [One R] [DecidableEq l] [DecidableEq r]
    (A : Matrix l r R) (i : r) (j : l) :
    perfectCompletion A (Sum.inr i) (Sum.inr j) = 0 := by
  rfl

/-- The displayed inverse is a right inverse. -/
theorem perfectCompletion_mul_inv {R l r : Type*} [Ring R]
    [Fintype l] [Fintype r] [DecidableEq l] [DecidableEq r]
    (A : Matrix l r R) :
    perfectCompletion A * perfectCompletionInv A = 1 := by
  simp [perfectCompletion, perfectCompletionInv, Matrix.fromBlocks_multiply]

/-- The displayed inverse is also a left inverse. -/
theorem perfectCompletion_inv_mul {R l r : Type*} [Ring R]
    [Fintype l] [Fintype r] [DecidableEq l] [DecidableEq r]
    (A : Matrix l r R) :
    perfectCompletionInv A * perfectCompletion A = 1 := by
  simp [perfectCompletion, perfectCompletionInv, Matrix.fromBlocks_multiply]

/-- Every finite bilinear pairing has the perfect completion used in the
BANANA manuscript. -/
theorem perfectCompletion_isPerfect {R l r : Type*} [Ring R]
    [Fintype l] [Fintype r] [DecidableEq l] [DecidableEq r]
    (A : Matrix l r R) :
    IsPerfect (perfectCompletion A) := by
  exact ⟨perfectCompletionInv A, perfectCompletion_mul_inv A,
    perfectCompletion_inv_mul A⟩

/-- Both sides of the completion have `|l|+|r|` coordinates. -/
theorem card_perfectCompletion_left_eq_right {l r : Type*}
    [Fintype l] [Fintype r] :
    Fintype.card (l ⊕ r) = Fintype.card (r ⊕ l) := by
  simp [Nat.add_comm]

/-- Coordinate inclusion of the old left space into the completion. -/
def completionLeftInclusion {R l r : Type*} [Zero R] [One R]
    [DecidableEq l] : Matrix (l ⊕ r) l R :=
  Matrix.fromRows 1 0

/-- Coordinate inclusion of the old right space into the completion. -/
def completionRightInclusion {R l r : Type*} [Zero R] [One R]
    [DecidableEq r] : Matrix (r ⊕ l) r R :=
  Matrix.fromRows 1 0

@[simp] theorem completionLeftInclusion_mulVec {R l r : Type*}
    [Semiring R] [Fintype l] [DecidableEq l]
    (x : l → R) :
    (completionLeftInclusion (R := R) (l := l) (r := r)) *ᵥ x =
      Sum.elim x 0 := by
  simp [completionLeftInclusion, Matrix.fromRows_mulVec]

@[simp] theorem completionRightInclusion_mulVec {R l r : Type*}
    [Semiring R] [Fintype r] [DecidableEq r]
    (x : r → R) :
    (completionRightInclusion (R := R) (l := l) (r := r)) *ᵥ x =
      Sum.elim x 0 := by
  simp [completionRightInclusion, Matrix.fromRows_mulVec]

/-- The canonical left coordinate inclusion is injective. -/
theorem completionLeftInclusion_injective {R l r : Type*}
    [Semiring R] [Fintype l] [DecidableEq l] :
    Function.Injective
      (fun x : l → R =>
        (completionLeftInclusion (R := R) (l := l) (r := r)) *ᵥ x) := by
  intro x y h
  funext i
  have hi := congrFun h (Sum.inl i)
  simpa using hi

/-- The canonical right coordinate inclusion is injective. -/
theorem completionRightInclusion_injective {R l r : Type*}
    [Semiring R] [Fintype r] [DecidableEq r] :
    Function.Injective
      (fun x : r → R =>
        (completionRightInclusion (R := R) (l := l) (r := r)) *ᵥ x) := by
  intro x y h
  funext i
  have hi := congrFun h (Sum.inl i)
  simpa using hi


/-- For the BANANA field `F₂`, a completed pairing with original coordinate
sets `l,r` has `2^(|l|+|r|+1)` carrier elements across its two sorts. -/
theorem card_f2_perfectCompletion_carrier {l r : Type*}
    [Fintype l] [Fintype r] :
    Fintype.card
      (((l ⊕ r → ZMod 2) ⊕ (r ⊕ l → ZMod 2))) =
      2 ^ (Fintype.card l + Fintype.card r + 1) := by
  simp [pow_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, two_mul]


end SuccessorTree.BANANA

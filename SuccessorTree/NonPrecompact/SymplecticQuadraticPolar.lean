import SuccessorTree.NonPrecompact.QuadraticGauss

/-!
# Quadratic refinements of alternating binary matrices

This file formalises the two finite algebra facts used in the circulation
proof of the symplectic persistent colouring theorem.

* The strict upper-triangular part of an alternating matrix defines a
  quadratic refinement whose polar form is the original bilinear form.
* Translating a quadratic map by a fixed vector changes only affine terms;
  the affine polar form of the translate is the restriction of the original
  polar form.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators Matrix
open LinearMap

/-- Strict upper-triangular part of a square matrix. -/
def strictUpper
    {n : Type*} [LinearOrder n] [DecidableEq n]
    (M : Matrix n n F2) : Matrix n n F2 :=
  fun i j => if i < j then M i j else 0

/-- For a symmetric zero-diagonal binary matrix, the strict upper triangle
plus its transpose is the original matrix. -/
theorem strictUpper_add_transpose_eq
    {n : Type*} [LinearOrder n] [DecidableEq n]
    (M : Matrix n n F2)
    (hdiag : ∀ i, M i i = 0)
    (hsymm : ∀ i j, M i j = M j i) :
    strictUpper M + (strictUpper M)ᵀ = M := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · have hji : ¬ j < i := not_lt_of_ge hij.le
    simp [strictUpper, hij, hji]
  · subst j
    simp [strictUpper, hdiag i]
  · have hij' : ¬ i < j := not_lt_of_ge hij.le
    have hji : j < i := hij
    simp [strictUpper, hij', hji, hsymm i j]

/-- The standard quadratic refinement attached to the strict upper triangle
of a binary matrix. -/
def upperQuadratic
    {n : Type*} [Fintype n] [LinearOrder n] [DecidableEq n]
    (M : Matrix n n F2) :
    QuadraticForm F2 (n → F2) :=
  (Matrix.toBilin' (strictUpper M)).toQuadraticMap

/-- The polar bilinear form of the upper-triangular quadratic refinement is
the original bilinear form, provided the matrix is symmetric with zero
diagonal. -/
theorem polarBilin_upperQuadratic
    {n : Type*} [Fintype n] [LinearOrder n] [DecidableEq n]
    (M : Matrix n n F2)
    (hdiag : ∀ i, M i i = 0)
    (hsymm : ∀ i j, M i j = M j i) :
    QuadraticMap.polarBilin (upperQuadratic M) =
      Matrix.toBilin' M := by
  rw [upperQuadratic, LinearMap.BilinMap.polarBilin_toQuadraticMap]
  apply LinearMap.BilinForm.ext_basis (Pi.basisFun F2 n)
  intro i j
  simp only [Pi.basisFun_apply, LinearMap.add_apply, LinearMap.flip_apply,
    Matrix.toBilin'_single]
  have hmat := congrArg (fun X : Matrix n n F2 => X i j)
    (strictUpper_add_transpose_eq M hdiag hsymm)
  simpa using hmat

/-- The manuscript's affine polar expression in characteristic two. -/
def affinePolar
    {V : Type*} [AddCommGroup V]
    (f : V → F2) (x y : V) : F2 :=
  f (x + y) + f x + f y + f 0

/-- Translating a quadratic map and precomposing by a linear map preserves
the polar form.  This is the affine-translate step used on w + W. -/
theorem affinePolar_translate_quadratic
    {V W : Type*}
    [AddCommGroup V] [Module F2 V]
    [AddCommGroup W] [Module F2 W]
    (Q : QuadraticForm F2 V)
    (w : V)
    (L : W →ₗ[F2] V)
    (x y : W) :
    affinePolar (fun u => Q (w + L u)) x y =
      QuadraticMap.polar Q (L x) (L y) := by
  simp only [affinePolar, LinearMap.map_add, LinearMap.map_zero]
  rw [show w + (L x + L y) = (w + L x) + L y by abel]
  rw [QuadraticMap.map_add (fun v => Q v) (w + L x) (L y)]
  rw [QuadraticMap.map_add (fun v => Q v) w (L y)]
  rw [QuadraticMap.polar_add_left (Q := Q)]
  simp only [QuadraticMap.polar, sub_eq_add_neg]
  ring_nf
  simp

end SuccessorTree.NonPrecompact

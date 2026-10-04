import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import SuccessorTree.NonPrecompact.BilinearResidue

/-!
# Character-sum input for the symplectic quadratic residue argument

The quadratic residue proof in the BANANA circulation manuscript uses the
elementary cancellation fact that a nonzero F₂-linear functional has equally
many zero and one values.  In character language, its {+1,-1}-sum vanishes.

This file isolates that fact as the first reusable layer of the quadratic
Gauss-sum formalisation.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- The real/integer sign character of F₂, written with integer values. -/
def f2Sign (a : F2) : ℤ :=
  if a = 0 then 1 else -1

@[simp] theorem f2Sign_zero : f2Sign 0 = 1 := by
  simp [f2Sign]

@[simp] theorem f2Sign_one : f2Sign 1 = -1 := by
  norm_num [f2Sign]

theorem f2Sign_add (a b : F2) :
    f2Sign (a + b) = f2Sign a * f2Sign b := by
  rcases f2_eq_zero_or_one a with rfl | rfl <;>
    rcases f2_eq_zero_or_one b with rfl | rfl <;>
      simp [f2Sign, CharTwo.add_self_eq_zero]

/-- The nontrivial additive character F₂ → {+1,-1} ⊂ ℤ. -/
def f2SignChar : AddChar F2 ℤ where
  toFun := f2Sign
  map_zero_eq_one' := f2Sign_zero
  map_add_eq_mul' := f2Sign_add

@[simp] theorem f2SignChar_apply (a : F2) :
    f2SignChar a = f2Sign a := rfl

theorem exists_eq_one_of_linearMap_ne_zero
    {V : Type*} [AddCommGroup V] [Module F2 V]
    (L : V →ₗ[F2] F2) (hL : L ≠ 0) :
    ∃ x : V, L x = 1 := by
  by_contra h
  push Not at h
  apply hL
  apply LinearMap.ext
  intro x
  rcases f2_eq_zero_or_one (L x) with hx | hx
  · simpa using hx
  · exact (h x hx).elim

/-- The ±1 character sum of a nonzero F₂-linear functional vanishes. -/
theorem sum_f2Sign_linear_eq_zero
    {V : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]
    (L : V →ₗ[F2] F2) (hL : L ≠ 0) :
    (∑ x : V, f2Sign (L x)) = 0 := by
  let ψ : AddChar V ℤ :=
    f2SignChar.compAddMonoidHom L.toAddMonoidHom
  have hψ : ψ ≠ 1 := by
    obtain ⟨x, hx⟩ := exists_eq_one_of_linearMap_ne_zero L hL
    intro h
    have hval := DFunLike.congr_fun h x
    have hneg : (-1 : ℤ) = 1 := by
      simpa [ψ, hx] using hval
    norm_num at hneg
  simpa [ψ] using (AddChar.sum_eq_zero_of_ne_one hψ)


/-- For a bilinear form with injective right adjoint, the sign-character
sum in the first variable is zero away from the zero second variable and
is the full cardinality at zero. -/
theorem sum_f2Sign_bilinear_fixed
    {V : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]
    [DecidableEq V]
    (b : V →ₗ[F2] V →ₗ[F2] F2)
    (hnondeg : Function.Injective b.flip)
    (w : V) :
    (∑ x : V, f2Sign (b x w)) =
      if w = 0 then (Fintype.card V : ℤ) else 0 := by
  by_cases hw : w = 0
  · subst w
    simp [f2Sign]
  · rw [if_neg hw]
    have hlin : b.flip w ≠ 0 := by
      intro hzero
      apply hw
      apply hnondeg
      simpa using hzero
    simpa [LinearMap.flip_apply] using
      sum_f2Sign_linear_eq_zero (b.flip w) hlin


/-- The integer Gauss sum attached to an F₂-valued function. -/
def quadraticGaussSum
    {V : Type*} [Fintype V]
    (p : V → F2) : ℤ :=
  ∑ z : V, f2Sign (p z)

/-- The polar identity rewrites the product of two quadratic signs as a
constant sign times the sign of the polar bilinear form. -/
theorem f2Sign_quadratic_pair
    {V : Type*} [AddCommGroup V] [Module F2 V]
    (p : V → F2)
    (b : V →ₗ[F2] V →ₗ[F2] F2)
    (hpolar :
      ∀ z w,
        p (z + w) + p z + p w + p 0 = b z w)
    (z w : V) :
    f2Sign (p z) * f2Sign (p (z + w)) =
      f2Sign (p w + p 0) * f2Sign (b z w) := by
  rw [← f2Sign_add, ← f2Sign_add]
  congr 1
  rw [← hpolar z w]
  symm
  calc
    p w + p 0 + (p (z + w) + p z + p w + p 0) =
        (p z + p (z + w)) + (p w + p w) + (p 0 + p 0) := by
      abel
    _ = p z + p (z + w) := by
      rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero]
      simp

/-- Translation of the second variable in the squared Gauss sum. -/
theorem sum_f2Sign_translate_second
    {V : Type*} [AddCommGroup V] [Fintype V]
    (p : V → F2) (z : V) :
    (∑ y : V, f2Sign (p z) * f2Sign (p y)) =
      ∑ w : V, f2Sign (p z) * f2Sign (p (z + w)) := by
  refine Fintype.sum_equiv (Equiv.subRight z) _ _ ?_
  intro y
  simp only [Equiv.subRight_apply]
  congr 2
  abel

/-- For a nondegenerate polar form, the square of the quadratic sign Gauss
sum is the cardinality of the underlying finite F₂-vector space. -/
theorem quadraticGaussSum_sq_eq_card
    {V : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]
    [DecidableEq V]
    (p : V → F2)
    (b : V →ₗ[F2] V →ₗ[F2] F2)
    (hpolar :
      ∀ z w,
        p (z + w) + p z + p w + p 0 = b z w)
    (hnondeg : Function.Injective b.flip) :
    quadraticGaussSum p ^ 2 = (Fintype.card V : ℤ) := by
  unfold quadraticGaussSum
  rw [pow_two, Fintype.sum_mul_sum]

  have hinner (w : V) :
      (∑ z : V,
        f2Sign (p z) * f2Sign (p (z + w))) =
        f2Sign (p w + p 0) *
          ∑ z : V, f2Sign (b z w) := by
    calc
      (∑ z : V,
          f2Sign (p z) * f2Sign (p (z + w))) =
          ∑ z : V,
            f2Sign (p w + p 0) * f2Sign (b z w) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact f2Sign_quadratic_pair p b hpolar z w
      _ = f2Sign (p w + p 0) *
          ∑ z : V, f2Sign (b z w) := by
        rw [Finset.mul_sum]

  calc
    (∑ z : V, ∑ y : V,
        f2Sign (p z) * f2Sign (p y)) =
        ∑ z : V, ∑ w : V,
          f2Sign (p z) * f2Sign (p (z + w)) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact sum_f2Sign_translate_second p z
    _ = ∑ w : V, ∑ z : V,
          f2Sign (p z) * f2Sign (p (z + w)) := by
      rw [Finset.sum_comm]
    _ = ∑ w : V,
          f2Sign (p w + p 0) *
            (if w = 0 then (Fintype.card V : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [hinner w, sum_f2Sign_bilinear_fixed b hnondeg w]
    _ = (Fintype.card V : ℤ) := by
      have hp0 : p 0 + p 0 = 0 :=
        CharTwo.add_self_eq_zero (p 0)
      simp [hp0, f2Sign]

end SuccessorTree.NonPrecompact

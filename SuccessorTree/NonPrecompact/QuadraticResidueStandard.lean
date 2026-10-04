import SuccessorTree.NonPrecompact.QuadraticResidueGenerating
import SuccessorTree.NonPrecompact.QuadraticResidueCollapse
import SuccessorTree.NonPrecompact.QuadraticCoordinateGlue
import SuccessorTree.NonPrecompact.QuadraticBinomial
import SuccessorTree.NonPrecompact.QuadraticMiddleCongruence
import SuccessorTree.NonPrecompact.QuadraticArithmetic
import SuccessorTree.NonPrecompact.QuadraticCongruence

/-!
# Standard-coordinate quadratic residue theorem

This file assembles the independently checked ingredients of the
symplectic quadratic-residue argument.  The affine functions are represented
by matrices and constant terms, and the quadratic weight is the diagonal
specialisation of the bilinear weight.

The theorem below is the standard-coordinate form of the circulation
manuscript's quadratic residue lemma.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators Matrix

/-- The natural-valued quadratic weight associated with two families of
affine F₂-functions. -/
noncomputable def quadraticAffineWeight
    {D n : ℕ}
    (A B : Matrix (Fin D) (Fin n) F2)
    (c e : Fin n → F2)
    (x : Fin D → F2) : ℕ :=
  bilinearWeight A B c e x x

/-- Standard-coordinate version of the quadratic residue lemma.

Let q=2^s and d=q-1.  On a 2d-dimensional binary vector space, let Q be a
sum of products of pairs of affine linear functions.  If the mod-two
reduction of Q has nondegenerate polar form, then every residue modulo q is
attained an odd number of times. -/
theorem quadraticAffineWeight_residueFibres_odd
    (s d n : ℕ)
    (hd : d = 2 ^ s - 1)
    (A B : Matrix (Fin (2 * d)) (Fin n) F2)
    (c e : Fin n → F2)
    (b :
      (Fin (2 * d) → F2) →ₗ[F2]
        (Fin (2 * d) → F2) →ₗ[F2] F2)
    (hpolar :
      ∀ z w,
        (quadraticAffineWeight A B c e (z + w) : F2) +
          (quadraticAffineWeight A B c e z : F2) +
          (quadraticAffineWeight A B c e w : F2) +
          (quadraticAffineWeight A B c e 0 : F2) =
        b z w)
    (hnondeg : Function.Injective b.flip)
    (r : ZMod (2 ^ s)) :
    Odd (((Finset.univ :
      Finset (Fin (2 * d) → F2)).filter
        (fun x =>
          (quadraticAffineWeight A B c e x : ZMod (2 ^ s)) = r)).card) := by
  let Q : (Fin (2 * d) → F2) → ℕ :=
    fun x => quadraticAffineWeight A B c e x
  let p : (Fin (2 * d) → F2) → F2 :=
    fun x => (Q x : F2)
  let M : ℕ → ℕ :=
    fun k => ∑ x : Fin (2 * d) → F2, (Q x).choose k
  let N : ℕ := max n d
  let T : ℤ :=
    ∑ x : Fin (2 * d) → F2, (-1 : ℤ) ^ Q x

  have hQ : ∀ x, Q x ≤ N := by
    intro x
    have hx :
        quadraticAffineWeight A B c e x ≤ n := by
      exact bilinearWeight_le_card A B c e x x
    exact hx.trans (Nat.le_max_left n d)

  have hdN : d ≤ N := by
    exact Nat.le_max_right n d

  have hmomentEq (k : ℕ) :
      quadraticSubsetMoment A B c e k = M k := by
    simpa [M, Q, quadraticAffineWeight] using
      quadraticSubsetMoment_eq_sum_choose_bilinearWeight_self
        A B c e k

  have hdivNat (k : ℕ) :
      2 ^ (2 * d - 2 * k) ∣ M k := by
    have h :=
      pow_two_sub_two_mul_dvd_quadraticSubsetMoment
        A B c e k
    rw [hmomentEq k] at h
    exact h

  have hlowEven :
      ∀ k, k < d → Even (M k) := by
    intro k hk
    exact even_of_quadratic_moment_divisibility
      d k (M k) hk (hdivNat k)

  have hgauss :
      quadraticGaussSum p ^ 2 =
        (Fintype.card (Fin (2 * d) → F2) : ℤ) := by
    apply quadraticGaussSum_sq_eq_card p b
    · simpa [p, Q] using hpolar
    · exact hnondeg

  have hgaussT : quadraticGaussSum p = T := by
    simpa [p, Q, T] using
      quadraticGaussSum_natWeight Q

  have hTsq :
      T ^ 2 = (2 : ℤ) ^ (2 * d) := by
    calc
      T ^ 2 = quadraticGaussSum p ^ 2 := by
        rw [hgaussT]
      _ = (Fintype.card (Fin (2 * d) → F2) : ℤ) := hgauss
      _ = (2 : ℤ) ^ (2 * d) := by
        norm_cast
        exact card_fin_fun_f2 (2 * d)

  have hTsign :
      T = (2 : ℤ) ^ d ∨ T = -((2 : ℤ) ^ d) :=
    int_eq_pow_two_or_neg_of_sq_eq T d hTsq

  have hbin :
      T =
        ∑ k ∈ Finset.range (N + 1),
          (-2 : ℤ) ^ k * (M k : ℤ) := by
    simpa [T, M] using
      sum_neg_one_pow_eq_sum_binomial_moments Q N hQ

  have hlowInt :
      ∀ k, k < d →
        (2 : ℤ) ^ (2 * d - 2 * k) ∣ (M k : ℤ) := by
    intro k hk
    exact int_pow_two_dvd_natCast_of_nat_dvd
      (2 * d - 2 * k) (M k) (hdivNat k)

  have hsumMod :
      (∑ k ∈ Finset.range (N + 1),
          (-2 : ℤ) ^ k * (M k : ℤ)) ≡
        (-2 : ℤ) ^ d * (M d : ℤ)
          [ZMOD (2 : ℤ) ^ (d + 1)] :=
    sum_neg_two_pow_mul_modEq_middle
      (fun k => (M k : ℤ)) d N hdN hlowInt

  have hmod :
      T ≡ (-2 : ℤ) ^ d * (M d : ℤ)
        [ZMOD (2 : ℤ) ^ (d + 1)] := by
    rw [hbin]
    exact hsumMod

  have hmid : Odd (M d) :=
    odd_of_gauss_congruence T (M d) d hTsign hmod

  have hmid' : Odd (M (2 ^ s - 1)) := by
    simpa [hd] using hmid

  have hlowEven' :
      ∀ k, k < 2 ^ s - 1 → Even (M k) := by
    intro k hk
    apply hlowEven k
    simpa [hd] using hk

  have hN' : 2 ^ s - 1 ≤ N := by
    simpa [hd] using hdN

  have hgenExpand :
      residueWeightGenerating (2 ^ s) Q =
        ∑ k ∈ Finset.range (N + 1),
          residueCoeff (2 ^ s) (M k : F2) *
            residueT (2 ^ s) ^ k := by
    simpa [M] using
      residueWeightGenerating_eq_sum_binomialMoments
        (2 ^ s) Q N hQ

  have hcollapse :
      (∑ k ∈ Finset.range (N + 1),
        residueCoeff (2 ^ s) (M k : F2) *
          residueT (2 ^ s) ^ k) =
        residueT (2 ^ s) ^ (2 ^ s - 1) :=
    residueMomentSum_eq_middle_power
      s N M hmid' hlowEven' hN'

  have hgen :
      residueWeightGenerating (2 ^ s) Q =
        residueT (2 ^ s) ^ (2 ^ s - 1) :=
    hgenExpand.trans hcollapse

  have hodd :=
    residueFibres_odd_of_generating_eq_middlePower
      s Q hgen r
  simpa [Q, quadraticAffineWeight] using hodd

end SuccessorTree.NonPrecompact

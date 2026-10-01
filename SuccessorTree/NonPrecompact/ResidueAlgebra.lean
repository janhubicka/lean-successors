import SuccessorTree.NonPrecompact.MatrixAffineParity
import SuccessorTree.NonPrecompact.SubsetSums

/-!
# The residue group algebra for BANANA

For a power of two `q`, we work in the group algebra
`F₂[Z/qZ]`.  The basis element at `1` plays the role of `z` in the
manuscript, and `t = 1 + z`.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

abbrev ResidueAlgebra (q : ℕ) := AddMonoidAlgebra F2 (ZMod q)

instance residueAlgebraCharP (q : ℕ) : CharP (ResidueAlgebra q) 2 := by
  have hinj : Function.Injective
      (AddMonoidAlgebra.singleZeroRingHom :
        F2 →+* ResidueAlgebra q) := by
    intro a b h
    have hc := congrArg (fun x : ResidueAlgebra q => x.coeff 0) h
    simpa using hc
  exact charP_of_injective_ringHom hinj 2

noncomputable def residueZ (q : ℕ) : ResidueAlgebra q :=
  AddMonoidAlgebra.single (1 : ZMod q) 1

noncomputable def residueT (q : ℕ) : ResidueAlgebra q :=
  1 + residueZ q

noncomputable def residueCoeff (q : ℕ) (a : F2) : ResidueAlgebra q :=
  AddMonoidAlgebra.single 0 a

noncomputable def residueFactor (q : ℕ) (a : F2) : ResidueAlgebra q :=
  1 + residueCoeff q a * residueT q

/-- A Boolean coefficient contributes either `1` or `z`:
`1 + a t = z^a`. -/
theorem residueFactor_eq_residueZ_pow_val
    (q : ℕ) (a : F2) :
    residueFactor q a = residueZ q ^ a.val := by
  by_cases ha : a = 0
  · subst a
    simp [residueFactor, residueCoeff]
  · have ha1 : a = 1 := by
      apply ZMod.val_injective
      have hpos : 0 < a.val := (ZMod.val_pos).2 ha
      have hlt : a.val < 2 := ZMod.val_lt a
      simp only [ZMod.val_one]
      omega
    subst a
    simp only [residueFactor, residueCoeff, ZMod.val_one, pow_one]
    change 1 + 1 * residueT q = residueZ q
    rw [one_mul, residueT, ← add_assoc,
      CharTwo.add_self_eq_zero, zero_add]

/-- Products of Boolean residue factors encode the ordinary sum of
their `0/1` values in the exponent. -/
theorem prod_residueFactor_eq_residueZ_pow_sum
    {q : ℕ} {ι : Type*} (s : Finset ι) (a : ι → F2) :
    (∏ i ∈ s, residueFactor q (a i)) =
      residueZ q ^ ∑ i ∈ s, (a i).val := by
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i hi
  exact residueFactor_eq_residueZ_pow_val q (a i)


/-- The coefficient embedding commutes with finite sums. -/
theorem residueCoeff_sum
    {q : ℕ} {ι : Type*} (s : Finset ι) (a : ι → F2) :
    residueCoeff q (∑ i ∈ s, a i) =
      ∑ i ∈ s, residueCoeff q (a i) := by
  change
    (AddMonoidAlgebra.singleZeroRingHom :
      F2 →+* ResidueAlgebra q) (∑ i ∈ s, a i) =
      ∑ i ∈ s,
        (AddMonoidAlgebra.singleZeroRingHom :
          F2 →+* ResidueAlgebra q) (a i)
  exact map_sum
    (AddMonoidAlgebra.singleZeroRingHom :
      F2 →+* ResidueAlgebra q) a s

/-- The coefficient embedding commutes with sums over a finite type. -/
theorem residueCoeff_fintype_sum
    {q : ℕ} {ι : Type*} [Fintype ι] (a : ι → F2) :
    residueCoeff q (∑ i, a i) =
      ∑ i, residueCoeff q (a i) := by
  simpa using residueCoeff_sum (q := q) Finset.univ a

/-- A product of coefficient-times-`t` factors separates into the
coefficient product and a power of `t`. -/
theorem prod_residueCoeff_mul_residueT
    {q : ℕ} {ι : Type*} (s : Finset ι) (a : ι → F2) :
    (∏ i ∈ s, residueCoeff q (a i) * residueT q) =
      residueCoeff q (∏ i ∈ s, a i) * residueT q ^ s.card := by
  rw [Finset.prod_mul_distrib]
  congr 1
  · change
      (∏ i ∈ s,
        (AddMonoidAlgebra.singleZeroRingHom :
          F2 →+* ResidueAlgebra q) (a i)) =
        (AddMonoidAlgebra.singleZeroRingHom :
          F2 →+* ResidueAlgebra q) (∏ i ∈ s, a i)
    rw [map_prod]
  · simp

/-- Expanding `∏ (1 + aᵢ t)` gives the expected powerset sum. -/
theorem prod_residueFactor_eq_sum_powerset
    {q : ℕ} {ι : Type*} (s : Finset ι) (a : ι → F2) :
    (∏ i ∈ s, residueFactor q (a i)) =
      ∑ u ∈ s.powerset,
        residueCoeff q (∏ i ∈ u, a i) * residueT q ^ u.card := by
  simp only [residueFactor]
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro u hu
  exact prod_residueCoeff_mul_residueT u a

@[simp] theorem residueZ_pow
    {q : ℕ} (n : ℕ) :
    residueZ q ^ n =
      AddMonoidAlgebra.single (n • (1 : ZMod q)) 1 := by
  simp [residueZ, AddMonoidAlgebra.single_pow]


/-- Multiplication by `t = 1 + z` adds two neighbouring coefficients. -/
theorem coeff_residueT_mul
    {q : ℕ} [NeZero q] (x : ResidueAlgebra q) (r : ZMod q) :
    (residueT q * x).coeff r =
      x.coeff r + x.coeff (r - 1) := by
  classical
  rw [residueT, add_mul, one_mul, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply]
  change x.coeff r +
      (AddMonoidAlgebra.single (1 : ZMod q) 1 * x).coeff r =
    x.coeff r + x.coeff (r - 1)
  rw [AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (r - 1)]
  · simp
  · intro m hm
    simpa [add_comm] using
      (eq_sub_iff_add_eq : m = r - 1 ↔ m + 1 = r).symm


/-- If `t x = 0`, adjacent coefficients of `x` agree. -/
theorem coeff_add_one_eq_of_residueT_mul_eq_zero
    {q : ℕ} [NeZero q] {x : ResidueAlgebra q}
    (hx : residueT q * x = 0) (r : ZMod q) :
    x.coeff (r + 1) = x.coeff r := by
  have h := congrArg (fun y : ResidueAlgebra q => y.coeff (r + 1)) hx
  rw [coeff_residueT_mul] at h
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h
  have hz :
      x.coeff (r + 1) + x.coeff r = 0 := by
    simpa using h
  exact CharTwo.add_eq_zero.mp hz

/-- If `t x = 0`, all coefficients of `x` are equal. -/
theorem coeff_eq_coeff_zero_of_residueT_mul_eq_zero
    {q : ℕ} [NeZero q] {x : ResidueAlgebra q}
    (hx : residueT q * x = 0) (r : ZMod q) :
    x.coeff r = x.coeff 0 := by
  obtain ⟨n, rfl⟩ :=
    exists_nsmul_eq_of_isUnit
      (a := (1 : ZMod q)) (y := r) isUnit_one
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        x.coeff ((n + 1) • (1 : ZMod q)) =
            x.coeff (n • (1 : ZMod q)) := by
              simpa [succ_nsmul] using
                coeff_add_one_eq_of_residueT_mul_eq_zero
                  (x := x) hx (n • (1 : ZMod q))
        _ = x.coeff 0 := ih

/-- For `q = 2^k`, the manuscript's element `t=1+z` satisfies
`t^q=0`. -/
theorem residueT_pow_two_pow_eq_zero (k : ℕ) :
    residueT (2 ^ k) ^ (2 ^ k) = 0 := by
  let q := 2 ^ k
  have hqpos : 0 < q := pow_pos (by decide) _
  letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective
      (AddMonoidAlgebra.singleZeroRingHom :
        F2 →+* ResidueAlgebra q) := by
    intro a b h
    have hc := congrArg (fun x : ResidueAlgebra q => x.coeff 0) h
    simpa using hc
  letI : CharP (ResidueAlgebra q) 2 :=
    charP_of_injective_ringHom hinj 2
  change (1 + residueZ q) ^ (2 ^ k) = 0
  rw [add_pow_char_pow]
  simp only [residueZ_pow, pow_zero]
  have hq : (2 ^ k) • (1 : ZMod q) = 0 := by
    simp [nsmul_eq_mul, q]
  rw [hq]
  simp only [one_pow]
  rw [AddMonoidAlgebra.one_def, ← AddMonoidAlgebra.single_add]
  have h11 : (1 + 1 : F2) = 0 := CharTwo.add_eq_zero.mpr rfl
  rw [h11, AddMonoidAlgebra.single_zero]


/-- The constant coefficient of `t^(q-1)` is one for `q = 2^k`.
No wrap-around can occur before exponent `q`. -/
theorem coeff_zero_residueT_pow_pred_two_pow (k : ℕ) :
    (residueT (2 ^ k) ^ (2 ^ k - 1)).coeff 0 = 1 := by
  let q := 2 ^ k
  have hqpos : 0 < q := pow_pos (by decide) _
  letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  have hqne : q ≠ 0 := Nat.ne_of_gt hqpos
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hqne)
  change ((1 + residueZ q) ^ (q - 1)).coeff 0 = 1
  rw [show 1 + residueZ q = residueZ q + 1 by ac_rfl, add_pow]
  simp only [residueZ_pow, one_pow, mul_one, AddMonoidAlgebra.natCast_def,
    AddMonoidAlgebra.single_mul_single, one_mul, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_single, Finset.sum_apply']
  refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
  · intro m hm hm0
    rw [Finsupp.single_eq_of_ne']
    have hmlt : m < q := by
      rw [← hpred]
      exact Finset.mem_range.mp hm
    have hmne : m • (1 : ZMod q) ≠ 0 :=
      nsmul_ne_zero_of_lt_addOrderOf hm0 (by
        simpa [ZMod.addOrderOf_one] using hmlt)
    simpa using hmne
  · simp [hpred, hqpos]
  · simp

/-- Every coefficient of `t^(q-1)` is one for a power of two `q`. -/
theorem coeff_residueT_pow_pred_two_pow_eq_one
    (k : ℕ) (r : ZMod (2 ^ k)) :
    (residueT (2 ^ k) ^ (2 ^ k - 1)).coeff r = 1 := by
  let q := 2 ^ k
  have hqpos : 0 < q := pow_pos (by decide) _
  letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  have hpred : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hqpos))
  have hx :
      residueT q * residueT q ^ (q - 1) = 0 := by
    rw [← pow_succ', hpred]
    simpa [q] using residueT_pow_two_pow_eq_zero k
  calc
    (residueT (2 ^ k) ^ (2 ^ k - 1)).coeff r =
        (residueT q ^ (q - 1)).coeff 0 := by
          simpa [q] using
            coeff_eq_coeff_zero_of_residueT_mul_eq_zero
              (x := residueT q ^ (q - 1)) hx (show ZMod q from r)
    _ = 1 := by
      simpa [q] using coeff_zero_residueT_pow_pred_two_pow k

end SuccessorTree.NonPrecompact

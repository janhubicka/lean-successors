import Mathlib

/-!
# Affine fibres over F₂

Small reusable lemmas for the BANANA residue colouring.  The parity
arguments repeatedly use that a nonempty affine fibre of a linear map is
a translate of its kernel, and that an underdetermined linear system over
`F₂` therefore has an even number of solutions.
-/

namespace SuccessorTree.NonPrecompact

abbrev F2 := ZMod 2

/-- The affine fibre of a linear map. -/
def affineFiber
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module F2 V] [Module F2 W]
    (L : V →ₗ[F2] W) (b : W) :=
  {x : V // L x = b}

/-- A nonempty affine fibre is a translate of the kernel. -/
noncomputable def affineFiberEquivKer
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module F2 V] [Module F2 W]
    (L : V →ₗ[F2] W) (b : W) (x0 : affineFiber L b) :
    affineFiber L b ≃ LinearMap.ker L where
  toFun x := ⟨x.1 - x0.1, by
    change L (x.1 - x0.1) = 0
    rw [map_sub, x.2, x0.2, sub_self]⟩
  invFun k := ⟨k.1 + x0.1, by
    change L (k.1 + x0.1) = b
    have hk : L k.1 = 0 := by
      simpa [LinearMap.mem_ker] using k.2
    rw [map_add, hk, x0.2, zero_add]⟩
  left_inv x := by
    apply Subtype.ext
    change (x.1 - x0.1) + x0.1 = x.1
    abel
  right_inv k := by
    apply Subtype.ext
    change (k.1 + x0.1) - x0.1 = k.1
    abel

theorem affineFiber_card_eq_ker_card
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module F2 V] [Module F2 W]
    [Finite V] [Finite W]
    (L : V →ₗ[F2] W) (b : W) (x0 : affineFiber L b) :
    Nat.card (affineFiber L b) = Nat.card (LinearMap.ker L) :=
  Nat.card_congr (affineFiberEquivKer L b x0)

/-- A nontrivial kernel over `F₂` has even cardinality. -/
theorem even_card_ker_of_ne_bot
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module F2 V] [Module F2 W]
    [Finite V] [Finite W]
    [FiniteDimensional F2 V] [FiniteDimensional F2 W]
    (L : V →ₗ[F2] W) (hker : LinearMap.ker L ≠ ⊥) :
    Even (Nat.card (LinearMap.ker L)) := by
  rw [Module.natCard_eq_pow_finrank (K := F2), Nat.card_zmod]
  exact even_two.pow_of_ne_zero
    (Nat.ne_of_gt ((Submodule.one_le_finrank_iff).2 hker))

/-- An underdetermined affine system over `F₂` has an even number of
solutions (including the inconsistent case, whose fibre is empty). -/
theorem even_card_affineFiber_of_finrank_lt
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module F2 V] [Module F2 W]
    [Finite V] [Finite W]
    [FiniteDimensional F2 V] [FiniteDimensional F2 W]
    (L : V →ₗ[F2] W) (b : W)
    (hdim : Module.finrank F2 W < Module.finrank F2 V) :
    Even (Nat.card (affineFiber L b)) := by
  by_cases hne : Nonempty (affineFiber L b)
  · let x0 : affineFiber L b := Classical.choice hne
    rw [affineFiber_card_eq_ker_card L b x0]
    exact even_card_ker_of_ne_bot L (L.ker_ne_bot_of_finrank_lt hdim)
  · letI : IsEmpty (affineFiber L b) := ⟨fun x => hne ⟨x⟩⟩
    rw [(Finite.card_eq_zero_iff).2 inferInstance]
    simp


/-- General power-of-two divisibility for affine fibres over F₂.

A nonempty affine fibre is a translate of the kernel.  Rank-nullity and
the bound on the rank by the target dimension show that its cardinality is
divisible by 2^(dim V - dim W).  The empty fibre is covered uniformly. -/
theorem pow_two_finrank_sub_dvd_card_affineFiber
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module F2 V] [Module F2 W]
    [Finite V] [Finite W]
    [FiniteDimensional F2 V] [FiniteDimensional F2 W]
    (L : V →ₗ[F2] W) (b : W) :
    2 ^ (Module.finrank F2 V - Module.finrank F2 W) ∣
      Nat.card (affineFiber L b) := by
  by_cases hne : Nonempty (affineFiber L b)
  · let x0 : affineFiber L b := Classical.choice hne
    rw [affineFiber_card_eq_ker_card L b x0]
    rw [Module.natCard_eq_pow_finrank (K := F2), Nat.card_zmod]
    apply pow_dvd_pow 2
    have hrange :
        Module.finrank F2 (LinearMap.range L) ≤
          Module.finrank F2 W :=
      (LinearMap.range L).finrank_le
    have hsum := L.finrank_range_add_finrank_ker
    omega
  · letI : IsEmpty (affineFiber L b) :=
      ⟨fun x => hne ⟨x⟩⟩
    rw [(Finite.card_eq_zero_iff).2 inferInstance]
    exact dvd_zero _

end SuccessorTree.NonPrecompact

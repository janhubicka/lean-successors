import SuccessorTree.BANANA.EPPA
import SuccessorTree.BANANA.StrongAmalgamation

namespace SuccessorTree.BANANA

/-- An embedding of two-sorted bilinear structures.  This is the finite
BANANA embedding notion stripped of first-order-language bureaucracy. -/
structure PairingEmbedding
    {K LA RA LB RB : Type*} [Field K]
    [AddCommGroup LA] [Module K LA] [AddCommGroup RA] [Module K RA]
    [AddCommGroup LB] [Module K LB] [AddCommGroup RB] [Module K RB]
    (βA : BilinearPairing K LA RA) (βB : BilinearPairing K LB RB) where
  left : LA →ₗ[K] LB
  right : RA →ₗ[K] RB
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  preserves : ∀ x y, βB (left x) (right y) = βA x y

/-- Any injective linear map can be put into the split-coordinate form
used by the explicit BANANA amalgamation construction. -/
theorem exists_split_equiv_of_injective
    {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (hf : Function.Injective f) :
    ∃ Q : Submodule K W, ∃ e : (V × Q) ≃ₗ[K] W,
      ∀ x : V, e (x, 0) = f x := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (LinearMap.range f)
  let er : V ≃ₗ[K] LinearMap.range f := LinearEquiv.ofInjective f hf
  let ep : (LinearMap.range f × Q) ≃ₗ[K] W :=
    (LinearMap.range f).prodEquivOfIsCompl Q hQ
  refine ⟨Q, (er.prodCongr (LinearEquiv.refl K Q)).trans ep, ?_⟩
  intro x
  simp [er, ep, LinearEquiv.trans_apply]

/-- Both sides of a BANANA embedding admit compatible split coordinates.
Thus arbitrary amalgamation diagrams reduce to the split situation treated
in `StrongAmalgamation.lean`. -/
theorem PairingEmbedding.exists_split_coordinates
    {K LA RA LB RB : Type*} [Field K]
    [AddCommGroup LA] [Module K LA] [AddCommGroup RA] [Module K RA]
    [AddCommGroup LB] [Module K LB] [AddCommGroup RB] [Module K RB]
    {βA : BilinearPairing K LA RA} {βB : BilinearPairing K LB RB}
    (e : PairingEmbedding βA βB) :
    ∃ QL : Submodule K LB, ∃ QR : Submodule K RB,
      ∃ eL : (LA × QL) ≃ₗ[K] LB, ∃ eR : (RA × QR) ≃ₗ[K] RB,
        (∀ x : LA, eL (x, 0) = e.left x) ∧
        (∀ y : RA, eR (y, 0) = e.right y) := by
  obtain ⟨QL, eL, hL⟩ :=
    exists_split_equiv_of_injective e.left e.left_injective
  obtain ⟨QR, eR, hR⟩ :=
    exists_split_equiv_of_injective e.right e.right_injective
  exact ⟨QL, QR, eL, eR, hL, hR⟩


/-- Orthogonal direct sum of two bilinear pairings.  This is the joint
embedding construction for finite BANANA structures. -/
def pairingSum
    {K L₁ R₁ L₂ R₂ : Type*} [Field K]
    [AddCommGroup L₁] [Module K L₁] [AddCommGroup R₁] [Module K R₁]
    [AddCommGroup L₂] [Module K L₂] [AddCommGroup R₂] [Module K R₂]
    (β₁ : BilinearPairing K L₁ R₁) (β₂ : BilinearPairing K L₂ R₂) :
    BilinearPairing K (L₁ × L₂) (R₁ × R₂) := by
  apply LinearMap.mk₂ K (fun x y => β₁ x.1 y.1 + β₂ x.2 y.2)
  · intro x x' y
    simp [add_assoc, add_left_comm, add_comm]
  · intro c x y
    simp [mul_add]
  · intro x y y'
    simp [add_assoc, add_left_comm, add_comm]
  · intro c x y
    simp [mul_add]

/-- The first summand embeds into the orthogonal sum. -/
def pairingSumInl
    {K L₁ R₁ L₂ R₂ : Type*} [Field K]
    [AddCommGroup L₁] [Module K L₁] [AddCommGroup R₁] [Module K R₁]
    [AddCommGroup L₂] [Module K L₂] [AddCommGroup R₂] [Module K R₂]
    (β₁ : BilinearPairing K L₁ R₁) (β₂ : BilinearPairing K L₂ R₂) :
    PairingEmbedding β₁ (pairingSum β₁ β₂) where
  left := LinearMap.inl K L₁ L₂
  right := LinearMap.inl K R₁ R₂
  left_injective := LinearMap.inl_injective
  right_injective := LinearMap.inl_injective
  preserves := by
    intro x y
    simp [pairingSum]

/-- The second summand embeds into the orthogonal sum. -/
def pairingSumInr
    {K L₁ R₁ L₂ R₂ : Type*} [Field K]
    [AddCommGroup L₁] [Module K L₁] [AddCommGroup R₁] [Module K R₁]
    [AddCommGroup L₂] [Module K L₂] [AddCommGroup R₂] [Module K R₂]
    (β₁ : BilinearPairing K L₁ R₁) (β₂ : BilinearPairing K L₂ R₂) :
    PairingEmbedding β₂ (pairingSum β₁ β₂) where
  left := LinearMap.inr K L₁ L₂
  right := LinearMap.inr K R₁ R₂
  left_injective := LinearMap.inr_injective
  right_injective := LinearMap.inr_injective
  preserves := by
    intro x y
    simp [pairingSum]


end SuccessorTree.BANANA

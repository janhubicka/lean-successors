import SuccessorTree.BANANA.EPPA

namespace SuccessorTree.BANANA

/-- The automorphism group of a bilinear pairing, realised as a subgroup of
the product of the two general linear groups. -/
def pairingAutSubgroup
    {K L R : Type*} [Field K]
    [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    (β : BilinearPairing K L R) :
    Subgroup ((L ≃ₗ[K] L) × (R ≃ₗ[K] R)) where
  carrier := {p | ∀ x y, β (p.1 x) (p.2 y) = β x y}
  one_mem' := by
    intro x y
    rfl
  mul_mem' := by
    intro a b ha hb x y
    change β (a.1 (b.1 x)) (a.2 (b.2 y)) = β x y
    rw [ha, hb]
  inv_mem' := by
    intro a ha x y
    have h := ha (a.1.symm x) (a.2.symm y)
    simpa using h.symm

abbrev PairingAut
    {K L R : Type*} [Field K]
    [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    (β : BilinearPairing K L R) :=
  pairingAutSubgroup β

/-- An automorphism of a pairing acts canonically on its perfect
completion: on the dual coordinates it acts contragrediently. -/
noncomputable def completionPairingAut
    {K L R : Type*} [Field K]
    [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    {β : BilinearPairing K L R} (a : PairingAut β) :
    PairingAut (completionForm β) := by
  refine ⟨(a.1.1.prodCongr a.1.2.symm.dualMap,
      a.1.2.prodCongr a.1.1.symm.dualMap), ?_⟩
  intro x y
  simp only [completionForm_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.dualMap_apply]
  rw [a.2]
  simp

theorem completionPairingAut_one
    {K L R : Type*} [Field K]
    [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    {β : BilinearPairing K L R} :
    completionPairingAut (1 : PairingAut β) = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · ext x <;> simp [completionPairingAut]
  · ext x <;> simp [completionPairingAut]

theorem completionPairingAut_mul
    {K L R : Type*} [Field K]
    [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    {β : BilinearPairing K L R} (a b : PairingAut β) :
    completionPairingAut (a * b) =
      completionPairingAut a * completionPairingAut b := by
  apply Subtype.ext
  apply Prod.ext
  · ext x <;> simp [completionPairingAut]
  · ext x <;> simp [completionPairingAut]

/-- The perfect-completion construction is functorial on automorphism
groups.  This is the local homomorphism used in the coherent-EPPA
transport construction. -/
noncomputable def completionPairingAutHom
    {K L R : Type*} [Field K]
    [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    (β : BilinearPairing K L R) :
    PairingAut β →* PairingAut (completionForm β) where
  toFun := completionPairingAut
  map_one' := completionPairingAut_one
  map_mul' := completionPairingAut_mul

end SuccessorTree.BANANA

import Mathlib

namespace SuccessorTree.BANANA

open Module

/-- A bilinear pairing between two vector spaces. -/
abbrev BilinearPairing (K L R : Type*) [CommSemiring K] [AddCommMonoid L]
    [Module K L] [AddCommMonoid R] [Module K R] :=
  L →ₗ[K] (R →ₗ[K] K)

/-- The perfect-completion form used in the BANANA paper. -/
def completionForm {K L R : Type*} [CommRing K]
    [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    (β : BilinearPairing K L R) :
    (L × Module.Dual K R) →ₗ[K] ((R × Module.Dual K L) →ₗ[K] K) := by
  apply LinearMap.mk₂ K
    (fun x y => β x.1 y.1 + x.2 y.1 + y.2 x.1)
  · intro x x' y
    simp [add_assoc, add_left_comm, add_comm]
  · intro c x y
    simp [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
  · intro x y y'
    simp [add_assoc, add_left_comm, add_comm]
  · intro c x y
    simp [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]

@[simp] theorem completionForm_apply {K L R : Type*} [CommRing K]
    [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    (β : BilinearPairing K L R) (x : L × Module.Dual K R)
    (y : R × Module.Dual K L) :
    completionForm β x y = β x.1 y.1 + x.2 y.1 + y.2 x.1 := by
  rfl

/-- A lower triangular shear.  This is the elementary automorphism used to
absorb the defect of arbitrary extensions of a partial pairing isomorphism. -/
def lowerShear {K M N : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (D : M →ₗ[K] N) : (M × N) ≃ₗ[K] (M × N) where
  toFun z := (z.1, D z.1 + z.2)
  invFun z := (z.1, z.2 - D z.1)
  left_inv z := by
    ext <;> simp
  right_inv z := by
    ext <;> simp
  map_add' x y := by
    ext <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' c x := by
    ext <;> simp [smul_add]

@[simp] theorem lowerShear_apply {K M N : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (D : M →ₗ[K] N) (x : M) (y : N) :
    lowerShear D (x, y) = (x, D x + y) := by
  rfl

/-- An isomorphism between two finite sub-pairings of a fixed ambient
pairing. -/
structure PartialPairingIso {K L R : Type*} [Field K]
    [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
    (β : BilinearPairing K L R) where
  leftDom : Submodule K L
  leftCod : Submodule K L
  rightDom : Submodule K R
  rightCod : Submodule K R
  left : leftDom ≃ₗ[K] leftCod
  right : rightDom ≃ₗ[K] rightCod
  preserves : ∀ x : leftDom, ∀ y : rightDom,
    β (x : L) (y : R) = β (left x : L) (right y : R)

namespace PartialPairingIso

variable {K L R : Type*} [Field K]
  [AddCommGroup L] [Module K L] [AddCommGroup R] [Module K R]
  {β : BilinearPairing K L R}

/-- The pairing defect, viewed on the target right subspace. -/
noncomputable def localDefect (p : PartialPairingIso β)
    (F : L ≃ₗ[K] L) (G : R ≃ₗ[K] R) :
    L →ₗ[K] Module.Dual K p.rightCod := by
  apply LinearMap.mk₂ K
    (fun x (y : p.rightCod) =>
      β (F.symm x) (G.symm (y : R)) - β x (y : R))
  · intro x x' y
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · intro c x y
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  · intro x y y'
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · intro c x y
    simp only [Submodule.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring

/-- Extend the local defect linearly from the target right subspace to the
whole right space. -/
noncomputable def globalDefect (p : PartialPairingIso β)
    (F : L ≃ₗ[K] L) (G : R ≃ₗ[K] R) :
    L →ₗ[K] Module.Dual K R :=
  (Subspace.dualLift p.rightCod).comp (p.localDefect F G)

/-- The correction on the dual-left coordinate of the right completion.
It is chosen so that the two completed maps preserve the pairing globally. -/
noncomputable def rightCorrection (p : PartialPairingIso β)
    (F : L ≃ₗ[K] L) (G : R ≃ₗ[K] R) :
    R →ₗ[K] Module.Dual K L := by
  let D := p.globalDefect F G
  apply LinearMap.mk₂ K
    (fun (y : R) (x : L) => β (F.symm x) (G.symm y) - β x y - D x y)
  · intro y y' x
    simp only [map_add, LinearMap.add_apply]
    ring
  · intro c y x
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  · intro y x x'
    simp only [map_add, LinearMap.add_apply]
    ring
  · intro c y x
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring

@[simp] theorem localDefect_apply (p : PartialPairingIso β)
    (F : L ≃ₗ[K] L) (G : R ≃ₗ[K] R) (x : L) (y : p.rightCod) :
    p.localDefect F G x y =
      β (F.symm x) (G.symm (y : R)) - β x (y : R) := by
  rfl

@[simp] theorem rightCorrection_apply (p : PartialPairingIso β)
    (F : L ≃ₗ[K] L) (G : R ≃ₗ[K] R) (y : R) (x : L) :
    p.rightCorrection F G y x =
      β (F.symm x) (G.symm y) - β x y - p.globalDefect F G x y := by
  rfl

/-- The left automorphism of the perfect completion obtained from arbitrary
ambient extensions `F,G` of the partial isomorphism. -/
noncomputable def completionLeftExtension (p : PartialPairingIso β)
    (F : L ≃ₗ[K] L) (G : R ≃ₗ[K] R) :
    ((L × Module.Dual K R) ≃ₗ[K] (L × Module.Dual K R)) :=
  (F.prodCongr G.symm.dualMap).trans (lowerShear (p.globalDefect F G))

/-- The corresponding right automorphism of the perfect completion. -/
noncomputable def completionRightExtension (p : PartialPairingIso β)
    (F : L ≃ₗ[K] L) (G : R ≃ₗ[K] R) :
    ((R × Module.Dual K L) ≃ₗ[K] (R × Module.Dual K L)) :=
  (G.prodCongr F.symm.dualMap).trans (lowerShear (p.rightCorrection F G))

/-- The two completed automorphisms preserve the perfect-completion pairing.
This identity does not require `F,G` themselves to preserve `β`; the two
shear terms absorb exactly their defect. -/
theorem completion_extensions_preserve (p : PartialPairingIso β)
    (F : L ≃ₗ[K] L) (G : R ≃ₗ[K] R)
    (x : L × Module.Dual K R) (y : R × Module.Dual K L) :
    completionForm β (p.completionLeftExtension F G x)
        (p.completionRightExtension F G y) = completionForm β x y := by
  simp only [completionForm_apply, completionLeftExtension,
    completionRightExtension, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    lowerShear_apply, LinearMap.add_apply, rightCorrection_apply,
    LinearEquiv.dualMap_apply, LinearEquiv.symm_apply_apply]
  ring

/-- On the target right subspace, the global defect agrees with the local
one by construction. -/
theorem globalDefect_apply_of_mem (p : PartialPairingIso β)
    (F : L ≃ₗ[K] L) (G : R ≃ₗ[K] R) (x : L) {y : R}
    (hy : y ∈ p.rightCod) :
    p.globalDefect F G x y = p.localDefect F G x ⟨y, hy⟩ := by
  simp only [globalDefect, LinearMap.comp_apply]
  exact Subspace.dualLift_of_mem hy

/-- Arbitrary extensions `F,G` of the two sides give an extension of the
partial isomorphism to the perfect completion. -/
theorem completion_extensions_apply_left (p : PartialPairingIso β)
    (F : L ≃ₗ[K] L) (G : R ≃ₗ[K] R)
    (hF : ∀ x : p.leftDom, p.left x = F x)
    (hG : ∀ y : p.rightDom, p.right y = G y)
    (x : p.leftDom) :
    p.completionLeftExtension F G ((x : L), 0) = ((p.left x : L), 0) := by
  have hlocal : p.localDefect F G (F x) = 0 := by
    ext y'
    let y : p.rightDom := p.right.symm y'
    have hGy : G (y : R) = (y' : R) := by
      calc
        G (y : R) = (p.right y : R) := by simpa using (hG y).symm
        _ = (y' : R) := by simp [y]
    have hGsymm : G.symm (y' : R) = (y : R) := by
      apply G.injective
      simp [hGy]
    have hFx : F (x : L) = (p.left x : L) := by
      simpa using (hF x).symm
    simp only [localDefect_apply, LinearMap.zero_apply]
    rw [F.symm_apply_apply, hGsymm, hFx, p.preserves x y]
    simp [y]
  have hD : p.globalDefect F G (F x) = 0 := by
    rw [globalDefect, LinearMap.comp_apply, hlocal, map_zero]
  simp [completionLeftExtension, lowerShear, hD, hF x]

/-- The right completed automorphism extends the right part of the partial
isomorphism. -/
theorem completion_extensions_apply_right (p : PartialPairingIso β)
    (F : L ≃ₗ[K] L) (G : R ≃ₗ[K] R)
    (hG : ∀ y : p.rightDom, p.right y = G y)
    (y : p.rightDom) :
    p.completionRightExtension F G ((y : R), 0) = ((p.right y : R), 0) := by
  have hGy : G (y : R) = (p.right y : R) := by
    simpa using (hG y).symm
  have hy : G (y : R) ∈ p.rightCod := by
    rw [hGy]
    exact (p.right y).property
  have hC : p.rightCorrection F G (G y) = 0 := by
    ext x
    rw [rightCorrection_apply, p.globalDefect_apply_of_mem F G x hy]
    simp only [localDefect_apply, LinearMap.zero_apply, G.symm_apply_apply]
    ring
  simp only [completionRightExtension, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply, lowerShear_apply, map_zero, add_zero]
  rw [hC, hGy]

/-- Ordinary EPPA for one finite BANANA structure: its perfect completion is
an EPPA witness.  The ambient extensions of the two partial linear maps are
supplied by `Submodule.exists_linearEquiv_restrict_eq`; the correction terms
above make them pairing-preserving on the completion. -/
theorem exists_completion_extension (p : PartialPairingIso β)
    [FiniteDimensional K L] [FiniteDimensional K R] :
    ∃ H : ((L × Module.Dual K R) ≃ₗ[K] (L × Module.Dual K R)),
      ∃ J : ((R × Module.Dual K L) ≃ₗ[K] (R × Module.Dual K L)),
        (∀ x : p.leftDom, H ((x : L), 0) = ((p.left x : L), 0)) ∧
        (∀ y : p.rightDom, J ((y : R), 0) = ((p.right y : R), 0)) ∧
        (∀ x y, completionForm β (H x) (J y) = completionForm β x y) := by
  obtain ⟨F, hF⟩ := p.leftDom.exists_linearEquiv_restrict_eq p.left
  obtain ⟨G, hG⟩ := p.rightDom.exists_linearEquiv_restrict_eq p.right
  refine ⟨p.completionLeftExtension F G, p.completionRightExtension F G, ?_, ?_, ?_⟩
  · exact p.completion_extensions_apply_left F G hF hG
  · exact p.completion_extensions_apply_right F G hG
  · exact p.completion_extensions_preserve F G

end PartialPairingIso

end SuccessorTree.BANANA

import SuccessorTree.NonPrecompact.AffineParity

/-!
# Extending partial linear equivalences over a fixed quotient

This file formalises the elementary linear-extension lemma used in the
circulation part of the BANANA manuscript.

The main statement says that if two surjective linear maps from the same
finite-dimensional vector space to a common quotient agree along a partial
linear equivalence, then that partial equivalence extends to a global linear
automorphism intertwining the two quotient maps.
-/

namespace SuccessorTree.NonPrecompact

open LinearMap Module

section AmbientExtension

variable {K V V' : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']

/-- A linear equivalence between subspaces of equal-dimensional finite
vector spaces extends to a linear equivalence of the ambient spaces. -/
theorem exists_linearEquiv_extends_submoduleEquiv
    {W : Submodule K V} {W' : Submodule K V'}
    (f : W ≃ₗ[K] W')
    (hdim : finrank K V = finrank K V') :
    ∃ g : V ≃ₗ[K] V', ∀ x : W, g x = f x := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
  let eQ : (W × Q) ≃ₗ[K] V := W.prodEquivOfIsCompl Q hQ
  obtain ⟨Q', hQ'⟩ := Submodule.exists_isCompl W'
  let eQ' : (W' × Q') ≃ₗ[K] V' := W'.prodEquivOfIsCompl Q' hQ'
  have hQdim : finrank K Q = finrank K Q' := by
    have hleft := eQ.finrank_eq
    have hright := eQ'.finrank_eq
    simp only [Module.finrank_prod] at hleft hright
    have hf := f.finrank_eq
    omega
  let fQ : Q ≃ₗ[K] Q' := LinearEquiv.ofFinrankEq Q Q' hQdim
  refine ⟨eQ.symm ≪≫ₗ LinearEquiv.prodCongr f fQ ≪≫ₗ eQ', ?_⟩
  aesop

end AmbientExtension

section QuotientExtension

variable {V W : Type*}
variable [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
variable [AddCommGroup W] [Module F2 W] [FiniteDimensional F2 W]

/-- Manuscript Lemma `extendlinearmap`, in a slightly more general form.

Two surjections from the same finite-dimensional vector space to a common
quotient are intertwined by a global automorphism whenever a prescribed
partial linear equivalence already intertwines them on its domain. -/
theorem exists_linearEquiv_extends_of_surjective
    (q q' : V →ₗ[F2] W)
    (hq : Function.Surjective q)
    (hq' : Function.Surjective q')
    {A A' : Submodule F2 V}
    (f : A ≃ₗ[F2] A')
    (hf : ∀ x : A, q' (f x) = q x) :
    ∃ h : V ≃ₗ[F2] V,
      (∀ x : A, h x = f x) ∧
      q'.comp h.toLinearMap = q := by
  let qA : A →ₗ[F2] W := q.comp A.subtype
  let qA' : A' →ₗ[F2] W := q'.comp A'.subtype
  have hfA (x : A) : qA' (f x) = qA x := by
    simpa [qA, qA'] using hf x

  have hkerMap :
      Submodule.map f.toLinearMap qA.ker = qA'.ker := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      apply LinearMap.mem_ker.mpr
      change qA' (f x) = 0
      rw [hfA x]
      exact LinearMap.mem_ker.mp hx
    · intro hy
      refine ⟨f.symm y, ?_, ?_⟩
      · apply LinearMap.mem_ker.mpr
        rw [← hfA (f.symm y), f.apply_symm_apply]
        exact LinearMap.mem_ker.mp hy
      · simp

  let fKer : qA.ker ≃ₗ[F2] qA'.ker :=
    LinearEquiv.ofSubmodules f qA.ker qA'.ker hkerMap

  let K := q.ker
  let K' := q'.ker
  let i : qA.ker →ₗ[F2] K :=
    (A.subtype.comp qA.ker.subtype).codRestrict K (fun x => by
      have hx0 : qA x.1 = 0 := LinearMap.mem_ker.mp x.2
      change q x.1.1 = 0
      simpa [qA] using hx0)
  let i' : qA'.ker →ₗ[F2] K' :=
    (A'.subtype.comp qA'.ker.subtype).codRestrict K' (fun x => by
      have hx0 : qA' x.1 = 0 := LinearMap.mem_ker.mp x.2
      change q' x.1.1 = 0
      simpa [qA'] using hx0)
  have hi : Function.Injective i := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : K => (z : V)) hxy
  have hi' : Function.Injective i' := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : K' => (z : V)) hxy

  let I := LinearMap.range i
  let I' := LinearMap.range i'
  let ei : qA.ker ≃ₗ[F2] I := LinearEquiv.ofInjective i hi
  let ei' : qA'.ker ≃ₗ[F2] I' := LinearEquiv.ofInjective i' hi'
  let fI : I ≃ₗ[F2] I' := ei.symm ≪≫ₗ fKer ≪≫ₗ ei'

  have hKdim : finrank F2 K = finrank F2 K' := by
    have hqdim := q.finrank_range_add_finrank_ker
    have hq'dim := q'.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hq, finrank_top] at hqdim
    rw [LinearMap.range_eq_top.mpr hq', finrank_top] at hq'dim
    have hqdimK : finrank F2 W + finrank F2 K = finrank F2 V := by
      simpa [K] using hqdim
    have hq'dimK : finrank F2 W + finrank F2 K' = finrank F2 V := by
      simpa [K'] using hq'dim
    omega

  obtain ⟨T, hT⟩ :=
    exists_linearEquiv_extends_submoduleEquiv fI hKdim

  have hTker (x : qA.ker) : T (i x) = i' (fKer x) := by
    let z : I := ⟨i x, ⟨x, rfl⟩⟩
    have heix : ei.symm z = x := by
      apply ei.injective
      simp [z, ei]
    have hz := hT z
    simpa [z, fI, ei', heix] using hz

  obtain ⟨s, hs⟩ :=
    q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  obtain ⟨s', hs'⟩ :=
    q'.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq')
  have hs_apply (y : W) : q (s y) = y := by
    exact LinearMap.congr_fun hs y
  have hs'_apply (y : W) : q' (s' y) = y := by
    exact LinearMap.congr_fun hs' y

  let pV : V →ₗ[F2] V := LinearMap.id - s.comp q
  have hp_mem (x : V) : pV x ∈ K := by
    change q (pV x) = 0
    simp [pV, hs_apply]
  let p : V →ₗ[F2] K := pV.codRestrict K hp_mem

  let pV' : V →ₗ[F2] V := LinearMap.id - s'.comp q'
  have hp'_mem (x : V) : pV' x ∈ K' := by
    change q' (pV' x) = 0
    simp [pV', hs'_apply]
  let p' : V →ₗ[F2] K' := pV'.codRestrict K' hp'_mem

  let leftCoord : A →ₗ[F2] K := p.comp A.subtype
  let rightCoord : A →ₗ[F2] K' :=
    p'.comp (A'.subtype.comp f.toLinearMap)
  let delta : A →ₗ[F2] K' :=
    rightCoord - T.toLinearMap.comp leftCoord

  have hdeltaKer : qA.ker ≤ delta.ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    let xKer : qA.ker := ⟨x, hx⟩
    have hqx : qA x = 0 := LinearMap.mem_ker.mp hx
    have hqxV : q (x : V) = 0 := by
      simpa [qA] using hqx
    have hleft : leftCoord x = i xKer := by
      apply Subtype.ext
      simp [leftCoord, p, pV, i, xKer, hqxV]
    have hright : rightCoord x = i' (fKer xKer) := by
      apply Subtype.ext
      have hqfx : q' (f x : V) = 0 := by
        rw [hf x]
        exact hqxV
      simp [rightCoord, p', pV', i', fKer, xKer, hqfx]
    simp [delta, hleft, hright, hTker xKer]

  let deltaQ : A ⧸ qA.ker →ₗ[F2] K' :=
    qA.ker.liftQ delta hdeltaKer
  let deltaRange : qA.range →ₗ[F2] K' :=
    deltaQ.comp qA.quotKerEquivRange.symm.toLinearMap
  obtain ⟨L, hL⟩ := LinearMap.exists_extend deltaRange

  have hL_on (x : A) : L (qA x) = delta x := by
    let y : qA.range := ⟨qA x, ⟨x, rfl⟩⟩
    have hy := LinearMap.congr_fun hL y
    calc
      L (qA x) = deltaRange y := by
        simpa [y] using hy
      _ = delta x := by
        have hyq :
            qA.quotKerEquivRange.symm y = qA.ker.mkQ x := by
          exact qA.quotKerEquivRange_symm_apply_image x _
        rw [show deltaRange y =
            deltaQ (qA.quotKerEquivRange.symm y) by rfl, hyq]
        rfl

  let kernelPart : V →ₗ[F2] K' :=
    T.toLinearMap.comp p + L.comp q
  let hlin : V →ₗ[F2] V :=
    K'.subtype.comp kernelPart + s'.comp q

  have hq_hlin (x : V) : q' (hlin x) = q x := by
    have hh :
        hlin x = ((kernelPart x : K') : V) + s' (q x) := rfl
    rw [hh, map_add, hs'_apply]
    have hk := (kernelPart x).2
    change q' (((kernelPart x : K') : V)) = 0 at hk
    rw [hk, zero_add]

  have hlin_injective : Function.Injective hlin := by
    intro x y hxy
    let z := x - y
    have hz : hlin z = 0 := by
      change hlin (x - y) = 0
      rw [map_sub, hxy, sub_self]
    have hqz : q z = 0 := by
      rw [← hq_hlin z, hz, map_zero]
    have hkernel : kernelPart z = T (p z) := by
      simp [kernelPart, hqz]
    have hTz : T (p z) = 0 := by
      apply K'.subtype_injective
      have hh : (((kernelPart z : K') : V)) = 0 := by
        have hz' := hz
        change (((kernelPart z : K') : V)) + s' (q z) = 0 at hz'
        simpa [hqz] using hz'
      simpa [hkernel] using hh
    have hpz : p z = 0 := T.injective (by simpa using hTz)
    have hz0 : z = 0 := by
      have hpz' := congrArg Subtype.val hpz
      change z - s (q z) = 0 at hpz'
      simpa [hqz] using hpz'
    exact sub_eq_zero.mp hz0

  let h : V ≃ₗ[F2] V :=
    LinearEquiv.ofInjectiveOfFinrankEq hlin hlin_injective rfl

  have hext (x : A) : hlin x = f x := by
    have hdelta : L (q x) = delta x := by
      simpa [qA] using hL_on x
    change
      (((T (p x) + L (q x) : K') : V) + s' (q x)) = (f x : V)
    rw [hdelta]
    have hcoord :
        T (p x) + delta x = rightCoord x := by
      simp [delta, leftCoord]
    rw [hcoord]
    change (((p' (f x) : K') : V) + s' (q x)) = (f x : V)
    change (f x : V) - s' (q' (f x)) + s' (q x) = (f x : V)
    rw [hf x]
    abel

  refine ⟨h, ?_, ?_⟩
  · intro x
    change h.toLinearMap (x : V) = (f x : V)
    rw [show h.toLinearMap = hlin by simp [h]]
    exact hext x
  · rw [show h.toLinearMap = hlin by simp [h]]
    ext x
    exact hq_hlin x

end QuotientExtension

end SuccessorTree.NonPrecompact

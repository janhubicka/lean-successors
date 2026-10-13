import SuccessorTree.V10.M2SparsePullbackAge
import SuccessorTree.V10.AdmissibleKptPrefix
import Mathlib.Tactic

/-!
# Finite L-model of one complete admissible partial type

An admissible Kpt node is represented by a vertex v of an actual
forbidden-free partial structure W, at its canonical E free cut n.
Its entire L reduct over the first n vertices plus the type vertex
is consequently a finite forbidden-free induced ordered L-model,
with the distinguished vertex renamed to numerical address n.

The source E relation is not transported into this auxiliary
L-model. It is used only later to choose the one compatible
ordinary E socle for the non-edge padding construction.
-/

namespace SuccessorTree.V10

def typeAgeIndex (n x : Nat) : Option (Fin n) :=
  if h : x < n then some ⟨x,h⟩ else none

/-- Interpret one complete partial-type L-reduct on the finite
initial carrier 0,...,n, with its distinguished type vertex at n. -/
def PartialTypeWithE.ageModel {n db du dd : Nat}
    (T : PartialTypeWithE n db du dd) : AgeTestModel db du dd where
  carrier := {x | x ≤ n}
  binary := fun x y t =>
    T.lReduct.binary (typeAgeIndex n x) (typeAgeIndex n y) t
  unary := fun x t => T.lReduct.unary (typeAgeIndex n x) t
  diagonal := fun x t => T.lReduct.diagonal (typeAgeIndex n x) t

/-- The finite L-model literally realizes the original complete
L type of its last numerical vertex. -/
theorem PartialTypeWithE.ageModel_type {n db du dd : Nat}
    (T : PartialTypeWithE n db du dd) :
    RelationalPrefixType.ofAgeModel T.ageModel n n = T.lReduct := by
  apply RelationalPrefixType.eq_of_atoms
  · intro x y t
    cases x <;> cases y <;>
      simp [RelationalPrefixType.ofAgeModel,PartialTypeWithE.ageModel,
        prefixVertexIndex,typeAgeIndex]
  · intro x t
    cases x <;>
      simp [RelationalPrefixType.ofAgeModel,PartialTypeWithE.ageModel,
        prefixVertexIndex,typeAgeIndex]
  · intro x t
    cases x <;>
      simp [RelationalPrefixType.ofAgeModel,PartialTypeWithE.ageModel,
        prefixVertexIndex,typeAgeIndex]

/-- Every genuine admissible L+ type has its one-point finite L model
embedded inducedly into the actual forbidden-free ambient witness.
The embedding needs to be increasing only on the carrier. -/
theorem PartialTypeWithE.ageModel_induced_of_admissible
    {n db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (T : PartialTypeWithE n db du dd)
    (hAd : IsAdmissibleRawType family
      (⟨n,T⟩ : RawPartialTypeNode db du dd)) :
    ∃ W : EnumeratedPartialStructure db du dd,
      (∀ bad, bad ∈ family → bad.Avoids W.L) ∧
      T.ageModel.InducedEmbeddingOnCarrier W.L := by
  obtain ⟨W,w,hw,hAvoid,hRaw⟩ := hAd
  have hCut : n = W.freeLevel w := congrArg Sigma.fst hRaw
  have hEq : T = W.partialTypeAt n w := by
    have hSigma :
      (⟨n,T⟩ : RawPartialTypeNode db du dd) =
        (⟨n,W.partialTypeAt n w⟩ : RawPartialTypeNode db du dd) := by
      calc
        (⟨n,T⟩ : RawPartialTypeNode db du dd) =
          W.rawTypeAtFree w := hRaw
        _ = (⟨n,W.partialTypeAt n w⟩ :
            RawPartialTypeNode db du dd) := by
          change
            (⟨W.freeLevel w,
              W.partialTypeAt (W.freeLevel w) w⟩ :
              RawPartialTypeNode db du dd) =
            (⟨n,W.partialTypeAt n w⟩ :
              RawPartialTypeNode db du dd)
          rw [←hCut]
    exact eq_of_heq (Sigma.mk.inj_iff.mp hSigma).2
  let phi : Nat → Nat := fun x => prefixVertexIndex w (typeAgeIndex n x)
  have hPhiLow (x : Nat) (hx : x < n) : phi x = x := by
    simp [phi,typeAgeIndex,hx,prefixVertexIndex]
  have hPhiTop : phi n = w := by
    simp [phi,typeAgeIndex,prefixVertexIndex]
  have hnW : n ≤ w := by
    have hBound := W.freeLevel_le w
    omega
  refine ⟨W,hAvoid,?_⟩
  exact
    { toFun := phi
      order := by
        intro x y hx hy hxy
        change x ≤ n at hx
        change y ≤ n at hy
        by_cases hyLow : y < n
        · have hxLow : x < n := by omega
          rw [hPhiLow x hxLow,hPhiLow y hyLow]
          exact hxy
        · have hyTop : y = n := by omega
          have hxLow : x < n := by omega
          rw [hyTop,hPhiTop,hPhiLow x hxLow]
          omega
      inside := by
        intro x hx
        change x ≤ n at hx
        by_cases hxLow : x < n
        · rw [hPhiLow x hxLow]
          exact (W.carrier_iff x).2 (by omega)
        · have hxTop : x = n := by omega
          rw [hxTop,hPhiTop]
          exact (W.carrier_iff w).2 hw
      binary := by
        intro x y hx hy hne t
        change W.L.binary (phi x) (phi y) t =
          T.lReduct.binary (typeAgeIndex n x) (typeAgeIndex n y) t
        rw [hEq]
        rfl
      unary := by
        intro x hx t
        change W.L.unary (phi x) t =
          T.lReduct.unary (typeAgeIndex n x) t
        rw [hEq]
        rfl
      diagonal := by
        intro x hx t
        change W.L.diagonal (phi x) t =
          T.lReduct.diagonal (typeAgeIndex n x) t
        rw [hEq]
        rfl }

/-- The original source admissibility certificate itself supplies
forbidden avoidance of the finite type L-model. -/
theorem PartialTypeWithE.ageModel_avoids
    {n db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (T : PartialTypeWithE n db du dd)
    (hAd : IsAdmissibleRawType family
      (⟨n,T⟩ : RawPartialTypeNode db du dd)) :
    ∀ bad, bad ∈ family → bad.Avoids T.ageModel := by
  obtain ⟨W,hAvoid,hEmbed⟩ :=
    T.ageModel_induced_of_admissible family hAd
  exact hEmbed.preserves_avoidance family hAvoid

end SuccessorTree.V10

import SuccessorTree.V10.M2SourceTypeAge
import SuccessorTree.V10.M2NonedgePairAge
import SuccessorTree.V10.PrescribedBoringData
import Mathlib.Tactic

/-!
# Two compatible source types, freely joined over their old L-socle

The two genuine type vertices are placed at n and n+1, with no
binary L relation between them. Every relation to the first n
vertices, including negative directed atoms and each singleton,
is copied from its own full source L+ type. The initial L-socle
agrees by SameOrdinaryAtCut.

The two one-vertex-deleted restrictions embed inducedly into the
individual type age models. Normalized irreducible forbidden
avoidance follows from the two-vertex nonedge lemma. The auxiliary
E relation is added subsequently by NonedgePadding, not here.
-/

namespace SuccessorTree.V10

/-- In the right-hand one-point model, the newer distinguished vertex
at n+1 is renamed back to n; all earlier source positions are fixed. -/
def freePairRightAddress (n x : Nat) : Nat :=
  if x = n+1 then n else x

/-- Literal finite ordered L free amalgamation of two type records
with a common initial socle. No edge in either direction joins their
distinguished vertices. -/
def twoTypeFreeAge {n db du dd : Nat}
    (T U : PartialTypeWithE n db du dd) :
    AgeTestModel db du dd where
  carrier := {x | x < n+2}
  binary := fun x y t =>
    if x = n+1 then
      if y = n then false
      else U.lReduct.binary none (typeAgeIndex n y) t
    else if y = n+1 then
      if x = n then false
      else U.lReduct.binary (typeAgeIndex n x) none t
    else T.lReduct.binary (typeAgeIndex n x) (typeAgeIndex n y) t
  unary := fun x t =>
    if x = n+1 then U.lReduct.unary none t
    else T.lReduct.unary (typeAgeIndex n x) t
  diagonal := fun x t =>
    if x = n+1 then U.lReduct.diagonal none t
    else T.lReduct.diagonal (typeAgeIndex n x) t

/-- The joint pair has no directed L-atom between its two new
vertices. This is the only property needed by irreducibility. -/
theorem twoTypeFreeAge_no_cross {n db du dd : Nat}
    (T U : PartialTypeWithE n db du dd) (t : Fin db) :
    (twoTypeFreeAge T U).binary n (n+1) t = false ∧
      (twoTypeFreeAge T U).binary (n+1) n t = false := by
  constructor <;> simp [twoTypeFreeAge]

/-- Deleting the second distinguished vertex recovers the whole first
source type L-model by the identity map on the true carrier. -/
def twoTypeFreeAge_left_embeds {n db du dd : Nat}
    (T U : PartialTypeWithE n db du dd) :
    AgeTestModel.InducedEmbeddingOnCarrier
      ((twoTypeFreeAge T U).withoutVertex (n+1)) T.ageModel where
  toFun := id
  order := by
    intro x y hx hy hxy
    exact hxy
  inside := by
    intro x hx
    change x < n+2 ∧ x ≠ n+1 at hx
    change x ≤ n
    omega
  binary := by
    intro x y hx hy hne t
    change x < n+2 ∧ x ≠ n+1 at hx
    change y < n+2 ∧ y ≠ n+1 at hy
    change (T.ageModel).binary x y t = (twoTypeFreeAge T U).binary x y t
    simp [twoTypeFreeAge,PartialTypeWithE.ageModel,hx.2,hy.2]
  unary := by
    intro x hx t
    change x < n+2 ∧ x ≠ n+1 at hx
    change (T.ageModel).unary x t = (twoTypeFreeAge T U).unary x t
    simp [twoTypeFreeAge,PartialTypeWithE.ageModel,hx.2]
  diagonal := by
    intro x hx t
    change x < n+2 ∧ x ≠ n+1 at hx
    change (T.ageModel).diagonal x t = (twoTypeFreeAge T U).diagonal x t
    simp [twoTypeFreeAge,PartialTypeWithE.ageModel,hx.2]

/-- Deleting the first distinguished vertex recovers the second
source type L-model, renaming n+1 to n. Initial L atoms agree by
compatibility; all directed incidences with the other distinguished
vertex are copied literally. -/
def twoTypeFreeAge_right_embeds {n db du dd : Nat}
    (T U : PartialTypeWithE n db du dd)
    (hComp : SameOrdinaryAtCut T U) :
    AgeTestModel.InducedEmbeddingOnCarrier
      ((twoTypeFreeAge T U).withoutVertex n) U.ageModel where
  toFun := freePairRightAddress n
  order := by
    intro x y hx hy hxy
    change x < n+2 ∧ x ≠ n at hx
    change y < n+2 ∧ y ≠ n at hy
    by_cases hyTop : y = n+1
    · have hxLow : x < n := by omega
      simp [freePairRightAddress,hyTop,show x ≠ n+1 by omega]
      omega
    · have hxLow : x < n := by omega
      have hyLow : y < n := by omega
      simpa [freePairRightAddress,hyTop,
        show x ≠ n+1 by omega] using hxy
  inside := by
    intro x hx
    change x < n+2 ∧ x ≠ n at hx
    change freePairRightAddress n x ≤ n
    by_cases hxTop : x = n+1
    · simp [freePairRightAddress,hxTop]
    · have hxLow : x < n := by omega
      simp [freePairRightAddress,hxTop]
      omega
  binary := by
    intro x y hx hy hne t
    change x < n+2 ∧ x ≠ n at hx
    change y < n+2 ∧ y ≠ n at hy
    change (U.ageModel).binary (freePairRightAddress n x)
      (freePairRightAddress n y) t = (twoTypeFreeAge T U).binary x y t
    by_cases hxTop : x = n+1
    · subst x
      have hyLow : y < n := by omega
      have hyNe : y ≠ n := by omega
      have hyNeTop : y ≠ n+1 := by omega
      simp [twoTypeFreeAge,PartialTypeWithE.ageModel,
        freePairRightAddress,typeAgeIndex,hyLow,hyNe,hyNeTop]
    · by_cases hyTop : y = n+1
      · subst y
        have hxLow : x < n := by omega
        have hxNe : x ≠ n := by omega
        simp [twoTypeFreeAge,PartialTypeWithE.ageModel,
          freePairRightAddress,typeAgeIndex,hxLow,hxTop,hxNe]
      · have hxLow : x < n := by omega
        have hyLow : y < n := by omega
        let i : Fin n := ⟨x,hxLow⟩
        let j : Fin n := ⟨y,hyLow⟩
        simpa [twoTypeFreeAge,PartialTypeWithE.ageModel,
          freePairRightAddress,typeAgeIndex,hxLow,hyLow,hxTop,hyTop]
          using (hComp.1 i j t).symm
  unary := by
    intro x hx t
    change x < n+2 ∧ x ≠ n at hx
    by_cases hxTop : x = n+1
    · subst x
      simp [twoTypeFreeAge,PartialTypeWithE.ageModel,
        freePairRightAddress,typeAgeIndex]
    · have hxLow : x < n := by omega
      let i : Fin n := ⟨x,hxLow⟩
      simpa [twoTypeFreeAge,PartialTypeWithE.ageModel,
        freePairRightAddress,typeAgeIndex,hxLow,hxTop]
        using (hComp.2.1 i t).symm
  diagonal := by
    intro x hx t
    change x < n+2 ∧ x ≠ n at hx
    by_cases hxTop : x = n+1
    · subst x
      simp [twoTypeFreeAge,PartialTypeWithE.ageModel,
        freePairRightAddress,typeAgeIndex]
    · have hxLow : x < n := by omega
      let i : Fin n := ⟨x,hxLow⟩
      simpa [twoTypeFreeAge,PartialTypeWithE.ageModel,
        freePairRightAddress,typeAgeIndex,hxLow,hxTop]
        using (hComp.2.2.1 i t).symm

/-- The L-only free union of two compatible genuine source types
is forbidden-free. The genuine E socle is not part of this argument. -/
theorem twoTypeFreeAge_avoids {n db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (T U : PartialTypeWithE n db du dd)
    (hT : IsAdmissibleRawType family
      (⟨n,T⟩ : RawPartialTypeNode db du dd))
    (hU : IsAdmissibleRawType family
      (⟨n,U⟩ : RawPartialTypeNode db du dd))
    (hComp : SameOrdinaryAtCut T U) :
    ∀ bad, bad ∈ family → bad.Avoids (twoTypeFreeAge T U) := by
  let W := twoTypeFreeAge T U
  have hLeft : ∀ bad, bad ∈ family →
      bad.Avoids (W.withoutVertex (n+1)) :=
    (twoTypeFreeAge_left_embeds T U).preserves_avoidance
      family (T.ageModel_avoids family hT)
  have hRight : ∀ bad, bad ∈ family →
      bad.Avoids (W.withoutVertex n) :=
    (twoTypeFreeAge_right_embeds T U hComp).preserves_avoidance
      family (U.ageModel_avoids family hU)
  intro bad hBad
  exact bad.avoids_of_nonedge_pair W n (n+1) (by omega)
    (twoTypeFreeAge_no_cross T U)
    (hRight bad hBad) (hLeft bad hBad)

end SuccessorTree.V10

import SuccessorTree.FatTree.RelativeEA
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Constructions
import Mathlib.Topology.GDelta.Basic

/-!
# Relative EA2: the open-subspace category bridge

An EA2 witness is a nonempty *open* fat-tree neighbourhood C.
Its prescribed regularity conditions concern pullbacks as sets of the
subspace C. The corrected manuscript uses the following general,
application-independent facts:

* a relatively meagre set is meagre after inclusion in the ambient
  space;
* a relatively Baire set in an open subspace is ambient Baire;
* pullbacks of nowhere-dense sets being meagre is enough to obtain
  pullbacks of every meagre set, and hence of every Baire set.

No global continuity or openness of the fat-tree projection is
assumed. The original (false) neighbourhood projection identity is
not used.
-/

namespace SuccessorTree.RelativeCategory

open Filter
open scoped Topology

universe u v

variable {α : Type u} {β : Type v}
variable [TopologicalSpace α] [TopologicalSpace β]

/-- Membership in the image of a subtype set is evaluated at the
unique subtype element over the given ambient point. -/
private theorem image_val_mem_iff
    (C : Set α) (S : Set C) (x : α) (hx : x ∈ C) :
    x ∈ ((Subtype.val : C → α) '' S : Set α) ↔
      (⟨x, hx⟩ : C) ∈ S := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have h : y = (⟨x, hx⟩ : C) := Subtype.ext hxy
    simpa [h] using hy
  · intro hy
    exact ⟨⟨x, hx⟩, hy, rfl⟩

/-- The image of a Baire subset of an **open** subspace has the Baire
property in the ambient topology. Openness is essential here. -/
theorem baire_image_val_of_isOpen
    (C : Set α) (hC : IsOpen C)
    (S : Set C) (hS : BaireMeasurableSet S) :
    BaireMeasurableSet ((Subtype.val : C → α) '' S : Set α) := by
  obtain ⟨O, hO, hEq⟩ := hS.residualEq_isOpen
  let M : Set C := {z | ¬ (z ∈ S ↔ z ∈ O)}
  have hm : IsMeagre M := by
    change Mᶜ ∈ residual C
    simpa [M] using (Filter.eventuallyEqSet_iff.mp hEq)
  have hmAmbient :
      IsMeagre ((Subtype.val : C → α) '' M : Set α) :=
    IsMeagre.image_val hm
  have hSub :
      {x : α | ¬
        (x ∈ ((Subtype.val : C → α) '' S : Set α) ↔
         x ∈ ((Subtype.val : C → α) '' O : Set α))} ⊆
        ((Subtype.val : C → α) '' M : Set α) := by
    intro x hx
    by_cases hxC : x ∈ C
    · refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      change ¬ ((⟨x, hxC⟩ : C) ∈ S ↔ (⟨x, hxC⟩ : C) ∈ O)
      intro hiff
      apply hx
      exact (image_val_mem_iff C S x hxC).trans
        (hiff.trans (image_val_mem_iff C O x hxC).symm)
    · have hnone (A : Set C) :
          x ∉ ((Subtype.val : C → α) '' A : Set α) := by
        rintro ⟨y, hy, hxy⟩
        exact hxC (hxy ▸ y.property)
      exact False.elim (hx
        ⟨fun h => (hnone S h).elim, fun h => (hnone O h).elim⟩)
  have hmDiff :
      IsMeagre {x : α | ¬
        (x ∈ ((Subtype.val : C → α) '' S : Set α) ↔
         x ∈ ((Subtype.val : C → α) '' O : Set α))} :=
    hmAmbient.mono hSub
  have hRes :
      {x : α |
        x ∈ ((Subtype.val : C → α) '' S : Set α) ↔
        x ∈ ((Subtype.val : C → α) '' O : Set α)} ∈ residual α := by
    change {x : α | ¬ ¬
      (x ∈ ((Subtype.val : C → α) '' S : Set α) ↔
       x ∈ ((Subtype.val : C → α) '' O : Set α))} ∈ residual α at hmDiff
    simpa only [not_not] using hmDiff
  have hImageEq :
      ((Subtype.val : C → α) '' S : Set α) =ᵇ
      ((Subtype.val : C → α) '' O : Set α) :=
    Filter.eventuallyEqSet_iff.mpr hRes
  have hOpenImage :
      IsOpen ((Subtype.val : C → α) '' O : Set α) :=
    hC.isOpenMap_subtype_val O hO
  exact hOpenImage.baireMeasurableSet.congr hImageEq.symm

/-- No continuity is needed: if the preimage of each nowhere-dense
set is meagre, then so is the preimage of each meagre set. -/
theorem meagre_preimage_of_nowhereDense
    (f : α → β)
    (hND : ∀ N : Set β, IsNowhereDense N → IsMeagre (f ⁻¹' N))
    (X : Set β) (hX : IsMeagre X) :
    IsMeagre (f ⁻¹' X) := by
  obtain ⟨S, hNDs, hCount, hUnion⟩ :=
    isMeagre_iff_eq_countable_union_isNowhereDense.mp hX
  have hBig : IsMeagre (⋃ N ∈ S, f ⁻¹' N) :=
    isMeagre_biUnion hCount (by
      intro N hNS
      exact hND N (hNDs N hNS))
  apply hBig.mono
  intro x hx
  have hxUnion : f x ∈ ⋃₀ S := by
    change f x ∈ X at hx
    rw [hUnion] at hx
    exact hx
  rcases Set.mem_sUnion.mp hxUnion with ⟨N, hNS, hxN⟩
  exact Set.mem_iUnion.mpr
    ⟨N, Set.mem_iUnion.mpr ⟨hNS, hxN⟩⟩

/-- EA2's two source-side regularity assertions extend from open and
nowhere-dense target sets to all target Baire sets. This is a plain
topological statement, independent of Ramsey spaces. -/
theorem baire_preimage_of_open_and_nowhereDense
    (f : α → β)
    (hOpen : ∀ O : Set β, IsOpen O →
      BaireMeasurableSet (f ⁻¹' O))
    (hND : ∀ N : Set β, IsNowhereDense N →
      IsMeagre (f ⁻¹' N))
    (X : Set β) (hX : BaireMeasurableSet X) :
    BaireMeasurableSet (f ⁻¹' X) := by
  obtain ⟨O, hO, hEq⟩ := hX.residualEq_isOpen
  have hm : IsMeagre {y : β | ¬ (y ∈ X ↔ y ∈ O)} := by
    change {y : β | ¬ (y ∈ X ↔ y ∈ O)}ᶜ ∈ residual β
    simpa only [Set.compl_setOf, not_not] using
      (Filter.eventuallyEqSet_iff.mp hEq)
  have hmp := meagre_preimage_of_nowhereDense f hND _ hm
  have hRes :
      {z : α | z ∈ (f ⁻¹' X) ↔ z ∈ (f ⁻¹' O)} ∈ residual α := by
    change {z : α | ¬ ¬ (f z ∈ X ↔ f z ∈ O)} ∈ residual α at hmp
    have hPlain : {z : α | f z ∈ X ↔ f z ∈ O} ∈ residual α := by
      simpa only [not_not] using hmp
    simpa only [Set.mem_preimage] using hPlain
  have hEqPre : (f ⁻¹' X) =ᵇ (f ⁻¹' O) :=
    Filter.eventuallyEqSet_iff.mpr hRes
  exact (hOpen O hO).congr hEqPre.symm

/-- Relative meagreness already implies ambient meagreness of the
corresponding subset of the original space. -/
theorem meagre_of_relative_preimage
    (C : Set α) (f : α → β) (X : Set β)
    (h : IsMeagre {z : C | f z.1 ∈ X}) :
    IsMeagre (C ∩ f ⁻¹' X) := by
  have himage :
      ((Subtype.val : C → α) '' {z : C | f z.1 ∈ X} : Set α) =
      C ∩ f ⁻¹' X := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hxC, hxX⟩
      exact ⟨⟨x, hxC⟩, hxX, rfl⟩
  rw [← himage]
  exact IsMeagre.image_val h

/-- From the exact *relative* EA2 clauses on an open neighbourhood to
the ambient Baire property of the **restricted** pullback. This does
not assert any global pullback regularity outside that neighbourhood. -/
theorem baire_of_relative_EA2
    (C : Set α) (hC : IsOpen C)
    (f : α → β)
    (hOpen : ∀ O : Set β, IsOpen O →
      BaireMeasurableSet {z : C | f z.1 ∈ O})
    (hND : ∀ N : Set β, IsNowhereDense N →
      IsMeagre {z : C | f z.1 ∈ N})
    (X : Set β) (hX : BaireMeasurableSet X) :
    BaireMeasurableSet (C ∩ f ⁻¹' X) := by
  let fC : C → β := fun z => f z.1
  have hRel : BaireMeasurableSet (fC ⁻¹' X) :=
    baire_preimage_of_open_and_nowhereDense fC
      (by intro O hO; exact hOpen O hO)
      (by intro N hN; exact hND N hN) X hX
  have himage :
      ((Subtype.val : C → α) '' (fC ⁻¹' X) : Set α) =
      C ∩ f ⁻¹' X := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.property, hz⟩
    · rintro ⟨hxC, hxX⟩
      exact ⟨⟨x, hxC⟩, hxX, rfl⟩
  rw [← himage]
  exact baire_image_val_of_isOpen C hC (fC ⁻¹' X) hRel

/-- The *nowhere-dense* part of relative EA2 also implies that the
restricted pullback of an arbitrary meagre target is ambient meagre. -/
theorem meagre_of_relative_EA2
    (C : Set α) (f : α → β)
    (hND : ∀ N : Set β, IsNowhereDense N →
      IsMeagre {z : C | f z.1 ∈ N})
    (X : Set β) (hX : IsMeagre X) :
    IsMeagre (C ∩ f ⁻¹' X) := by
  let fC : C → β := fun z => f z.1
  have hRel : IsMeagre (fC ⁻¹' X) :=
    meagre_preimage_of_nowhereDense fC
      (by intro N hN; exact hND N hN) X hX
  exact meagre_of_relative_preimage C f X hRel

end SuccessorTree.RelativeCategory

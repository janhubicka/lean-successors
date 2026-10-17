import SuccessorTree.FatTree.CategoryTests

/-!
# The exact image criterion for EA2 on a fat-tree witness

The fat-tree Ellentuck theorem makes every meagre set nowhere dense.
This property passes to open subspaces. On such a space a Baire set
with empty interior is meagre. Consequently EA2 on one fixed fat
witness is equivalent to Baire pullbacks of open target sets together
with somewhere-dense images of all nonempty relative open sets.

Continuity is not needed for this equivalence. The image test may also
be restricted to the nonempty fat basic neighbourhoods contained in
the witness, including neighbourhoods with a deeper stem. The
fixed-stem lifting assertion in EA1 is not that all-basic image test.
-/

namespace SuccessorTree.RelativeCategory

open Filter
open scoped Topology

universe u v

variable {α : Type u} {β : Type v}
variable [TopologicalSpace α] [TopologicalSpace β]

/-- In a space where every meagre set is nowhere dense, a Baire set
with empty interior is meagre. -/
theorem meagre_of_baire_emptyInterior
    (hSmall : ∀ M : Set α, IsMeagre M → IsNowhereDense M)
    (A : Set α) (hA : BaireMeasurableSet A)
    (hInt : interior A = ∅) : IsMeagre A := by
  classical
  obtain ⟨O, hO, hEq⟩ := hA.residualEq_isOpen
  let M : Set α := {x | ¬ (x ∈ A ↔ x ∈ O)}
  have hM : IsMeagre M := by
    have hRes : {x : α | x ∈ A ↔ x ∈ O} ∈ residual α := by
      have h := Filter.eventuallyEqSet_iff.mp hEq
      change {x : α | x ∈ A ↔ x ∈ O} ∈ residual α at h
      exact h
    change Mᶜ ∈ residual α
    have hSet : Mᶜ = {x : α | x ∈ A ↔ x ∈ O} := by
      ext x
      simp [M]
    rwa [hSet]
  have hND : IsNowhereDense M := hSmall M hM
  have hDiffSub : O \ closure M ⊆ A := by
    intro x hx
    by_contra hxA
    apply hx.2
    apply subset_closure
    change ¬ (x ∈ A ↔ x ∈ O)
    intro hiff
    exact hxA (hiff.mpr hx.1)
  have hOSub : O ⊆ closure M := by
    intro x hx
    by_contra hxM
    have hxInt : x ∈ interior A :=
      interior_maximal hDiffSub (hO.sdiff isClosed_closure) ⟨hx, hxM⟩
    simp only [hInt, Set.mem_empty_iff_false] at hxInt
  have hOEmpty : O = ∅ := by
    apply Set.eq_empty_of_subset_empty
    intro x hx
    have hxInt : x ∈ interior (closure M) :=
      interior_maximal hOSub hO hx
    exact hND ▸ hxInt
  apply hM.mono
  intro x hx
  change ¬ (x ∈ A ↔ x ∈ O)
  intro hiff
  have hxO : x ∈ O := hiff.mp hx
  simp only [hOEmpty, Set.mem_empty_iff_false] at hxO

/-- The property that all meagre sets are nowhere dense passes to an
open subspace. -/
theorem meagre_nowhereDense_open_subtype
    (hSmall : ∀ M : Set α, IsMeagre M → IsNowhereDense M)
    (C : Set α) (hC : IsOpen C)
    (A : Set C) (hA : IsMeagre A) : IsNowhereDense A := by
  let j : C → α := Subtype.val
  have hND : IsNowhereDense (j '' A) :=
    hSmall (j '' A) (IsMeagre.image_val hA)
  have hDense : Dense (j ⁻¹' (closure (j '' A))ᶜ) :=
    ((isClosed_isNowhereDense_iff_compl.mp
      ⟨isClosed_closure, hND.closure⟩).2).preimage hC.isOpenMap_subtype_val
  have hClosed : IsClosed (j ⁻¹' closure (j '' A)) :=
    isClosed_closure.preimage continuous_subtype_val
  have hPreND : IsNowhereDense (j ⁻¹' closure (j '' A)) := by
    apply (isClosed_isNowhereDense_iff_compl.mpr ?_).2
    refine ⟨hClosed.isOpen_compl, ?_⟩
    simpa only [Set.preimage_compl] using hDense
  apply IsNowhereDense.mono ?_ hPreND
  intro x hx
  exact subset_closure ⟨x, hx, rfl⟩

/-- For a source where meagre sets are nowhere dense, the two EA2
tests are exactly the open-pullback test and the somewhere-dense
image test. The map need not be continuous. -/
theorem open_and_closedNowhereDense_iff_open_and_image
    (hSmall : ∀ M : Set α, IsMeagre M → IsNowhereDense M)
    (q : α → β) :
    ((∀ O : Set β, IsOpen O →
        BaireMeasurableSet (q ⁻¹' O)) ∧
      (∀ N : Set β, IsClosed N → IsNowhereDense N →
        IsMeagre (q ⁻¹' N))) ↔
    ((∀ O : Set β, IsOpen O →
        BaireMeasurableSet (q ⁻¹' O)) ∧
      (∀ V : Set α, IsOpen V → V.Nonempty →
        ¬ IsNowhereDense (q '' V))) := by
  constructor
  · rintro ⟨hOpen, hPull⟩
    refine ⟨hOpen, ?_⟩
    intro V hV hne hImageND
    have hPreND : IsNowhereDense (q ⁻¹' closure (q '' V)) :=
      hSmall _ (hPull _ isClosed_closure hImageND.closure)
    obtain ⟨x, hx⟩ := hne
    have hSub : V ⊆ closure (q ⁻¹' closure (q '' V)) := by
      intro z hz
      apply subset_closure
      exact subset_closure ⟨z, hz, rfl⟩
    have hxInt : x ∈ interior (closure (q ⁻¹' closure (q '' V))) :=
      interior_maximal hSub hV hx
    have hxEmpty : x ∈ (∅ : Set α) := hPreND ▸ hxInt
    exact hxEmpty
  · rintro ⟨hOpen, hImage⟩
    refine ⟨hOpen, ?_⟩
    intro N hClosed hND
    have hBaire : BaireMeasurableSet (q ⁻¹' N) := by
      have h := (hOpen Nᶜ hClosed.isOpen_compl).compl
      simpa only [Set.preimage_compl, compl_compl] using h
    apply meagre_of_baire_emptyInterior hSmall _ hBaire
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    apply hImage (interior (q ⁻¹' N)) isOpen_interior ⟨x, hx⟩
    apply IsNowhereDense.mono ?_ hND
    rintro y ⟨z, hz, rfl⟩
    exact (interior_subset : interior (q ⁻¹' N) ⊆ q ⁻¹' N) hz

end SuccessorTree.RelativeCategory

namespace SuccessorTree.SMTree.FatTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable (H : SMTree S)

local instance : TopologicalSpace (FatTree H) :=
  (approximationSystem H).ellentuckTopology

local instance : TopologicalSpace (MMap H) :=
  (ramseyApproximationSystem H).ellentuckTopology

/-- In the actual fat-tree Ellentuck topology, every meagre set is
nowhere dense. Fat Ramsey nullity gives an open refinement avoiding
it inside every nonempty basic neighbourhood. -/
theorem fatTree_isNowhereDense_of_isMeagre
    (A : Set (FatTree H)) (hA : IsMeagre A) : IsNowhereDense A := by
  let R := approximationSystem H
  letI : TopologicalSpace R.Point := R.ellentuckTopology
  change interior (closure A) = (∅ : Set (FatTree H))
  apply Set.eq_empty_of_subset_empty
  intro X hX
  have hOpen : R.IsEllentuckOpen (interior (closure A)) := by
    exact (R.isOpen_ellentuck_iff _).mp isOpen_interior
  obtain ⟨n, a, U, hXU, hSub⟩ := hOpen hX
  obtain ⟨V, hVU, hDis⟩ :=
    (fatTreeEllentuck H).2 A hA a U ⟨X, hXU⟩
  have hV : V ∈ R.neighborhood a V := ⟨R.le_refl V, hVU.2⟩
  have hVClosure : V ∈ closure A := interior_subset (hSub hVU)
  obtain ⟨W, hW, hWA⟩ :=
    (mem_closure_iff.mp hVClosure) (R.neighborhood a V)
      (R.isOpen_neighborhood a V) hV
  exact False.elim ((Set.disjoint_left.mp hDis) hW hWA)

/-- Meagreness and nowhere denseness coincide in the fat-tree
Ellentuck topology. -/
theorem fatTree_isMeagre_iff_isNowhereDense
    (A : Set (FatTree H)) : IsMeagre A ↔ IsNowhereDense A :=
  ⟨fatTree_isNowhereDense_of_isMeagre H A, fun h => h.isMeagre⟩

/-- The same coincidence holds in every relative fat-tree witness. -/
theorem fatWitness_isMeagre_iff_isNowhereDense
    {n : Nat} (a : (approximationSystem H).Approx n)
    (U : FatTree H)
    (A : Set ((approximationSystem H).neighborhood a U)) :
    IsMeagre A ↔ IsNowhereDense A := by
  constructor
  · intro hA
    exact SuccessorTree.RelativeCategory.meagre_nowhereDense_open_subtype
      (fatTree_isNowhereDense_of_isMeagre H)
      ((approximationSystem H).neighborhood a U)
      ((approximationSystem H).isOpen_neighborhood a U) A hA
  · intro hA
    exact hA.isMeagre

/-- A relatively Baire set in a fat witness with empty relative
interior is meagre there. -/
theorem fatWitness_meagre_of_baire_emptyInterior
    {n : Nat} (a : (approximationSystem H).Approx n)
    (U : FatTree H)
    (A : Set ((approximationSystem H).neighborhood a U))
    (hA : BaireMeasurableSet A) (hInt : interior A = ∅) :
    IsMeagre A :=
  SuccessorTree.RelativeCategory.meagre_of_baire_emptyInterior
    (fun M hM => (fatWitness_isMeagre_iff_isNowhereDense H a U M).mp hM)
    A hA hInt

/-- Exact EA2 on its fixed witness: retain the open-pullback Baire
condition and test somewhere-dense images of every nonempty relative
open set. No continuity hypothesis is required. -/
theorem hasRelativeEA2Closed_iff_open_and_image
    {n : Nat} (a : (approximationSystem H).Approx n)
    (U : FatTree H) (rho : FatTree H → MMap H) :
    HasRelativeEA2Closed H a U rho ↔
      let C : Set (FatTree H) := (approximationSystem H).neighborhood a U
      (∀ O : Set (MMap H), IsOpen O →
        BaireMeasurableSet {W : C | rho W.1 ∈ O}) ∧
      (∀ V : Set C, IsOpen V → V.Nonempty →
        ¬ IsNowhereDense ((fun W : C => rho W.1) '' V)) := by
  exact SuccessorTree.RelativeCategory.open_and_closedNowhereDense_iff_open_and_image
    (fun M hM => (fatWitness_isMeagre_iff_isNowhereDense H a U M).mp hM)
    (fun W : (approximationSystem H).neighborhood a U => rho W.1)

/-- The same exact image criterion for the original all-nowhere-dense
formulation of EA2. -/
theorem hasRelativeEA2_iff_open_and_image
    {n : Nat} (a : (approximationSystem H).Approx n)
    (U : FatTree H) (rho : FatTree H → MMap H) :
    HasRelativeEA2 H a U rho ↔
      let C : Set (FatTree H) := (approximationSystem H).neighborhood a U
      (∀ O : Set (MMap H), IsOpen O →
        BaireMeasurableSet {W : C | rho W.1 ∈ O}) ∧
      (∀ V : Set C, IsOpen V → V.Nonempty →
        ¬ IsNowhereDense ((fun W : C => rho W.1) '' V)) :=
  (hasRelativeEA2_iff_closed H a U rho).trans
    (hasRelativeEA2Closed_iff_open_and_image H a U rho)

/-- Only the image clause admits this immediate basis reduction: test
every nonempty fat basic neighbourhood contained in the original
witness, including those with a deeper stem. -/
theorem relativeImage_test_iff_basic
    {n : Nat} (a : (approximationSystem H).Approx n)
    (U : FatTree H) (rho : FatTree H → MMap H) :
    let C : Set (FatTree H) := (approximationSystem H).neighborhood a U
    (∀ V : Set C, IsOpen V → V.Nonempty →
      ¬ IsNowhereDense ((fun W : C => rho W.1) '' V)) ↔
    (∀ {m : Nat} (b : (approximationSystem H).Approx m) (W : FatTree H),
      ((approximationSystem H).neighborhood b W).Nonempty →
      (approximationSystem H).neighborhood b W ⊆ C →
      ¬ IsNowhereDense (rho '' (approximationSystem H).neighborhood b W)) := by
  let R := approximationSystem H
  let C : Set (FatTree H) := R.neighborhood a U
  change
    (∀ V : Set C, IsOpen V → V.Nonempty →
      ¬ IsNowhereDense ((fun W : C => rho W.1) '' V)) ↔ _
  constructor
  · intro hImage m b W hne hSub hND
    let V : Set C := (Subtype.val : C → FatTree H) ⁻¹' R.neighborhood b W
    have hVOpen : IsOpen V :=
      (R.isOpen_neighborhood b W).preimage continuous_subtype_val
    obtain ⟨X, hX⟩ := hne
    have hVne : V.Nonempty := ⟨⟨X, hSub hX⟩, hX⟩
    apply hImage V hVOpen hVne
    apply IsNowhereDense.mono ?_ hND
    rintro Y ⟨X, hX, rfl⟩
    exact ⟨X.1, hX, rfl⟩
  · intro hBasic V hV hne hND
    have hImageOpen : IsOpen ((Subtype.val : C → FatTree H) '' V) :=
      (R.isOpen_neighborhood a U).isOpenMap_subtype_val V hV
    have hOpen : R.IsEllentuckOpen ((Subtype.val : C → FatTree H) '' V) :=
      (R.isOpen_ellentuck_iff _).mp hImageOpen
    obtain ⟨X, hX⟩ := hne
    obtain ⟨m, b, W, hXW, hSub⟩ := hOpen ⟨X, hX, rfl⟩
    have hSubC : R.neighborhood b W ⊆ C := by
      intro Z hZ
      obtain ⟨z, hz, hzZ⟩ := hSub hZ
      exact hzZ ▸ z.property
    apply hBasic b W ⟨X.1, hXW⟩ hSubC
    apply IsNowhereDense.mono ?_ hND
    rintro Y ⟨Z, hZ, rfl⟩
    obtain ⟨z, hz, hzZ⟩ := hSub hZ
    exact ⟨z, hz, congrArg rho hzZ⟩

end SuccessorTree.SMTree.FatTree

import SuccessorTree.FatTree.Section4Conditional

/-!
# Equivalent tests for the relative EA2 category condition

EA2 may test closed nowhere-dense target sets: taking the closure
recovers the test on an arbitrary nowhere-dense set. The resulting
condition is equivalent to preservation of meagreness under pullback.
Together with Baire pullbacks of all open target sets, it is equivalent
to preserving both the Baire property and meagreness under pullback.

These equivalences concern a fixed map and its fixed source space.
They do not assert necessity of EA2 for a Ramsey theorem, nor allow
the source witness to change between the two clauses.
-/

namespace SuccessorTree.RelativeCategory

universe u v

variable {α : Type u} {β : Type v}
variable [TopologicalSpace α] [TopologicalSpace β]

/-- Testing closed nowhere-dense targets is equivalent to testing
all nowhere-dense targets. No continuity assumption is needed. -/
theorem nowhereDense_preimage_test_iff_closed (f : α → β) :
    (∀ N : Set β, IsNowhereDense N → IsMeagre (f ⁻¹' N)) ↔
      (∀ N : Set β, IsClosed N → IsNowhereDense N →
        IsMeagre (f ⁻¹' N)) := by
  constructor
  · intro h N _ hN
    exact h N hN
  · intro h N hN
    apply (h (closure N) isClosed_closure hN.closure).mono
    intro x hx
    exact subset_closure hx

/-- Closed nowhere-dense tests suffice for pullbacks of every meagre
target set. This is the category clause used by the manuscript. -/
theorem meagre_preimage_of_closedNowhereDense
    (f : α → β)
    (hClosedND : ∀ N : Set β, IsClosed N → IsNowhereDense N →
      IsMeagre (f ⁻¹' N))
    (X : Set β) (hX : IsMeagre X) :
    IsMeagre (f ⁻¹' X) :=
  meagre_preimage_of_nowhereDense f
    ((nowhereDense_preimage_test_iff_closed f).mpr hClosedND) X hX

/-- The closed nowhere-dense test is exactly meagre pullback
preservation, rather than a stronger regularity assumption. -/
theorem closedNowhereDense_preimage_test_iff_meagre (f : α → β) :
    (∀ N : Set β, IsClosed N → IsNowhereDense N →
      IsMeagre (f ⁻¹' N)) ↔
      (∀ X : Set β, IsMeagre X → IsMeagre (f ⁻¹' X)) := by
  constructor
  · intro h X hX
    exact meagre_preimage_of_closedNowhereDense f h X hX
  · intro h N _ hN
    exact h N hN.isMeagre

/-- The manuscript's two tests imply Baire pullback preservation. -/
theorem baire_preimage_of_open_and_closedNowhereDense
    (f : α → β)
    (hOpen : ∀ O : Set β, IsOpen O →
      BaireMeasurableSet (f ⁻¹' O))
    (hClosedND : ∀ N : Set β, IsClosed N → IsNowhereDense N →
      IsMeagre (f ⁻¹' N))
    (X : Set β) (hX : BaireMeasurableSet X) :
    BaireMeasurableSet (f ⁻¹' X) :=
  baire_preimage_of_open_and_nowhereDense f hOpen
    ((nowhereDense_preimage_test_iff_closed f).mpr hClosedND) X hX

/-- On one fixed source witness, the two EA2 tests are exactly
preservation of both Baire sets and meagre sets under pullback. -/
theorem open_and_closedNowhereDense_iff_baire_and_meagre
    (f : α → β) :
    ((∀ O : Set β, IsOpen O →
        BaireMeasurableSet (f ⁻¹' O)) ∧
      (∀ N : Set β, IsClosed N → IsNowhereDense N →
        IsMeagre (f ⁻¹' N))) ↔
    ((∀ X : Set β, BaireMeasurableSet X →
        BaireMeasurableSet (f ⁻¹' X)) ∧
      (∀ X : Set β, IsMeagre X → IsMeagre (f ⁻¹' X))) := by
  constructor
  · rintro ⟨hOpen, hClosedND⟩
    exact ⟨baire_preimage_of_open_and_closedNowhereDense f hOpen hClosedND,
      meagre_preimage_of_closedNowhereDense f hClosedND⟩
  · rintro ⟨hBaire, hMeagre⟩
    exact ⟨fun O hO => hBaire O hO.baireMeasurableSet,
      fun N _ hN => hMeagre N hN.isMeagre⟩

/-- A continuous map whose nonempty open images are somewhere dense
pulls closed nowhere-dense targets back to nowhere-dense source sets.
The image itself need not have nonempty interior. -/
theorem closedNowhereDense_preimage_of_continuous_and_image
    (f : α → β) (hCont : Continuous f)
    (hImage : ∀ U : Set α, IsOpen U → U.Nonempty →
      ¬ IsNowhereDense (f '' U))
    (N : Set β) (hClosed : IsClosed N) (hND : IsNowhereDense N) :
    IsNowhereDense (f ⁻¹' N) := by
  apply (hClosed.preimage hCont).isNowhereDense_iff.mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  apply hImage (interior (f ⁻¹' N)) isOpen_interior ⟨x, hx⟩
  apply IsNowhereDense.mono ?_ hND
  rintro y ⟨z, hz, rfl⟩
  exact interior_subset hz

/-- The weakened geometric sufficient condition printed after EA2:
continuity and somewhere-dense images of nonempty open source sets. -/
theorem open_and_closedNowhereDense_of_continuous_and_image
    (f : α → β) (hCont : Continuous f)
    (hImage : ∀ U : Set α, IsOpen U → U.Nonempty →
      ¬ IsNowhereDense (f '' U)) :
    (∀ O : Set β, IsOpen O → BaireMeasurableSet (f ⁻¹' O)) ∧
      (∀ N : Set β, IsClosed N → IsNowhereDense N →
        IsMeagre (f ⁻¹' N)) := by
  constructor
  · intro O hO
    exact (hO.preimage hCont).baireMeasurableSet
  · intro N hClosed hND
    exact (closedNowhereDense_preimage_of_continuous_and_image
      f hCont hImage N hClosed hND).isMeagre

end SuccessorTree.RelativeCategory

namespace SuccessorTree.SMTree.FatTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable (H : SMTree S)

/-- The literal source EA2 test after restricting the second clause
to closed nowhere-dense sets. The source witness is unchanged. -/
def HasRelativeEA2Closed {n : Nat}
    (a : (approximationSystem H).Approx n)
    (U : FatTree H) (rho : FatTree H → MMap H) : Prop :=
  let C : Set (FatTree H) := (approximationSystem H).neighborhood a U
  (∀ O : Set (MMap H),
      @IsOpen (MMap H) (ramseyApproximationSystem H).ellentuckTopology O →
      @BaireMeasurableSet C
        (TopologicalSpace.induced (Subtype.val : C → FatTree H)
          (approximationSystem H).ellentuckTopology)
        {W : C | rho W.1 ∈ O}) ∧
  (∀ N : Set (MMap H),
      @IsClosed (MMap H) (ramseyApproximationSystem H).ellentuckTopology N →
      @IsNowhereDense (MMap H) (ramseyApproximationSystem H).ellentuckTopology N →
      @_root_.IsMeagre C
        (TopologicalSpace.induced (Subtype.val : C → FatTree H)
          (approximationSystem H).ellentuckTopology)
        {W : C | rho W.1 ∈ N})

/-- The old all-nowhere-dense and the reduced closed-nowhere-dense
formulations of EA2 are equivalent on the same relative witness. -/
theorem hasRelativeEA2_iff_closed {n : Nat}
    (a : (approximationSystem H).Approx n)
    (U : FatTree H) (rho : FatTree H → MMap H) :
    HasRelativeEA2 H a U rho ↔ HasRelativeEA2Closed H a U rho := by
  let C : Set (FatTree H) := (approximationSystem H).neighborhood a U
  letI : TopologicalSpace (FatTree H) :=
    (approximationSystem H).ellentuckTopology
  letI : TopologicalSpace (MMap H) :=
    (ramseyApproximationSystem H).ellentuckTopology
  change
    ((∀ O : Set (MMap H), IsOpen O →
        BaireMeasurableSet {W : C | rho W.1 ∈ O}) ∧
      (∀ N : Set (MMap H), IsNowhereDense N →
        _root_.IsMeagre {W : C | rho W.1 ∈ N})) ↔
    ((∀ O : Set (MMap H), IsOpen O →
        BaireMeasurableSet {W : C | rho W.1 ∈ O}) ∧
      (∀ N : Set (MMap H), IsClosed N → IsNowhereDense N →
        _root_.IsMeagre {W : C | rho W.1 ∈ N}))
  constructor
  · rintro ⟨hOpen, hND⟩
    exact ⟨hOpen, fun N _ hN => hND N hN⟩
  · rintro ⟨hOpen, hClosedND⟩
    refine ⟨hOpen, ?_⟩
    exact (SuccessorTree.RelativeCategory.nowhereDense_preimage_test_iff_closed
      (fun W : C => rho W.1)).mpr hClosedND

end SuccessorTree.SMTree.FatTree

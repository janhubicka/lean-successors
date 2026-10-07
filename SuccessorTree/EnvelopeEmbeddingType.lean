import SuccessorTree.EnvelopeUniqueness
import Mathlib.Tactic

/-!
# Choice-independence of the embedding type: one stage

At an interesting stage the map is unchanged.  At a noninteresting stage the
only issue is whether two choices of the one-level factor give the same inverse
of X.  The common outer embedding type is contained in the parameter-closed
pullback closures for both outer maps; local inverse uniqueness on their
intersection gives the result.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Intersections preserve parameter closure. -/
theorem ParameterClosedOver.inter
    {A B : Set T} {J : Set Nat}
    (hA : ParameterClosedOver S A J)
    (hB : ParameterClosedOver S B J) :
    ParameterClosedOver S (A ∩ B) J := by
  intro a ha i hi hia p c hs x hx
  exact ⟨hA ha.1 hi hia hs hx, hB ha.2 hi hia hs hx⟩

/-- The pullback closure occurring at stage i+1. -/
def stagePullback
    (S : STree T Label) (G : ShapeMap S)
    (I : Set Nat) (X : Set T) : Set T :=
  G ⁻¹' closure S I X

/-- A common embedding type is contained in the intersection of the two
pullback closures. -/
theorem commonType_subset_pullback_inter
    (G E : ShapeMap S) (I : Set Nat) (X : Set T)
    (hType : G ⁻¹' X = E ⁻¹' X) :
    G ⁻¹' X ⊆
      stagePullback S G I X ∩ stagePullback S E I X := by
  intro y hy
  refine ⟨?_, ?_⟩
  · exact subset_closure S I X hy
  · change E y ∈ closure S I X
    have hyE : E y ∈ X := by
      have : y ∈ E ⁻¹' X := by
        rw [← hType]
        exact hy
      exact this
    exact subset_closure S I X hyE

/-- One-step choice independence at a noninteresting level. -/
theorem embeddingType_noninteresting_choice_independent
    (H : SMTree S) (hE1 : OneLevelPullback H)
    (X : Set T) (ell i : Nat)
    (hXbound : X ⊆ levelLe ell)
    (I : Set Nat)
    (G G' D E : MMap H)
    (hInvG : StageInvariant H X ell (i + 1) I G)
    (hInvG' : StageInvariant H X ell (i + 1) I G')
    (hOuterType : G.map ⁻¹' X = G'.map ⁻¹' X)
    (hDskip : D.map.SkipsOnly i)
    (hEskip : E.map.SkipsOnly i)
    (hno : ∀ ⦃x : T⦄, x ∈ closure S I X → LevelTree.lev x ≠ i)
    (hDcross :
      ∀ ⦃c : T⦄, c ∈ closure S I X →
        ∀ (hic : i < LevelTree.lev c),
          D (LevelTree.ancestor c i (Nat.le_of_lt hic)) =
            LevelTree.ancestor c (i + 1) (Nat.succ_le_iff.mpr hic))
    (hEcross :
      ∀ ⦃c : T⦄, c ∈ closure S I X →
        ∀ (hic : i < LevelTree.lev c),
          E (LevelTree.ancestor c i (Nat.le_of_lt hic)) =
            LevelTree.ancestor c (i + 1) (Nat.succ_le_iff.mpr hic)) :
    (MMap.comp H G D).map ⁻¹' X =
      (MMap.comp H G' E).map ⁻¹' X := by
  let C : Set T := closure S I X
  let ZG : Set T := stagePullback S G.map I X
  let ZG' : Set T := stagePullback S G'.map I X
  let Z : Set T := ZG ∩ ZG'
  have hBound : C ⊆ levelLe ell :=
    closure_subset_levelLe I X ell hXbound
  have hThroughG : FixesThrough G.map i :=
    fixesThrough_of_fixesBelow_succ H G i hInvG.2.1
  have hThroughG' : FixesThrough G'.map i :=
    fixesThrough_of_fixesBelow_succ H G' i hInvG'.2.1
  have hIndexedG :
      ∀ ⦃q : Nat⦄, q ∈ G.map.levelRange →
        i < q → q ≤ ell → q ∈ I := by
    intro q hq hiq hqell
    rw [hInvG.2.2]
    exact ⟨hq, by omega, hqell⟩
  have hIndexedG' :
      ∀ ⦃q : Nat⦄, q ∈ G'.map.levelRange →
        i < q → q ≤ ell → q ∈ I := by
    intro q hq hiq hqell
    rw [hInvG'.2.2]
    exact ⟨hq, by omega, hqell⟩
  have hParamG : ParameterClosedOver S ZG {j | i < j} := by
    exact preimage_parameterClosed_of_bounded_indexed
      H G.map i ell C I (closure_parameterClosed S I X)
      hBound hIndexedG
  have hParamG' : ParameterClosedOver S ZG' {j | i < j} := by
    exact preimage_parameterClosed_of_bounded_indexed
      H G'.map i ell C I (closure_parameterClosed S I X)
      hBound hIndexedG'
  have hParamZ : ParameterClosedOver S Z {j | i < j} :=
    hParamG.inter hParamG'
  have hNoG : ∀ ⦃z : T⦄, z ∈ ZG → LevelTree.lev z ≠ i := by
    exact preimage_has_no_level_of_fixesThrough G.map i hThroughG hno
  have hNoZ : ∀ ⦃z : T⦄, z ∈ Z → LevelTree.lev z ≠ i := by
    intro z hz
    exact hNoG hz.1
  have hCrossDZ :
      ∀ ⦃z : T⦄, z ∈ Z → ∀ (hiz : i < LevelTree.lev z),
        D (LevelTree.ancestor z i (Nat.le_of_lt hiz)) =
          LevelTree.ancestor z (i + 1) (Nat.succ_le_iff.mpr hiz) := by
    intro z hz hiz
    exact pullback_crossing_of_extension
      G.map D.map i hThroughG C hDcross hz.1 hiz
  have hCrossEZ :
      ∀ ⦃z : T⦄, z ∈ Z → ∀ (hiz : i < LevelTree.lev z),
        E (LevelTree.ancestor z i (Nat.le_of_lt hiz)) =
          LevelTree.ancestor z (i + 1) (Nat.succ_le_iff.mpr hiz) := by
    intro z hz hiz
    exact pullback_crossing_of_extension
      G'.map E.map i hThroughG' C hEcross hz.2 hiz
  have hRangeD : ZG ⊆ Set.range D := by
    exact preimage_subset_range_of_bounded_indexed
      H G.map D.map i ell hThroughG hDskip (hE1 D i hDskip)
      C I (closure_parameterClosed S I X) hBound hIndexedG hno hDcross
  have hRangeE : ZG' ⊆ Set.range E := by
    exact preimage_subset_range_of_bounded_indexed
      H G'.map E.map i ell hThroughG' hEskip (hE1 E i hEskip)
      C I (closure_parameterClosed S I X) hBound hIndexedG' hno hEcross
  have hTypeInZ :
      G.map ⁻¹' X ⊆ Z := by
    exact commonType_subset_pullback_inter G.map G'.map I X hOuterType
  ext x
  constructor
  · intro hx
    have hy : D x ∈ G.map ⁻¹' X := hx
    have hyZ : D x ∈ Z := hTypeInZ hy
    obtain ⟨e, he⟩ := hRangeE hyZ.2
    have hxe : x = e := by
      apply oneLevel_preimage_unique_below
        H D.map E.map i hDskip hEskip Z hParamZ hNoZ hCrossDZ hCrossEZ
        hyZ le_rfl (hNoZ hyZ) rfl he
    subst e
    change G' (E x) ∈ X
    have hyOuter : D x ∈ G'.map ⁻¹' X := by
      rw [← hOuterType]
      exact hy
    simpa [he] using hyOuter
  · intro hx
    have hy : E x ∈ G'.map ⁻¹' X := hx
    have hyG : E x ∈ G.map ⁻¹' X := by
      rw [hOuterType]
      exact hy
    have hyZ : E x ∈ Z := hTypeInZ hyG
    obtain ⟨d, hd⟩ := hRangeD hyZ.1
    have hdx : d = x := by
      apply oneLevel_preimage_unique_below
        H D.map E.map i hDskip hEskip Z hParamZ hNoZ hCrossDZ hCrossEZ
        hyZ le_rfl (hNoZ hyZ) hd rfl
    subst d
    change G (D x) ∈ X
    simpa [hd] using hyG

end Envelope
end SMTree
end SuccessorTree

import SuccessorTree.FatTree.BorelCone
import SuccessorTree.FatTree.Section4Conditional
import SuccessorTree.FatTree.CategoryTests
import SuccessorTree.FatTree.ProjectionTransfer
import SuccessorTree.RamseySpace.Nonempty

/-!
# Source statements for the relative Borel and Ellentuck theorems

The lower-level transfer theorems allow an arbitrary projection, family of
pure refinements and family of cones. This module fixes all three to the
objects in the manuscript: rho_F(U) = F ∘ associatedMap(U), the direct
right-composition neighbourhood [f,F'], and the original protected depth
of f in F. EA1 uses the prescribed F' = rho_F(V), not an arbitrary map
whose cone happens to be covered. EA2 is imposed on the same fat witness.

Approximation indices count source levels. For a nonempty map stem, Lean's
depth is one more than the manuscript's last-source-level convention;
depth zero corresponds to the manuscript's empty-stem depth -1. No direct
shape-map A.3(2) or AbstractRamseySpace instance is used.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable (H : SMTree S)

/-- Left composition respects equality of genuine finite map stems. -/
theorem ramseyApprox_comp_eq_of_eq
    (F G K : MMap H) (n : Nat)
    (h : ramseyApprox H n G = ramseyApprox H n K) :
    ramseyApprox H n (MMap.comp H F G) =
      ramseyApprox H n (MMap.comp H F K) := by
  cases n with
  | zero => rfl
  | succ n =>
      apply Subtype.ext
      funext x
      have hval := congrArg Subtype.val h
      have hx := congrFun hval x
      change G x.1 = K x.1 at hx
      change F (G x.1) = F (K x.1)
      exact congrArg (fun y : T => F y) hx

/-- The finite map F_x carried by a fat stem x. Any infinite extension
can be used, because the projection respects finite prefixes. -/
noncomputable def carriedApprox {n : Nat}
    (a : (approximationSystem H).Approx n) : RamseyApprox H n :=
  ramseyApprox H n (associatedMap H
    (Classical.choose ((approximationSystem H).approx_surjective n a)))

/-- Projecting an extension of a finite fat stem recovers its carried map. -/
theorem associatedMap_approx_eq_carriedApprox
    {n : Nat} (a : (approximationSystem H).Approx n)
    (W : FatTree H)
    (hW : (approximationSystem H).approx n W = a) :
    ramseyApprox H n (associatedMap H W) = carriedApprox H a := by
  let U : FatTree H :=
    Classical.choose ((approximationSystem H).approx_surjective n a)
  have hU : (approximationSystem H).approx n U = a :=
    Classical.choose_spec ((approximationSystem H).approx_surjective n a)
  have hPrefix : W.initialSegment H n = U.initialSegment H n :=
    congrArg Subtype.val (hW.trans hU.symm)
  exact projectionRespectsPrefixes H W U n hPrefix

/-- Left composition of a realized finite map stem. The definition is
independent of the chosen total representative. -/
noncomputable def leftComposeApprox (F : MMap H) {n : Nat}
    (g : RamseyApprox H n) : RamseyApprox H n :=
  ramseyApprox H n (MMap.comp H F
    (Classical.choose ((ramseyApproximationSystem H).approx_surjective n g)))

theorem ramseyApprox_comp_eq_leftComposeApprox
    (F G : MMap H) {n : Nat} (g : RamseyApprox H n)
    (hG : ramseyApprox H n G = g) :
    ramseyApprox H n (MMap.comp H F G) = leftComposeApprox H F g := by
  let K : MMap H :=
    Classical.choose ((ramseyApproximationSystem H).approx_surjective n g)
  have hK : ramseyApprox H n K = g :=
    Classical.choose_spec ((ramseyApproximationSystem H).approx_surjective n g)
  exact ramseyApprox_comp_eq_of_eq H F G K n (hG.trans hK.symm)

/-- Quantification over finite depths is exactly quantification over
nonempty direct-monoid neighbourhoods; only direct A.3(1) is needed. -/
theorem source_finiteDepth_iff_nonempty
    {n : Nat} (f : (ramseyApproximationSystem H).Approx n)
    (F : MMap H) :
    (∃ d, (ramseyFinitization H).HasDepth f F d) ↔
      ((ramseyApproximationSystem H).neighborhood f F).Nonempty := by
  constructor
  · rintro ⟨d, hd⟩
    exact fusionNeighborhood_nonempty H f F hd
      ((ramseyApproximationSystem H).self_mem_levelNeighborhood d F)
  · rintro ⟨G, hG⟩
    exact (ramseyFinitization H).exists_hasDepth_of_mem_neighborhood hG

/-- For f = (F ∘ G)|T(≤n), the formal approximation depth is exactly
G's last image level plus one. This is the manuscript's numeric depth
convention with the empty approximation counted as length zero. -/
theorem source_depth_comp (F G : MMap H) (n : Nat) :
    (ramseyFinitization H).HasDepth
      (ramseyApprox H (n + 1) (MMap.comp H F G)) F
      (H.levelMap G.map n + 1) := by
  constructor
  · change Nonempty (RamseyFiniteFactor H
      (ramseyApprox H (n + 1) (MMap.comp H F G))
      (ramseyApprox H (H.levelMap G.map n + 1) F))
    refine ⟨{ map := G, bound := ?_, agrees := ?_ }⟩
    · intro x
      calc
        LevelTree.lev (G x.1) = H.levelMap G.map (LevelTree.lev x.1) :=
          (H.levelMap_eq G.map (a := x.1)).symm
        _ ≤ H.levelMap G.map n := (H.levelMap_strictMono G.map).monotone x.2
    · intro x
      rfl
  · intro e he hfin
    cases e with
    | zero =>
        change False at hfin
        exact hfin
    | succ e =>
        change Nonempty (RamseyFiniteFactor H
          (ramseyApprox H (n + 1) (MMap.comp H F G))
          (ramseyApprox H (e + 1) F)) at hfin
        obtain ⟨fac⟩ := hfin
        obtain ⟨x, hx⟩ := H.level_nonempty n
        let xx : InitialNode T n := ⟨x, Nat.le_of_eq hx⟩
        have hEq : F (G x) = F (fac.map x) := fac.agrees xx
        have hNode : G x = fac.map x := F.map.injective hEq
        have hBound : LevelTree.lev (fac.map x) ≤ e := fac.bound xx
        have hLevel : LevelTree.lev (G x) = H.levelMap G.map n := by
          simpa only [hx] using (H.levelMap_eq G.map (a := x)).symm
        rw [← hNode, hLevel] at hBound
        omega

/-- Both directions of the source/approximation depth correspondence. -/
theorem source_depth_comp_iff (F G : MMap H) (n d : Nat) :
    (ramseyFinitization H).HasDepth
      (ramseyApprox H (n + 1) (MMap.comp H F G)) F d ↔
      d = H.levelMap G.map n + 1 := by
  constructor
  · intro hd
    exact (ramseyFinitization H).hasDepth_unique hd (source_depth_comp H F G n)
  · intro hd
    subst d
    exact source_depth_comp H F G n

/-- The empty stem has formal depth zero, corresponding to the
manuscript's empty-stem level -1. -/
theorem source_depth_empty (F : MMap H) (f : RamseyApprox H 0) :
    (ramseyFinitization H).HasDepth f F 0 := by
  constructor
  · change True
    trivial
  · intro e he
    omega

/-- The manuscript's EA1 witness at the original monoid depth.

`stem` is F ∘ F_x = f, equivalently F_x = g for the unique finite
quotient f = F ∘ g. It concerns the stem x; it does not say that the
ambient fat tree or any pure fat refinement literally begins with x.
The equation F' = rho_F(V) in `lifting` is retained literally. -/
structure SourceEA1Witness {n : Nat}
    (f : (ramseyApproximationSystem H).Approx n)
    (F : MMap H) (sourceDepth : Nat) where
  fatStem : (approximationSystem H).Approx n
  tree : FatTree H
  fatDepth : Nat
  depth : (finitization H).HasDepth fatStem tree fatDepth
  nonempty : ((approximationSystem H).neighborhood fatStem tree).Nonempty
  stem : leftComposeApprox H F (carriedApprox H fatStem) = f
  lifting : ∀ V,
    V ∈ (approximationSystem H).levelNeighborhood fatDepth tree →
    let F' := MMap.comp H F (associatedMap H V)
    F' ∈ (ramseyApproximationSystem H).levelNeighborhood sourceDepth F ∧
      ((ramseyApproximationSystem H).neighborhood f F').Nonempty ∧
      (ramseyApproximationSystem H).neighborhood f F' ⊆
        (fun W => MMap.comp H F (associatedMap H W)) ''
          ((approximationSystem H).neighborhood fatStem V)

/-- The stored finite-stem equation gives the exact prescribed source
stem on every infinite extension, not only on one representative. -/
theorem SourceEA1Witness.sourceStem
    {n : Nat} {f : (ramseyApproximationSystem H).Approx n}
    {F : MMap H} {sourceDepth : Nat}
    (ea : SourceEA1Witness H f F sourceDepth)
    (W : FatTree H)
    (hW : (approximationSystem H).approx n W = ea.fatStem) :
    ramseyApprox H n (MMap.comp H F (associatedMap H W)) = f := by
  exact (ramseyApprox_comp_eq_leftComposeApprox H F (associatedMap H W)
    (carriedApprox H ea.fatStem)
    (associatedMap_approx_eq_carriedApprox H ea.fatStem W hW)).trans ea.stem

/-- EA1 at every nonempty direct-monoid neighbourhood. Finite depth is
equivalent to nonemptiness, using the already proved direct A.3(1). -/
def HasSourceEA1 : Prop :=
  ∀ {n : Nat} (f : (ramseyApproximationSystem H).Approx n)
    (F : MMap H) {sourceDepth : Nat},
    (ramseyFinitization H).HasDepth f F sourceDepth →
    Nonempty (SourceEA1Witness H f F sourceDepth)

/-- Full EA: the EA1 witness and relative EA2 clauses use exactly the
same fat stem, fat tree and actual relative projection rho_F. -/
def HasSourceEA : Prop :=
  ∀ {n : Nat} (f : (ramseyApproximationSystem H).Approx n)
    (F : MMap H) {sourceDepth : Nat},
    (ramseyFinitization H).HasDepth f F sourceDepth →
    ∃ ea : SourceEA1Witness H f F sourceDepth,
      HasRelativeEA2Closed H ea.fatStem ea.tree
        (fun W => MMap.comp H F (associatedMap H W))

theorem HasSourceEA.toEA1 (hEA : HasSourceEA H) : HasSourceEA1 H := by
  intro n f F d hd
  obtain ⟨ea, _⟩ := hEA f F hd
  exact ⟨ea⟩

/-- The unconditional Borel fat-image theorem with the original fat
depth protected. Finite-colour elimination takes place in basic
neighbourhoods, followed by one genuine fat-tree A.3(2) refinement. -/
theorem fatImageHomogeneous_pure_of_pointwiseBorel
    {κ : Type w} [Fintype κ]
    {n : Nat} (a : (approximationSystem H).Approx n)
    (U : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a U d)
    (colour : MMap H → κ)
    (hBorel : ∀ c : κ,
      @MeasurableSet (MMap H) (pointwiseBorel H) {F | colour F = c}) :
    ∃ V, V ∈ (approximationSystem H).levelNeighborhood d U ∧
      ((approximationSystem H).neighborhood a V).Nonempty ∧
      ∃ c : κ, ∀ W,
        W ∈ (approximationSystem H).neighborhood a V →
          colour (associatedMap H W) = c := by
  have hne : ((approximationSystem H).neighborhood a U).Nonempty :=
    typed_amalgamation_nonempty H a U hd
      ((approximationSystem H).self_mem_levelNeighborhood d U)
  obtain ⟨B, hBU, c, hmono⟩ :=
    fatImageHomogeneous_of_pointwiseBorel H a U hne colour hBorel
  obtain ⟨V, hVU, hsub⟩ := pureDepthRefine_of_basicMember H a U hd B hBU
  refine ⟨V, hVU, typed_amalgamation_nonempty H a U hd hVU, c, ?_⟩
  intro W hW
  exact hmono W (hsub hW)

/-- The source Borel theorem for whole right-composition cones under
EA1 alone, with the original monoid stem and depth unchanged. -/
theorem shapeMapBorelCone_of_EA1
    (hEA1 : HasSourceEA1 H)
    {κ : Type w} [Fintype κ]
    {n : Nat} (f : (ramseyApproximationSystem H).Approx n)
    (F : MMap H) {sourceDepth : Nat}
    (hd : (ramseyFinitization H).HasDepth f F sourceDepth)
    (colour : MMap H → κ)
    (hBorel : ∀ c : κ,
      @MeasurableSet (MMap H) (pointwiseBorel H) {G | colour G = c}) :
    ∃ F', F' ∈ (ramseyApproximationSystem H).levelNeighborhood sourceDepth F ∧
      ((ramseyApproximationSystem H).neighborhood f F').Nonempty ∧
      ∃ c : κ, ∀ G,
        G ∈ (ramseyApproximationSystem H).neighborhood f F' → colour G = c := by
  obtain ⟨ea⟩ := hEA1 f F hd
  exact coneHomogeneous_of_pointwiseBorel_and_EA1 H ea.fatStem ea.tree
    ea.depth ea.nonempty F
    ((ramseyApproximationSystem H).levelNeighborhood sourceDepth F)
    (fun F' => (ramseyApproximationSystem H).neighborhood f F')
    (by
      intro V hV
      exact ⟨MMap.comp H F (associatedMap H V), ea.lifting V hV⟩)
    colour hBorel

/-- The manuscript's depth-preserving Ramsey predicate for direct
shape maps. It makes no direct A.3(2) assumption. -/
def SourceIsRamsey (X : Set (MMap H)) : Prop :=
  ∀ {n : Nat} (f : (ramseyApproximationSystem H).Approx n)
    (F : MMap H) {d : Nat},
    (ramseyFinitization H).HasDepth f F d →
    ∃ F', F' ∈ (ramseyApproximationSystem H).levelNeighborhood d F ∧
      (((ramseyApproximationSystem H).neighborhood f F' ⊆ X) ∨
        Disjoint ((ramseyApproximationSystem H).neighborhood f F') X)

/-- The corresponding depth-preserving Ramsey-null predicate. -/
def SourceIsRamseyNull (X : Set (MMap H)) : Prop :=
  ∀ {n : Nat} (f : (ramseyApproximationSystem H).Approx n)
    (F : MMap H) {d : Nat},
    (ramseyFinitization H).HasDepth f F d →
    ∃ F', F' ∈ (ramseyApproximationSystem H).levelNeighborhood d F ∧
      Disjoint ((ramseyApproximationSystem H).neighborhood f F') X

/-- The source Ellentuck-Baire conclusion under the common EA witness. -/
theorem shapeMapRamsey_of_EA
    (hEA : HasSourceEA H) (X : Set (MMap H))
    (hX : @BaireMeasurableSet (MMap H)
      (ramseyApproximationSystem H).ellentuckTopology X) :
    SourceIsRamsey H X := by
  intro n f F d hd
  obtain ⟨ea, hEA2Closed⟩ := hEA f F hd
  have hEA2 := (hasRelativeEA2_iff_closed H ea.fatStem ea.tree
    (fun W => MMap.comp H F (associatedMap H W))).mpr hEA2Closed
  obtain ⟨F', hPure, _, hHom⟩ :=
    coneRamsey_of_relativeEA2 H ea.fatStem ea.tree ea.depth ea.nonempty
      (fun W => MMap.comp H F (associatedMap H W))
      ((ramseyApproximationSystem H).levelNeighborhood d F)
      (fun F' => (ramseyApproximationSystem H).neighborhood f F')
      (by
        intro V hV
        exact ⟨MMap.comp H F (associatedMap H V), ea.lifting V hV⟩)
      hEA2 X hX
  exact ⟨F', hPure, hHom⟩

/-- The source meagre/Ramsey-null conclusion under the common EA witness. -/
theorem shapeMapRamseyNull_of_EA
    (hEA : HasSourceEA H) (X : Set (MMap H))
    (hX : @_root_.IsMeagre (MMap H)
      (ramseyApproximationSystem H).ellentuckTopology X) :
    SourceIsRamseyNull H X := by
  intro n f F d hd
  obtain ⟨ea, hEA2Closed⟩ := hEA f F hd
  have hEA2 := (hasRelativeEA2_iff_closed H ea.fatStem ea.tree
    (fun W => MMap.comp H F (associatedMap H W))).mpr hEA2Closed
  obtain ⟨F', hPure, _, hDis⟩ :=
    coneNull_of_relativeEA2 H ea.fatStem ea.tree ea.depth ea.nonempty
      (fun W => MMap.comp H F (associatedMap H W))
      ((ramseyApproximationSystem H).levelNeighborhood d F)
      (fun F' => (ramseyApproximationSystem H).neighborhood f F')
      (by
        intro V hV
        exact ⟨MMap.comp H F (associatedMap H V), ea.lifting V hV⟩)
      hEA2 X hX
  exact ⟨F', hPure, hDis⟩

/-- Both clauses of the corrected shape-map Ellentuck theorem, using
the actual monoid topology, source stems and pure refinements. -/
theorem shapeMapEllentuck_of_EA (hEA : HasSourceEA H) :
    (∀ X : Set (MMap H),
      @BaireMeasurableSet (MMap H)
        (ramseyApproximationSystem H).ellentuckTopology X →
      SourceIsRamsey H X) ∧
    (∀ X : Set (MMap H),
      @_root_.IsMeagre (MMap H)
        (ramseyApproximationSystem H).ellentuckTopology X →
      SourceIsRamseyNull H X) := by
  exact ⟨shapeMapRamsey_of_EA H hEA, shapeMapRamseyNull_of_EA H hEA⟩

end SuccessorTree.SMTree.FatTree

import SuccessorTree.ShapeRamseyFusion
import SuccessorTree.ShapeFrontFusion
import SuccessorTree.ShapeExactFactor
import Mathlib.Tactic

/-!
# Local one-step pigeonhole from the global one-dimensional Ramsey theorem

The one-dimensional Milliken fusion is global at a frozen cut.  To run the
ordinary finite-front fusion we need the same statement below an arbitrary
finite prefix.  The bridge is canonical: a same-depth refinement fixes the
canonical extension of the prefix, and every one-step extension factors
through that fixed bridge with one coordinate in AM^d_1.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Canonicalising an already canonical extension at the same cut changes
nothing. -/
theorem canonicalExtension_idem
    (H : SMTree S) (F : MMap H) (n : Nat) :
    H.canonicalExtension (H.canonicalExtension F n) n =
      H.canonicalExtension F n := by
  have h :=
    H.canonicalExtension_unique
      (H.canonicalExtension F n)
      (H.canonicalExtension F n) n
      (by
        intro x hx
        rfl)
      (by
        intro ell hell
        apply H.canonicalExtension_tail_mem_levelRange F n ell
        rw [H.canonicalExtension_level_at_prefix F n] at hell
        exact hell)
  exact h.symm

/-- A same-depth refinement does not change the canonical bridge representing
a fixed finite prefix. -/
theorem prefixCanonical_eq_of_levelNeighborhood
    (H : SMTree S)
    {n d : Nat}
    {a : RamseyApprox H (n + 1)}
    {A B : MMap H}
    (hAB :
      A ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B)
    (hdB :
      (ramseyFinitization H).HasDepth (n := n + 1) a B (d + 1)) :
    let hdA :
        (ramseyFinitization H).HasDepth (n := n + 1) a A (d + 1) :=
      ((ramseyFinitization H).hasDepth_iff_of_mem_levelNeighborhood hAB).2 hdB
    H.prefixCanonical hdA = H.prefixCanonical hdB := by
  let hdA :
      (ramseyFinitization H).HasDepth (n := n + 1) a A (d + 1) :=
    ((ramseyFinitization H).hasDepth_iff_of_mem_levelNeighborhood hAB).2 hdB
  let CA : MMap H := H.prefixCanonical hdA
  let CB : MMap H := H.prefixCanonical hdB
  have hstep : FusionStep H d B A :=
    H.fusionStep_of_mem_levelNeighborhood hAB
  rcases hstep with ⟨K, hKfix, hAK⟩
  have hBreal := H.prefixCanonical_realizes hdB
  have hAreal := H.prefixCanonical_realizes hdA
  have hBunderA :
      ramseyApprox H (n + 1) (MMap.comp H A CB) = a := by
    apply Subtype.ext
    funext y
    have hBval := congrArg Subtype.val hBreal
    change (MMap.comp H B CB).restrictLe H n = a.1 at hBval
    have hyB := congrFun hBval y
    change A (CB y.1) = a.1 y
    rw [hAK]
    change B (K (CB y.1)) = a.1 y
    have hlev : LevelTree.lev (CB y.1) < d + 1 :=
      H.prefixCanonical_bound_prefix hdB y.1 y.2
    rw [hKfix (CB y.1) hlev]
    exact hyB
  have hagree :
      ∀ x : T, LevelTree.lev x ≤ n → CB x = CA x := by
    intro x hx
    let xx : InitialNode T n := ⟨x, hx⟩
    have hAval := congrArg Subtype.val hAreal
    have hBval := congrArg Subtype.val hBunderA
    change (MMap.comp H A CA).restrictLe H n = a.1 at hAval
    change (MMap.comp H A CB).restrictLe H n = a.1 at hBval
    have hAx := congrFun hAval xx
    have hBx := congrFun hBval xx
    apply A.map.injective
    exact hBx.trans hAx.symm
  have hfull :
      ∀ ell : Nat, H.levelMap CA.map n ≤ ell →
        ell ∈ CB.map.levelRange := by
    intro ell hell
    change ell ∈ (H.prefixCanonical hdB).map.levelRange
    let facB : RamseyFiniteFactor H a (ramseyApprox H (d + 1) B) :=
      Classical.choice hdB.1
    change ell ∈ (H.canonicalExtension facB.map n).map.levelRange
    apply H.canonicalExtension_tail_mem_levelRange facB.map n ell
    have hCA : H.levelMap CA.map n = d :=
      H.prefixCanonical_level hdA
    have hfac :
        H.levelMap facB.map.map n = d :=
      H.ramseyFiniteFactor_topLevel_of_depth hdB facB
    rw [hfac]
    simpa [hCA] using hell
  have huniq :
      CB = H.canonicalExtension CA n :=
    H.canonicalExtension_unique CA CB n hagree hfull
  calc
    H.prefixCanonical hdA = CA := rfl
    _ = H.canonicalExtension CA n :=
      (H.canonicalExtension_idem CA n).symm
    _ = CB := huniq.symm
    _ = H.prefixCanonical hdB := rfl


/-- The global one-dimensional Ramsey theorem implies the arbitrary-prefix
local pigeonhole principle required by the ordinary Milliken front fusion. -/
theorem shapeLocalPigeonhole
    [Fintype κ]
    (H : SMTree S)
    (colour : StepColouring H κ) :
    LocalPigeonhole H colour := by
  classical
  letI : DecidableEq κ := Classical.decEq κ
  intro p B D hDpos hdepth
  rcases p with ⟨m, a⟩
  cases m with
  | zero =>
      obtain ⟨d, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hDpos)
      exact False.elim (H.not_hasDepth_zero_of_succ B d a hdepth)
  | succ n =>
      obtain ⟨d, hD⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hDpos)
      subst D
      let C : MMap H := H.prefixCanonical hdepth
      let localColour : AM H (d + 1) 1 → κ :=
        fun q =>
          colour (n + 1)
            (ramseyApprox H (n + 2)
              (MMap.comp H B
                (MMap.comp H (q.representative H) C)))
      obtain ⟨W, hW⟩ :=
        H.shapeOneDimensionalRamsey (d + 1) localColour
      let A : MMap H := MMap.comp H B W.1
      have hAB :
          A ∈ (ramseyApproximationSystem H).levelNeighborhood (d + 1) B := by
        apply H.fusionStep_mem_levelNeighborhood
        exact ⟨W.1, W.2, rfl⟩
      let hdA :
          (ramseyFinitization H).HasDepth (n := n + 1) a A (d + 1) :=
        ((ramseyFinitization H).hasDepth_iff_of_mem_levelNeighborhood
          hAB).2 hdepth
      have hbridge :
          H.prefixCanonical hdA = C := by
        change H.prefixCanonical hdA = H.prefixCanonical hdepth
        exact H.prefixCanonical_eq_of_levelNeighborhood hAB hdepth
      let q0 : AM H (d + 1) 1 := AM.id1 H (d + 1)
      let c0 : κ := localColour (H.shapeAct (d + 1) W q0)
      refine ⟨A, hAB, c0, ?_⟩
      intro b hb
      rcases hb with ⟨X, hXaA, hXb⟩
      have hXbA :
          X ∈ (ramseyApproximationSystem H).neighborhood b A :=
        ⟨hXaA.1, hXb⟩
      obtain ⟨e, hbe⟩ :=
        (ramseyFinitization H).exists_hasDepth_of_mem_neighborhood hXbA
      have hstrict :
          d + 1 < e :=
        H.oneStep_hasDepth_strict hdA
          (show b ∈
            (ramseyApproximationSystem H).oneStepApproximations
              (n := n + 1) a A from ⟨X, hXaA, hXb⟩)
          hbe
      obtain ⟨qdepth, hqdepth⟩ :
          ∃ qdepth : Nat, e = qdepth + 1 := by
        exact ⟨e - 1, by omega⟩
      subst e
      obtain ⟨Q, hQfix, hQtop, hbfact⟩ :=
        H.oneStep_exactDepth_fixedBridge hdA
          (show b ∈
            (ramseyApproximationSystem H).oneStepApproximations
              (n := n + 1) a A from ⟨X, hXaA, hXb⟩)
          hbe
      let qAM : AM H (d + 1) 1 :=
        Q.toAM H (d + 1) 1 hQfix
      have heq :
          ramseyApprox H (n + 2)
              (MMap.comp H B
                (MMap.comp H
                  ((H.shapeAct (d + 1) W qAM).representative H)
                  C)) =
            b := by
        rw [hbfact]
        apply Subtype.ext
        funext y
        have hCy :
            LevelTree.lev (C y.1) ≤ d + 1 := by
          change LevelTree.lev (H.prefixCanonical hdepth y.1) ≤ d + 1
          exact H.prefixCanonical_bound_succ hdepth y.1 y.2
        have hact :
            (H.shapeAct (d + 1) W qAM).representative H (C y.1) =
              W.1 (qAM.representative H (C y.1)) :=
          H.shapeAct_representative_agrees
            (d + 1) W qAM (C y.1) hCy
        have hqrep :
            qAM.representative H (C y.1) = Q (C y.1) :=
          MMap.toAM_one_representative_agrees
            H Q (d + 1) hQfix (C y.1) hCy
        change
          B ((H.shapeAct (d + 1) W qAM).representative H (C y.1)) =
            A (Q (H.prefixCanonical hdA y.1))
        rw [hact, hqrep, hbridge]
        rfl
      calc
        colour (n + 1) b =
            localColour (H.shapeAct (d + 1) W qAM) := by
          change
            colour (n + 1) b =
              colour (n + 1)
                (ramseyApprox H (n + 2)
                  (MMap.comp H B
                    (MMap.comp H
                      ((H.shapeAct (d + 1) W qAM).representative H)
                      C)))
          rw [heq]
        _ = localColour (H.shapeAct (d + 1) W q0) :=
          hW qAM q0
        _ = c0 := rfl

end SMTree
end SuccessorTree

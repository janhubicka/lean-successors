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
    _ = H.canonicalExtension CA n := by
      rw [H.canonicalExtension_idem CA n]
    _ = CB := huniq.symm
    _ = H.prefixCanonical hdB := rfl


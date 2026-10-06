import SuccessorTree.ShapePrefixPigeonhole
import Mathlib.Tactic

/-!
# Simultaneous replay on a finite depth front

At one positive depth all finite prefixes use the same local replay level.
We therefore colour a local word by the vector of colours it induces at
every prefix on a finite depth front, and apply Hales--Jewett once.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- A positive depth cannot be the depth of the empty approximation. -/
theorem not_hasDepth_zero_of_succ
    (H : SMTree S) (B : MMap H) (e : Nat)
    (a : RamseyApprox H 0) :
    ¬ (ramseyFinitization H).HasDepth (n := 0) a B (e + 1) := by
  intro h
  have hzero :
      RamseyLeFin H
        (⟨0, a⟩ : (ramseyApproximationSystem H).FiniteApprox)
        ((ramseyApproximationSystem H).finiteApprox 0 B) := by
    trivial
  exact (h.2 0 (by omega)) hzero

/-- The finite approximation obtained from one local word at an arbitrary
front prefix of depth e+1. -/
noncomputable def frontWordApprox
    (H : SMTree S)
    (B : MMap H) (e : Nat)
    (p : (ramseyApproximationSystem H).FiniteApprox)
    (hp : (ramseyFinitization H).HasDepth p.2 B (e + 1))
    (word : List (OneLevelLetter H (e + 1))) :
    RamseyApprox H (p.1 + 1) := by
  rcases p with ⟨m, a⟩
  cases m with
  | zero =>
      exact False.elim (H.not_hasDepth_zero_of_succ B e a hp)
  | succ n =>
      exact H.prefixWordApprox hp word

/-- The finite approximation obtained from applying a common replay block at
an arbitrary front prefix of depth e+1. -/
noncomputable def frontReplayApply
    (H : SMTree S)
    (B : MMap H) (e : Nat)
    (p : (ramseyApproximationSystem H).FiniteApprox)
    (hp : (ramseyFinitization H).HasDepth p.2 B (e + 1))
    (R : ReplayBlock H (e + 1))
    (x : LineInput (OneLevelLetter H (e + 1))) :
    RamseyApprox H (p.1 + 1) := by
  rcases p with ⟨m, a⟩
  cases m with
  | zero =>
      exact False.elim (H.not_hasDepth_zero_of_succ B e a hp)
  | succ n =>
      exact H.prefixReplayApply hp R x

/-- A dependent tuple containing one next approximation for every member of a
finite front. -/
abbrev FrontApprox
    (H : SMTree S)
    (P : Finset (ramseyApproximationSystem H).FiniteApprox) :=
  (p : {p // p ∈ P}) → RamseyApprox H (p.1.1 + 1)

/-- ReplaySystem obtained by applying the same local replay block
simultaneously at every prefix of one finite positive-depth front. -/
noncomputable def frontReplaySystem
    (H : SMTree S)
    (B : MMap H) (e : Nat)
    (P : Finset (ramseyApproximationSystem H).FiniteApprox)
    (hdepth :
      ∀ p ∈ P, (ramseyFinitization H).HasDepth p.2 B (e + 1)) :
    ReplaySystem
      (OneLevelLetter H (e + 1))
      (FrontApprox H P)
      (ReplayBlock H (e + 1)) where
  wordApprox := fun word p =>
    H.frontWordApprox B e p.1 (hdepth p.1 p.2) word
  apply := fun R x p =>
    H.frontReplayApply B e p.1 (hdepth p.1 p.2) R x
  replay := fun L hs => H.replayBlock L hs
  replay_base := by
    intro L hs
    funext p
    rcases p with ⟨⟨m, a⟩, hmem⟩
    cases m with
    | zero =>
        exact False.elim
          (H.not_hasDepth_zero_of_succ B e a
            (hdepth ⟨0, a⟩ hmem))
    | succ n =>
        simp only [frontReplayApply, frontWordApprox]
        exact
          (H.prefixReplaySystem
            (hdepth ⟨n + 1, a⟩ hmem)).replay_base L hs
  replay_letter := by
    intro L hs letter
    funext p
    rcases p with ⟨⟨m, a⟩, hmem⟩
    cases m with
    | zero =>
        exact False.elim
          (H.not_hasDepth_zero_of_succ B e a
            (hdepth ⟨0, a⟩ hmem))
    | succ n =>
        simp only [frontReplayApply, frontWordApprox]
        exact
          (H.prefixReplaySystem
            (hdepth ⟨n + 1, a⟩ hmem)).replay_letter L hs letter

/-- One common replay block simultaneously makes the canonical local line at
every prefix of a finite depth-(e+1) front monochromatic. -/
theorem finiteDepthFront_replay_pigeonhole
    [Fintype κ]
    (H : SMTree S)
    (colour :
      (n : Nat) → RamseyApprox H (n + 1) → κ)
    (B : MMap H) (e : Nat)
    (P : Finset (ramseyApproximationSystem H).FiniteApprox)
    (hdepth :
      ∀ p ∈ P, (ramseyFinitization H).HasDepth p.2 B (e + 1)) :
    ∃ R : ReplayBlock H (e + 1),
      ∀ p : {p // p ∈ P},
        ∀ x : LineInput (OneLevelLetter H (e + 1)),
          colour p.1.1
              (H.frontReplayApply B e p.1
                (hdepth p.1 p.2) R x) =
            colour p.1.1
              (H.frontReplayApply B e p.1
                (hdepth p.1 p.2) R LineInput.base) := by
  classical
  let vectorColour : FrontApprox H P → ({p // p ∈ P} → κ) :=
    fun A p => colour p.1.1 (A p)
  obtain ⟨R, hR⟩ :=
    (H.frontReplaySystem B e P hdepth).oneDimensionalPigeonhole_finite
      vectorColour
  refine ⟨R, ?_⟩
  intro p x
  exact congrFun (hR x) p

end SMTree
end SuccessorTree

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
theorem not_hasDepth_zero_of_pos
    (H : SMTree S) (B : MMap H) {d : Nat} (hd : 0 < d)
    (a : RamseyApprox H 0) :
    ¬ (ramseyFinitization H).HasDepth a B d := by
  intro h
  have hzero :
      RamseyLeFin H
        (⟨0, a⟩ : (ramseyApproximationSystem H).FiniteApprox)
        ((ramseyApproximationSystem H).finiteApprox 0 B) := by
    trivial
  exact (h.2 0 hd) hzero

/-- The finite approximation obtained from one local word at an arbitrary
positive-depth front prefix. -/
noncomputable def frontWordApprox
    (H : SMTree S)
    (B : MMap H) {d : Nat} (hdpos : 0 < d)
    (p : (ramseyApproximationSystem H).FiniteApprox)
    (hp : (ramseyFinitization H).HasDepth p.2 B d)
    (word : List (OneLevelLetter H d)) :
    RamseyApprox H (p.1 + 1) := by
  rcases p with ⟨m, a⟩
  cases m with
  | zero =>
      exact False.elim (H.not_hasDepth_zero_of_pos B hdpos a hp)
  | succ n =>
      obtain ⟨e, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
      exact H.prefixWordApprox hp word

/-- The finite approximation obtained from applying a common replay block at
an arbitrary positive-depth front prefix. -/
noncomputable def frontReplayApply
    (H : SMTree S)
    (B : MMap H) {d : Nat} (hdpos : 0 < d)
    (p : (ramseyApproximationSystem H).FiniteApprox)
    (hp : (ramseyFinitization H).HasDepth p.2 B d)
    (R : ReplayBlock H d)
    (x : LineInput (OneLevelLetter H d)) :
    RamseyApprox H (p.1 + 1) := by
  rcases p with ⟨m, a⟩
  cases m with
  | zero =>
      exact False.elim (H.not_hasDepth_zero_of_pos B hdpos a hp)
  | succ n =>
      obtain ⟨e, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
      exact H.prefixReplayApply hp R x

/-- A dependent tuple containing one next approximation for every member of a
finite front. -/
abbrev FrontApprox
    (H : SMTree S)
    (P : Finset (ramseyApproximationSystem H).FiniteApprox) :=
  (p : {p // p ∈ P}) → RamseyApprox H (p.1.1 + 1)

/-- ReplaySystem obtained by applying the same local replay block
simultaneously at every prefix of a finite positive-depth front. -/
noncomputable def frontReplaySystem
    (H : SMTree S)
    (B : MMap H) {d : Nat} (hdpos : 0 < d)
    (P : Finset (ramseyApproximationSystem H).FiniteApprox)
    (hdepth :
      ∀ p ∈ P, (ramseyFinitization H).HasDepth p.2 B d) :
    ReplaySystem
      (OneLevelLetter H d)
      (FrontApprox H P)
      (ReplayBlock H d) where
  wordApprox := fun word p =>
    H.frontWordApprox B hdpos p.1 (hdepth p.1 p.2) word
  apply := fun R x p =>
    H.frontReplayApply B hdpos p.1 (hdepth p.1 p.2) R x
  replay := fun L hs => H.replayBlock L hs
  replay_base := by
    intro L hs
    funext p
    rcases p with ⟨⟨m, a⟩, hmem⟩
    cases m with
    | zero =>
        exact False.elim
          (H.not_hasDepth_zero_of_pos B hdpos a (hdepth ⟨0, a⟩ hmem))
    | succ n =>
        obtain ⟨e, rfl⟩ :=
          Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
        change
          H.prefixReplayApply (hdepth ⟨n + 1, a⟩ hmem)
              (H.replayBlock L hs) LineInput.base =
            H.prefixWordApprox (hdepth ⟨n + 1, a⟩ hmem) L.star
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
          (H.not_hasDepth_zero_of_pos B hdpos a (hdepth ⟨0, a⟩ hmem))
    | succ n =>
        obtain ⟨e, rfl⟩ :=
          Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdpos)
        change
          H.prefixReplayApply (hdepth ⟨n + 1, a⟩ hmem)
              (H.replayBlock L hs) (LineInput.letter letter) =
            H.prefixWordApprox (hdepth ⟨n + 1, a⟩ hmem) (L.eval letter)
        exact
          (H.prefixReplaySystem
            (hdepth ⟨n + 1, a⟩ hmem)).replay_letter L hs letter

/-- One common replay block simultaneously makes the canonical local line at
every prefix of a finite positive-depth front monochromatic. -/
theorem finiteDepthFront_replay_pigeonhole
    [Fintype κ]
    (H : SMTree S)
    (colour :
      (n : Nat) → RamseyApprox H (n + 1) → κ)
    (B : MMap H) (d : Nat) (hdpos : 0 < d)
    (P : Finset (ramseyApproximationSystem H).FiniteApprox)
    (hdepth :
      ∀ p ∈ P, (ramseyFinitization H).HasDepth p.2 B d) :
    ∃ R : ReplayBlock H d,
      ∀ p : {p // p ∈ P},
        ∀ x : LineInput (OneLevelLetter H d),
          colour p.1.1
              (H.frontReplayApply B hdpos p.1
                (hdepth p.1 p.2) R x) =
            colour p.1.1
              (H.frontReplayApply B hdpos p.1
                (hdepth p.1 p.2) R LineInput.base) := by
  classical
  let vectorColour : FrontApprox H P → ({p // p ∈ P} → κ) :=
    fun A p => colour p.1.1 (A p)
  obtain ⟨R, hR⟩ :=
    (H.frontReplaySystem B hdpos P hdepth).oneDimensionalPigeonhole_finite
      vectorColour
  refine ⟨R, ?_⟩
  intro p x
  exact congrFun (hR x) p

end SMTree
end SuccessorTree

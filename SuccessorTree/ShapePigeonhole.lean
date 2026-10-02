import SuccessorTree.Canonical
import SuccessorTree.Replay
import SuccessorTree.RamseySpace.Basic
import SuccessorTree.RamseySpace.Finitization

/-!
# Finite shape approximations and the one-dimensional pigeonhole lemma

This is the paper-level wrapper around the already verified M3 replay.
An element of `AM H n k` is a realized finite M-map through source level
`n+k-1` whose prefix through `n-1` is the identity.

The local line at level `n` is represented by `LineInput
(OneLevelLetter H n)`: the base case is the identity and the other cases are
the canonical one-level extensions.  The theorem at the end is Lemma 3.1 in
this concrete finite-approximation language.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Paper notation `AM^n_k`: realized finite shape maps of width `k`
which are the identity below the frozen source level `n`. -/
def AM (H : SMTree S) (n k : Nat) : Type u :=
  {a : RamseyApprox H (n + k) //
    (ramseyApproximationSystem H).IsInitial
      (ramseyApprox H n (MMap.id H)) a}

namespace MMap

/-- Equality of the finite prefix with the identity follows from pointwise
fixing below the cut. -/
theorem ramseyApprox_eq_id_of_fixesBelow
    (H : SMTree S) (F : MMap H) (n : Nat)
    (hF : F.FixesBelow H n) :
    ramseyApprox H n F = ramseyApprox H n (MMap.id H) := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      apply Subtype.ext
      funext a
      change F a.1 = a.1
      exact hF a.1 (by omega)

/-- A total M-map fixing all levels below `n` determines an element of every
finite class `AM^n_k`. -/
def toAM
    (H : SMTree S) (F : MMap H) (n k : Nat)
    (hF : F.FixesBelow H n) :
    AM H n k := by
  refine ⟨ramseyApprox H (n + k) F, ?_⟩
  refine ⟨by omega, F, ?_, rfl⟩
  exact F.ramseyApprox_eq_id_of_fixesBelow H n hF

@[simp] theorem toAM_val
    (H : SMTree S) (F : MMap H) (n k : Nat)
    (hF : F.FixesBelow H n) :
    (F.toAM H n k hF).1 = ramseyApprox H (n + k) F := rfl

end MMap

/-- Conversely, equality of the finite prefix with the identity forces
pointwise fixing below the cut. -/
theorem MMap.fixesBelow_of_ramseyApprox_eq_id
    (H : SMTree S) (F : MMap H) (n : Nat)
    (hF : ramseyApprox H n F = ramseyApprox H n (MMap.id H)) :
    F.FixesBelow H n := by
  cases n with
  | zero =>
      intro a ha
      omega
  | succ n =>
      intro a ha
      have hval := congrArg Subtype.val hF
      change F.restrictLe H n = (MMap.id H).restrictLe H n at hval
      have ha' : LevelTree.lev a ≤ n := by omega
      have happ := congrFun hval ⟨a, ha'⟩
      exact happ

namespace AM

/-- A deterministic representative is not needed for the finite map itself,
but choosing one is convenient when composing finite approximations. -/
noncomputable def representative
    (H : SMTree S) {n k : Nat} (a : AM H n k) : MMap H :=
  Classical.choose a.2.2

theorem representative_prefix
    (H : SMTree S) {n k : Nat} (a : AM H n k) :
    ramseyApprox H n (a.representative H) =
      ramseyApprox H n (MMap.id H) :=
  (Classical.choose_spec a.2.2).1

theorem representative_top
    (H : SMTree S) {n k : Nat} (a : AM H n k) :
    ramseyApprox H (n + k) (a.representative H) = a.1 :=
  (Classical.choose_spec a.2.2).2

theorem representative_fixesBelow
    (H : SMTree S) {n k : Nat} (a : AM H n k) :
    (a.representative H).FixesBelow H n :=
  MMap.fixesBelow_of_ramseyApprox_eq_id H _ n (a.representative_prefix H)

end AM

/-- Minimality of depth forces a finite factor to reach the top level of the
target approximation.  This is the finite-level bridge used when moving the
one-dimensional pigeonhole to an arbitrary prefix. -/
theorem ramseyFiniteFactor_topLevel_of_depth
    (H : SMTree S)
    {n d : Nat}
    {a : RamseyApprox H (n + 1)}
    {B : MMap H}
    (hd : (ramseyFinitization H).HasDepth (n := n + 1) a B (d + 1))
    (fac : RamseyFiniteFactor H a (ramseyApprox H (d + 1) B)) :
    H.levelMap fac.map.map n = d := by
  obtain ⟨x, hx⟩ := H.level_nonempty n
  have hupper : H.levelMap fac.map.map n ≤ d := by
    calc
      H.levelMap fac.map.map n = LevelTree.lev (fac.map x) := by
        simpa [hx] using H.levelMap_eq fac.map.map (a := x)
      _ ≤ d := fac.bound ⟨x, by simpa [hx]⟩
  apply le_antisymm hupper
  by_contra hnot
  have hlt : H.levelMap fac.map.map n < d := by omega
  let t : Nat := H.levelMap fac.map.map n
  have hsmall : t + 1 < d + 1 := by
    dsimp [t]
    omega
  apply hd.2 (t + 1) hsmall
  change Nonempty
    (RamseyFiniteFactor H a (ramseyApprox H (t + 1) B))
  refine ⟨{
    map := fac.map
    bound := ?_
    agrees := ?_
  }⟩
  · intro y
    calc
      LevelTree.lev (fac.map y.1) =
          H.levelMap fac.map.map (LevelTree.lev y.1) := by
        exact (H.levelMap_eq fac.map.map (a := y.1)).symm
      _ ≤ H.levelMap fac.map.map n :=
        (H.levelMap_strictMono fac.map.map).monotone y.2
      _ = t := rfl
  · intro y
    have hy := fac.agrees y
    change a.1 y = B (fac.map y.1) at hy
    change a.1 y = B (fac.map y.1)
    exact hy

/-- Every word in the one-level Hales--Jewett alphabet fixes the frozen
prefix. -/
theorem wordMap_fixesBelow
    (H : SMTree S) (n : Nat)
    (w : List (OneLevelLetter H n)) :
    (wordMap H n w).FixesBelow H n := by
  intro a ha
  exact H.wordMap_eq_id_below n w ha

/-- The paper's finite approximation `g_w`, now packaged in `AM^n_1`. -/
def wordApproxAM
    (H : SMTree S) (n : Nat)
    (w : List (OneLevelLetter H n)) :
    AM H n 1 :=
  (wordMap H n w).toAM H n 1 (H.wordMap_fixesBelow n w)

/-- The identity/letter members of the local line all fix the frozen prefix. -/
theorem localLine_fixesBelow
    (H : SMTree S) (n : Nat)
    (x : LineInput (OneLevelLetter H n)) :
    (match x with
      | .base => MMap.id H
      | .letter e => e.toMMap).FixesBelow H n := by
  cases x with
  | base =>
      exact MMap.id_fixesBelow H n
  | letter e =>
      intro a ha
      exact e.eq_id_below H ha

/-- A replay block is itself an element of `AM^n_2`. -/
def ReplayBlock.toAM2
    (H : SMTree S) (n : Nat)
    (B : ReplayBlock H n) :
    AM H n 2 :=
  B.toMMap.toAM H n 2 B.fixesBelow

/-- Composition of a replay block with the local identity/letter input,
packaged as an actual member of `AM^n_1`. -/
def replayApplyAM
    (H : SMTree S) (n : Nat)
    (B : ReplayBlock H n) :
    LineInput (OneLevelLetter H n) → AM H n 1
  | .base =>
      B.toMMap.toAM H n 1 B.fixesBelow
  | .letter e =>
      (MMap.comp H B.toMMap e.toMMap).toAM H n 1
        (MMap.comp_fixesBelow H B.toMMap e.toMMap n
          B.fixesBelow
          (by
            intro a ha
            exact e.eq_id_below H ha))

/-- The finite replay action has the same underlying restriction as the raw
replay action already verified in `Replay.lean`. -/
theorem replayApplyAM_restricted
    (H : SMTree S) (n : Nat)
    (B : ReplayBlock H n)
    (x : LineInput (OneLevelLetter H n)) :
    (replayApplyAM H n B x).1.1 =
      replayApply H n B x := by
  cases x <;> rfl

/-- The concrete replay system lifted from raw restrictions to realized
paper-level finite shape approximations. -/
noncomputable def replayAMSystem
    (H : SMTree S) (n : Nat) :
    ReplaySystem
      (OneLevelLetter H n)
      (AM H n 1)
      (ReplayBlock H n) where
  wordApprox := wordApproxAM H n
  apply := replayApplyAM H n
  replay := fun L hs => H.replayBlock L hs
  replay_base := by
    intro L hs
    apply Subtype.ext
    apply Subtype.ext
    funext a
    exact H.replayMap_base L hs a
  replay_letter := by
    intro L hs e
    apply Subtype.ext
    apply Subtype.ext
    have hraw := (H.replaySystem n).replay_letter L hs e
    exact hraw

/-- Paper Lemma 3.1 in finite shape-preserving language.

For every finite colouring of `AM^n_1`, an M3 replay block `B` gives an
element `h = B|T(<n+2) ∈ AM^n_2` such that all compositions with the local
identity/one-level letters have the same colour. -/
theorem oneDimensionalPigeonhole_shape
    [Fintype κ]
    (H : SMTree S) (n : Nat)
    (colour : AM H n 1 → κ) :
    ∃ B : ReplayBlock H n,
      ∀ x : LineInput (OneLevelLetter H n),
        colour (replayApplyAM H n B x) =
          colour (replayApplyAM H n B LineInput.base) := by
  exact (H.replayAMSystem n).oneDimensionalPigeonhole_finite colour

/-- Explicit paper-style witness: the replay block determines an
`AM^n_2` member witnessing the preceding pigeonhole conclusion. -/
theorem oneDimensionalPigeonhole_shape_AM2
    [Fintype κ]
    (H : SMTree S) (n : Nat)
    (colour : AM H n 1 → κ) :
    ∃ h : AM H n 2, ∃ B : ReplayBlock H n,
      h = B.toAM2 H n ∧
      ∀ x : LineInput (OneLevelLetter H n),
        colour (replayApplyAM H n B x) =
          colour (replayApplyAM H n B LineInput.base) := by
  obtain ⟨B, hB⟩ := H.oneDimensionalPigeonhole_shape n colour
  exact ⟨B.toAM2 H n, B, rfl, hB⟩

end SMTree
end SuccessorTree

import SuccessorTree.ShapeFiniteRamsey
import Mathlib.Order.KonigLemma

/-!
# Finite terminal bounds for shape approximations

This file packages the three finite terminal-level classes used in the
manuscript and the elementary finite-composition bookkeeping needed for the
two finite corollaries.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace AM

/-- The terminal target level of a nonempty finite shape approximation.
The paper uses this only when n+k>0. -/
noncomputable def terminalLevel
    (H : SMTree S) {n k : Nat} (a : AM H n k) : Nat :=
  H.levelMap (a.representative H).map (n + k - 1)

/-- Every value represented by a nonempty finite approximation lies no
higher than its terminal target level. -/
theorem level_le_terminalLevel
    (H : SMTree S) {n k : Nat} (a : AM H n k)
    {x : T} (hx : LevelTree.lev x < n + k) :
    LevelTree.lev (a.representative H x) ≤ a.terminalLevel H := by
  calc
    LevelTree.lev (a.representative H x) =
        H.levelMap (a.representative H).map (LevelTree.lev x) :=
      (H.levelMap_eq (a.representative H).map (a := x)).symm
    _ ≤ H.levelMap (a.representative H).map (n + k - 1) :=
      (H.levelMap_strictMono (a.representative H).map).monotone (by omega)
    _ = a.terminalLevel H := rfl

/-- A finite approximation ending at or before level N. -/
abbrev AtMost
    (H : SMTree S) (n k N : Nat) :=
  {a : AM H n k // a.terminalLevel H ≤ N}

/-- A finite approximation ending strictly before level N. -/
abbrev Below
    (H : SMTree S) (n k N : Nat) :=
  {a : AM H n k // a.terminalLevel H < N}

/-- A finite approximation ending exactly at level N. -/
abbrev At
    (H : SMTree S) (n k N : Nat) :=
  {a : AM H n k // a.terminalLevel H = N}

/-- Finite approximations agree when their total representatives agree on
the represented source segment. -/
theorem ramseyApprox_eq_of_apply
    (H : SMTree S) {m : Nat} {F G : MMap H}
    (h : ∀ x : T, LevelTree.lev x < m → F x = G x) :
    ramseyApprox H m F = ramseyApprox H m G := by
  cases m with
  | zero => rfl
  | succ m =>
      apply Subtype.ext
      funext x
      exact h x.1 (by omega)

/-- Code a bounded nonempty approximation by its finite action between two
finite initial tree segments. -/
noncomputable def atMostCode
    (H : SMTree S) {n k N : Nat} (hpos : 0 < n + k) :
    AtMost H n k N →
      (InitialNode T (n + k - 1) → InitialNode T N) :=
  fun a x =>
    ⟨a.1.representative H x.1,
      (a.1.level_le_terminalLevel H (by omega)).trans a.2⟩

theorem atMostCode_injective
    (H : SMTree S) {n k N : Nat} (hpos : 0 < n + k) :
    Function.Injective (atMostCode (T := T) H hpos :
      AtMost H n k N →
        (InitialNode T (n + k - 1) → InitialNode T N)) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  calc
    a.1.1 = ramseyApprox H (n + k) (a.1.representative H) :=
      (a.1.representative_top H).symm
    _ = ramseyApprox H (n + k) (b.1.representative H) := by
      apply ramseyApprox_eq_of_apply H
      intro x hx
      have hxTop : LevelTree.lev x ≤ n + k - 1 := by omega
      let xx : InitialNode T (n + k - 1) := ⟨x, hxTop⟩
      have hcode := congrArg Subtype.val (congrFun hab xx)
      exact hcode
    _ = b.1.1 := b.1.representative_top H

/-- Bounded nonempty finite approximations form a finite type. -/
theorem atMost_finite
    (H : SMTree S) {n k N : Nat} (hpos : 0 < n + k) :
    Finite (AtMost H n k N) := by
  classical
  letI : Fintype (InitialNode T (n + k - 1)) :=
    initialNodeFintype T (n + k - 1)
  letI : Fintype (InitialNode T N) :=
    initialNodeFintype T N
  exact Finite.of_injective
    (atMostCode (T := T) H hpos)
    (atMostCode_injective (T := T) H hpos)

/-- Strictly bounded approximations are finite. -/
theorem below_finite
    (H : SMTree S) {n k N : Nat} (hpos : 0 < n + k) :
    Finite (Below H n k N) := by
  letI : Finite (AtMost H n k N) :=
    atMost_finite (T := T) H hpos
  exact Finite.of_injective (fun a : Below H n k N =>
    (⟨a.1, Nat.le_of_lt a.2⟩ : AtMost H n k N)) (by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : AtMost H n k N => z.1) h)

/-- Exact-terminal approximations are finite. -/
theorem at_finite
    (H : SMTree S) {n k N : Nat} (hpos : 0 < n + k) :
    Finite (At H n k N) := by
  letI : Finite (AtMost H n k N) :=
    atMost_finite (T := T) H hpos
  exact Finite.of_injective (fun a : At H n k N =>
    (⟨a.1, a.2.le⟩ : AtMost H n k N)) (by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : AtMost H n k N => z.1) h)

end AM

/-- Literal finite composition of two shape approximations with the same
frozen prefix. -/
noncomputable def finiteShapeComp
    (H : SMTree S) {n m k : Nat}
    (f : AM H n m) (g : AM H n k) :
    AM H n k :=
  (MMap.comp H (f.representative H) (g.representative H)).toAM H n k
    (MMap.comp_fixesBelow H
      (f.representative H) (g.representative H) n
      (f.representative_fixesBelow H)
      (g.representative_fixesBelow H))

/-- The chosen representative of a toAM approximation has the expected
terminal level. -/
theorem MMap.toAM_terminalLevel
    (H : SMTree S) (F : MMap H) (n k : Nat)
    (hF : F.FixesBelow H n) (hpos : 0 < n + k) :
    ((F.toAM H n k hF).terminalLevel H) =
      H.levelMap F.map (n + k - 1) := by
  obtain ⟨x, hx⟩ := H.level_nonempty (n + k - 1)
  have hxlt : LevelTree.lev x < n + k := by
    rw [hx]
    omega
  unfold AM.terminalLevel
  calc
    H.levelMap ((F.toAM H n k hF).representative H).map (n + k - 1) =
        LevelTree.lev ((F.toAM H n k hF).representative H x) := by
      simpa [hx] using
        H.levelMap_eq ((F.toAM H n k hF).representative H).map (a := x)
    _ = LevelTree.lev (F x) := by
      exact congrArg LevelTree.lev
        (MMap.toAM_representative_agrees H F n k hF x hxlt)
    _ = H.levelMap F.map (n + k - 1) := by
      simpa [hx] using (H.levelMap_eq F.map (a := x)).symm

/-- If the inner approximation ends before the outer approximation's source
segment, finite composition cannot end above the outer approximation. -/
theorem finiteShapeComp_terminalLevel_le
    (H : SMTree S) {n m k : Nat}
    (hm : 0 < m) (hk : 0 < k)
    (f : AM H n m) (g : AM H n k)
    (hg : g.terminalLevel H < n + m) :
    (finiteShapeComp H f g).terminalLevel H ≤ f.terminalLevel H := by
  let F := f.representative H
  let G := g.representative H
  have hfix :
      (MMap.comp H F G).FixesBelow H n :=
    MMap.comp_fixesBelow H F G n
      (f.representative_fixesBelow H)
      (g.representative_fixesBelow H)
  unfold finiteShapeComp
  rw [MMap.toAM_terminalLevel H (MMap.comp H F G) n k hfix (by omega)]
  rw [H.levelMap_comp F G (n + k - 1)]
  change
    H.levelMap F.map (g.terminalLevel H) ≤ f.terminalLevel H
  have hg' : g.terminalLevel H ≤ n + m - 1 := by
    omega
  unfold AM.terminalLevel
  exact (H.levelMap_strictMono F.map).monotone hg'


end SMTree
end SuccessorTree

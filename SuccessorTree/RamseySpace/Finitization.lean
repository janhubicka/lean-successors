import SuccessorTree.RamseySpace.Basic
import RamseySpace.Finitization
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Finitization for the successor-tree Ramsey space

A finite factor from an approximation of length n+1 to one of length m+1
is the restriction of an M-map K which sends the source initial segment
through level n into the target initial segment through level m and makes the
obvious composition square commute.

This is the finite counterpart of right composition of M-maps.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- The initial tree segment through level n is finite. -/
theorem levelLe_finite (n : Nat) :
    Set.Finite {a : T | LevelTree.lev a ≤ n} := by
  have hEq :
      {a : T | LevelTree.lev a ≤ n} =
        ⋃ i : Fin (n + 1), {a : T | LevelTree.lev a = i.1} := by
    ext a
    constructor
    · intro ha
      have hlt : LevelTree.lev a < n + 1 := by omega
      refine Set.mem_iUnion.2 ⟨⟨LevelTree.lev a, hlt⟩, ?_⟩
      rfl
    · intro ha
      rcases Set.mem_iUnion.1 ha with ⟨i, hi⟩
      change LevelTree.lev a = i.1 at hi
      omega
  rw [hEq]
  exact Set.finite_iUnion (fun i : Fin (n + 1) =>
    LevelTree.level_finite i.1)

/-- Nodes in an initial tree segment, as a finite type. -/
abbrev InitialNode (T : Type u) [PartialOrder T] [LevelTree T] (n : Nat) :=
  {a : T // LevelTree.lev a ≤ n}

noncomputable instance initialNodeFintype
    (T : Type u) [PartialOrder T] [LevelTree T] (n : Nat) :
    Fintype (InitialNode T n) :=
  Set.Finite.fintype (levelLe_finite (T := T) n)

/-- Every shape-preserving map sends level n to level at least n. -/
theorem levelMap_id_le (H : SMTree S) (F : ShapeMap S) (n : Nat) :
    n ≤ H.levelMap F n := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hstep :=
        H.levelMap_strictMono F (Nat.lt_succ_self n)
      omega

/-- A finite composition witness between two nonempty approximations. -/
structure RamseyFiniteFactor (H : SMTree S) {n m : Nat}
    (a : RamseyApprox H (n + 1)) (b : RamseyApprox H (m + 1)) where
  map : MMap H
  bound : ∀ x : InitialNode T n, LevelTree.lev (map x.1) ≤ m
  agrees :
    ∀ x : InitialNode T n,
      a.1 x = b.1 ⟨map x.1, bound x⟩

/-- Finitary reduction on finite approximations.

The empty approximation is below every approximation. A nonempty
approximation cannot lie below the empty one. -/
def RamseyLeFin (H : SMTree S) :
    (ramseyApproximationSystem H).FiniteApprox →
      (ramseyApproximationSystem H).FiniteApprox → Prop
  | ⟨0, _⟩, _ => True
  | ⟨_ + 1, _⟩, ⟨0, _⟩ => False
  | ⟨n + 1, a⟩, ⟨m + 1, b⟩ =>
      Nonempty (RamseyFiniteFactor H a b)

theorem ramseyLeFin_refl (H : SMTree S)
    (a : (ramseyApproximationSystem H).FiniteApprox) :
    RamseyLeFin H a a := by
  rcases a with ⟨n, a⟩
  cases n with
  | zero =>
      trivial
  | succ n =>
      refine ⟨{
        map := MMap.id H
        bound := ?_
        agrees := ?_
      }⟩
      · intro x
        simpa using x.2
      · intro x
        rfl

theorem ramseyLeFin_trans (H : SMTree S)
    {a b c : (ramseyApproximationSystem H).FiniteApprox}
    (hab : RamseyLeFin H a b) (hbc : RamseyLeFin H b c) :
    RamseyLeFin H a c := by
  rcases a with ⟨na, a⟩
  rcases b with ⟨nb, b⟩
  rcases c with ⟨nc, c⟩
  cases na with
  | zero =>
      trivial
  | succ na =>
      cases nb with
      | zero =>
          contradiction
      | succ nb =>
          cases nc with
          | zero =>
              contradiction
          | succ nc =>
              rcases hab with ⟨f⟩
              rcases hbc with ⟨g⟩
              refine ⟨{
                map := MMap.comp H g.map f.map
                bound := ?_
                agrees := ?_
              }⟩
              · intro x
                let y : InitialNode T nb :=
                  ⟨f.map x.1, f.bound x⟩
                simpa [MMap.comp_apply] using g.bound y
              · intro x
                let y : InitialNode T nb :=
                  ⟨f.map x.1, f.bound x⟩
                calc
                  a.1 x = b.1 y := f.agrees x
                  _ = c.1 ⟨g.map y.1, g.bound y⟩ := g.agrees y
                  _ = c.1
                      ⟨(MMap.comp H g.map f.map) x.1,
                        by
                          simpa [MMap.comp_apply] using g.bound y⟩ := by
                        rfl

/-- Finitary reduction can only increase the approximation index. -/
theorem ramseyLeFin_level_le (H : SMTree S)
    {a b : (ramseyApproximationSystem H).FiniteApprox}
    (hab : RamseyLeFin H a b) :
    a.1 ≤ b.1 := by
  rcases a with ⟨na, a⟩
  rcases b with ⟨nb, b⟩
  cases na with
  | zero =>
      omega
  | succ na =>
      cases nb with
      | zero =>
          contradiction
      | succ nb =>
          rcases hab with ⟨f⟩
          obtain ⟨x, hx⟩ := H.level_nonempty na
          let xx : InitialNode T na := ⟨x, by omega⟩
          have hbound := f.bound xx
          have hmap :
              H.levelMap f.map.map na =
                LevelTree.lev (f.map x) := by
            simpa [hx] using H.levelMap_eq f.map.map (a := x)
          have hid := H.levelMap_id_le f.map.map na
          omega

end SMTree
end SuccessorTree

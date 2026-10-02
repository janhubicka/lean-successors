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

/-- A genuine right-composition reduction induces finite reductions at every
approximation level. -/
theorem ramseyLeFin_of_reduction (H : SMTree S) {F G : MMap H}
    (hFG : RamseyReduction H F G) (n : Nat) :
    ∃ m,
      RamseyLeFin H
        ((ramseyApproximationSystem H).finiteApprox n F)
        ((ramseyApproximationSystem H).finiteApprox m G) := by
  rcases hFG with ⟨K, hK⟩
  cases n with
  | zero =>
      refine ⟨0, ?_⟩
      trivial
  | succ n =>
      let m := H.levelMap K.map n
      refine ⟨m + 1, ?_⟩
      change Nonempty
        (RamseyFiniteFactor H
          (ramseyApprox H (n + 1) F)
          (ramseyApprox H (m + 1) G))
      refine ⟨{
        map := K
        bound := ?_
        agrees := ?_
      }⟩
      · intro x
        calc
          LevelTree.lev (K x.1) =
              H.levelMap K.map (LevelTree.lev x.1) :=
            (H.levelMap_eq K.map (a := x.1)).symm
          _ ≤ H.levelMap K.map n :=
            (H.levelMap_strictMono K.map).monotone x.2
          _ = m := rfl
      · intro x
        change F x.1 = G (K x.1)
        exact hK x.1

/-- Local finite factors through a fixed outer map agree on overlaps. This is
the compactness mechanism behind the converse direction of A.2. -/
theorem exists_local_factor_of_ramseyLeFin
    (H : SMTree S) {F G : MMap H}
    (hlocal :
      ∀ n, ∃ m,
        RamseyLeFin H
          ((ramseyApproximationSystem H).finiteApprox n F)
          ((ramseyApproximationSystem H).finiteApprox m G))
    (i : Nat) :
    ∃ K : MMap H, ∀ x : T, LevelTree.lev x ≤ i → F x = G (K x) := by
  rcases hlocal (i + 1) with ⟨m, hm⟩
  cases m with
  | zero =>
      change False at hm
      contradiction
  | succ m =>
      change Nonempty
        (RamseyFiniteFactor H
          (ramseyApprox H (i + 1) F)
          (ramseyApprox H (m + 1) G)) at hm
      rcases hm with ⟨fac⟩
      refine ⟨fac.map, ?_⟩
      intro x hx
      have h := fac.agrees (⟨x, hx⟩ : InitialNode T i)
      change F x = G (fac.map x) at h
      exact h

/-- If every finite approximation of F factors through some finite
approximation of G, the factor maps fuse to a single M-map K with F = G ∘ K. -/
theorem reduction_of_ramseyLeFin_all
    (H : SMTree S) {F G : MMap H}
    (hlocal :
      ∀ n, ∃ m,
        RamseyLeFin H
          ((ramseyApproximationSystem H).finiteApprox n F)
          ((ramseyApproximationSystem H).finiteApprox m G)) :
    RamseyReduction H F G := by
  classical
  have hex :
      ∀ i : Nat, ∃ K : MMap H,
        ∀ x : T, LevelTree.lev x ≤ i → F x = G (K x) :=
    fun i => H.exists_local_factor_of_ramseyLeFin hlocal i
  let K : Nat → MMap H := fun i => Classical.choose (hex i)
  have hK :
      ∀ i x, LevelTree.lev x ≤ i → F x = G (K i x) := by
    intro i x hx
    exact (Classical.choose_spec (hex i)) x hx
  have hstable : ShapeMap.FusionStable (fun i => (K i).map) := by
    intro i x hx
    apply G.map.injective
    exact (hK i x hx).symm.trans
      (hK (i + 1) x (hx.trans (Nat.le_succ i)))
  let Lmap : ShapeMap S :=
    ShapeMap.fusionLimit (fun i => (K i).map) hstable
  have hLmem : Lmap ∈ H.M :=
    H.fusion_mem (fun i => (K i).map) (fun i => (K i).mem) hstable
  let L : MMap H := ⟨Lmap, hLmem⟩
  refine ⟨L, ?_⟩
  intro x
  calc
    F x = G (K (LevelTree.lev x) x) :=
      hK (LevelTree.lev x) x le_rfl
    _ = G (L x) := by
      congr 1
      rfl

/-- A.2's order clause for the proposed finite reduction relation. -/
theorem ramseyReduction_iff_ramseyLeFin
    (H : SMTree S) (F G : MMap H) :
    RamseyReduction H F G ↔
      ∀ n, ∃ m,
        RamseyLeFin H
          ((ramseyApproximationSystem H).finiteApprox n F)
          ((ramseyApproximationSystem H).finiteApprox m G) := by
  constructor
  · intro h n
    exact H.ramseyLeFin_of_reduction h n
  · intro h
    exact H.reduction_of_ramseyLeFin_all h


/-- An initial finite approximation is literally the restriction of the longer
one on its smaller source segment. -/
theorem ramseyApprox_apply_of_initial {n m : Nat}
    (H : SMTree S) {a : RamseyApprox H (n + 1)}
    {b : RamseyApprox H (m + 1)}
    (hab : (ramseyApproximationSystem H).IsInitial a b)
    (x : InitialNode T n) :
    a.1 x =
      b.1 ⟨x.1, x.2.trans (by omega : n ≤ m)⟩ := by
  rcases hab with ⟨hnm, X, hXa, hXb⟩
  have hnm' : n ≤ m := by omega
  have hna := congrArg Subtype.val hXa
  have hmb := congrArg Subtype.val hXb
  change X.restrictLe H n = a.1 at hna
  change X.restrictLe H m = b.1 at hmb
  calc
    a.1 x = X x.1 := by
      simpa [MMap.restrictLe] using (congrFun hna x).symm
    _ = b.1 ⟨x.1, x.2.trans hnm'⟩ := by
      simpa [MMap.restrictLe] using
        congrFun hmb ⟨x.1, x.2.trans hnm'⟩

/-- A.2(3): a prefix of a finite factor again factors through the same
right-hand approximation. -/
theorem ramseyLeFin_prefix
    (H : SMTree S)
    {n m k : Nat}
    {a : (ramseyApproximationSystem H).Approx n}
    {b : (ramseyApproximationSystem H).Approx m}
    {c : (ramseyApproximationSystem H).Approx k}
    (hab : (ramseyApproximationSystem H).IsInitial a b)
    (hbc : RamseyLeFin H ⟨m, b⟩ ⟨k, c⟩) :
    ∃ (j : Nat) (d : (ramseyApproximationSystem H).Approx j),
      (ramseyApproximationSystem H).IsInitial d c ∧
        RamseyLeFin H ⟨n, a⟩ ⟨j, d⟩ := by
  refine ⟨k, c, (ramseyApproximationSystem H).isInitial_refl c, ?_⟩
  cases n with
  | zero =>
      trivial
  | succ n =>
      cases m with
      | zero =>
          exfalso
          exact (Nat.not_succ_le_zero n) hab.1
      | succ m =>
          cases k with
          | zero =>
              contradiction
          | succ k =>
              rcases hbc with ⟨fac⟩
              have hnm : n ≤ m := by omega
              refine ⟨{
                map := fac.map
                bound := ?_
                agrees := ?_
              }⟩
              · intro x
                let y : InitialNode T m :=
                  ⟨x.1, x.2.trans hnm⟩
                exact fac.bound y
              · intro x
                let y : InitialNode T m :=
                  ⟨x.1, x.2.trans hnm⟩
                calc
                  a.1 x = b.1 y :=
                    H.ramseyApprox_apply_of_initial hab x
                  _ = c.1 ⟨fac.map y.1, fac.bound y⟩ :=
                    fac.agrees y
                  _ = c.1
                      ⟨fac.map x.1,
                        by
                          exact fac.bound y⟩ := by
                        rfl


end SMTree
end SuccessorTree

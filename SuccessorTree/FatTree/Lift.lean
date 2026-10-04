import SuccessorTree.FatTree.Basic

/-!
# Lift along a fat subtree

This is the recursive `Lift_U(X,k)` operation from the manuscript.  We keep
its source index explicit in Lean; the paper can infer it from the level on
which `X` lives because the cut is strictly increasing.

Besides the level bookkeeping, this file proves the locality fact needed for
composition of fat-tree reductions: a lifted node remembers its unique
ancestor on the starting cut.  Consequently an inclusion proved for the whole
starting level automatically restricts to any subset of that level.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Nodes on one tree level. -/
def TreeLevel (n : Nat) : Set T :=
  {x | LevelTree.lev x = n}

/-- Immediate successors of members of a set. -/
def ImmediateSuccessors (X : Set T) : Set T :=
  {y | ∃ x ∈ X, x ⋖ y}

private theorem list_map_eq_self_of_mem_eq
    {α : Type u} (p : List α) (f : α → α)
    (h : ∀ x ∈ p, f x = x) :
    p.map f = p := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
      have hx : f x = x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons]
      rw [hx, ih hxs]

namespace MMap

/-- If an M-map fixes everything strictly below level `n`, then every
level-`n` node lies below its image.  This is the tree-theoretic reason that
fat-tree lifts remember their starting ancestor. -/
theorem le_apply_of_fixesBelow
    (H : SMTree S) (F : MMap H) {n : Nat}
    (hF : F.FixesBelow H n)
    {x : T} (hx : LevelTree.lev x = n) :
    x ≤ F x := by
  cases n with
  | zero =>
      exact F.map.root_le' hx
  | succ n =>
      have hnle : n ≤ LevelTree.lev x := by omega
      let p := LevelTree.ancestor x n hnle
      have hpx : p ≤ x := LevelTree.ancestor_le x n hnle
      have hpLevel : LevelTree.lev p = n :=
        LevelTree.level_ancestor x n hnle
      have hcov : p ⋖ x := by
        apply LevelTree.covBy_of_le_level_succ hpx
        omega
      obtain ⟨params, c, hsucc⟩ := S.s3 hcov
      have hpfix : F p = p := by
        apply hF p
        omega
      have hparams : params.map F = params := by
        apply list_map_eq_self_of_mem_eq
        intro y hy
        apply hF y
        have hylt := S.parameter_level_lt hsucc hy
        omega
      obtain ⟨d, hd, hdx⟩ := F.map.weak_succ' hsucc
      have hd' : S.succ p params c = some d := by
        simpa [hpfix, hparams] using hd
      have hdeq : d = x :=
        Option.some.inj (hd'.symm.trans hsucc)
      simpa [hdeq] using hdx

end MMap

namespace FatTree

variable (H : SMTree S)

/-- Immediate successors are monotone in the starting set. -/
theorem immediateSuccessors_mono
    {X Y : Set T} (hXY : X ⊆ Y) :
    ImmediateSuccessors (T := T) X ⊆ ImmediateSuccessors (T := T) Y := by
  intro z hz
  rcases hz with ⟨x, hx, hxz⟩
  exact ⟨x, hXY hx, hxz⟩

/-- Immediate successors of a set on level `n` lie on level `n+1`. -/
theorem immediateSuccessors_subset_level
    {n : Nat} {X : Set T} (hX : X ⊆ TreeLevel (T := T) n) :
    ImmediateSuccessors (T := T) X ⊆ TreeLevel (T := T) (n + 1) := by
  intro y hy
  rcases hy with ⟨x, hxX, hxy⟩
  have hx : LevelTree.lev x = n := hX hxX
  change LevelTree.lev y = n + 1
  calc
    LevelTree.lev y = LevelTree.lev x + 1 := LevelTree.covBy_level_eq hxy
    _ = n + 1 := by rw [hx]

/-- One step of the manuscript's lift operation. -/
noncomputable def oneLift (U : FatTree H) (i : Nat) (X : Set T) : Set T :=
  U.rowExtension H i '' ImmediateSuccessors (T := T) X

/-- One-step lifting is monotone in its starting set. -/
theorem oneLift_mono (U : FatTree H) (i : Nat)
    {X Y : Set T} (hXY : X ⊆ Y) :
    U.oneLift H i X ⊆ U.oneLift H i Y := by
  intro z hz
  rcases hz with ⟨y, hy, rfl⟩
  exact ⟨y, immediateSuccessors_mono hXY hy, rfl⟩

/-- The canonical row extension fixes everything strictly below its source
cut. -/
theorem rowExtension_fixesBelow (U : FatTree H) (i : Nat) :
    (U.rowExtension H i).FixesBelow H (U.cut i) := by
  intro x hx
  calc
    U.rowExtension H i x =
        (U.row i).representative H x :=
      U.rowExtension_agrees H i x (Nat.le_of_lt hx)
    _ = x :=
      (U.row i).representative_fixesBelow H x hx

/-- A source-cut node lies below its image under the canonical row
extension. -/
theorem le_rowExtension_at_cut (U : FatTree H) (i : Nat)
    {x : T} (hx : LevelTree.lev x = U.cut i) :
    x ≤ U.rowExtension H i x := by
  exact (U.rowExtension H i).le_apply_of_fixesBelow
    H (U.rowExtension_fixesBelow H i) hx

/-- The parenthetical level claim in Definition `def:lift`. -/
theorem oneLift_subset_nextLevel (U : FatTree H) (i : Nat)
    {X : Set T} (hX : X ⊆ TreeLevel (T := T) (U.cut i)) :
    U.oneLift H i X ⊆ TreeLevel (T := T) (U.cut (i + 1)) := by
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  have hzlev : LevelTree.lev z = U.cut i + 1 :=
    immediateSuccessors_subset_level hX hz
  change LevelTree.lev (U.rowExtension H i z) = U.cut (i + 1)
  calc
    LevelTree.lev (U.rowExtension H i z) =
        H.levelMap (U.rowExtension H i).map (LevelTree.lev z) :=
      (H.levelMap_eq (U.rowExtension H i).map (a := z)).symm
    _ = H.levelMap (U.rowExtension H i).map (U.cut i + 1) := by rw [hzlev]
    _ = U.cut (i + 1) := U.rowExtension_level_succ H i

/-- Every node produced by one lift lies above a member of the starting set. -/
theorem oneLift_descends (U : FatTree H) (i : Nat)
    {X : Set T} (hX : X ⊆ TreeLevel (T := T) (U.cut i))
    {z : T} (hz : z ∈ U.oneLift H i X) :
    ∃ x ∈ X, x ≤ z := by
  rcases hz with ⟨y, hy, rfl⟩
  rcases hy with ⟨x, hx, hxy⟩
  refine ⟨x, hx, ?_⟩
  have hxLevel : LevelTree.lev x = U.cut i := hX hx
  have hxrow : x ≤ U.rowExtension H i x :=
    U.le_rowExtension_at_cut H i hxLevel
  have hmap :
      U.rowExtension H i x ≤ U.rowExtension H i y :=
    (U.rowExtension H i).map.map_le_of_le hxy.le
  exact hxrow.trans hmap

/-- Source locality for one row.

If a node lies in the lift of the whole source level and lies above a member
of `X`, then it already lies in the lift of `X`. -/
theorem oneLift_mem_of_mem_full_of_source
    (U : FatTree H) (i : Nat)
    {X : Set T} (hX : X ⊆ TreeLevel (T := T) (U.cut i))
    {z : T}
    (hz :
      z ∈ U.oneLift H i (TreeLevel (T := T) (U.cut i)))
    (hsource : ∃ x ∈ X, x ≤ z) :
    z ∈ U.oneLift H i X := by
  rcases hz with ⟨y, hy, rfl⟩
  rcases hy with ⟨x₀, hx₀Level, hx₀y⟩
  rcases hsource with ⟨x, hx, hxz⟩
  have hxLevel : LevelTree.lev x = U.cut i := hX hx
  have hx₀Level' : LevelTree.lev x₀ = U.cut i := hx₀Level
  have hx₀row : x₀ ≤ U.rowExtension H i x₀ :=
    U.le_rowExtension_at_cut H i hx₀Level'
  have hx₀z :
      x₀ ≤ U.rowExtension H i y :=
    hx₀row.trans ((U.rowExtension H i).map.map_le_of_le hx₀y.le)
  have hxx₀ : x = x₀ := by
    rcases LevelTree.comparable_below hxz hx₀z with h | h
    · exact LevelTree.same_level_of_le h
        (hxLevel.trans hx₀Level'.symm)
    · exact (LevelTree.same_level_of_le h
        (hx₀Level'.trans hxLevel.symm)).symm
  refine ⟨y, ?_, rfl⟩
  exact ⟨x₀, by simpa [hxx₀] using hx, hx₀y⟩

/-- Iterate the one-step lift for a prescribed number of fat-tree rows. -/
noncomputable def liftSteps (U : FatTree H) :
    (i steps : Nat) → Set T → Set T
  | _, 0, X => X
  | i, steps + 1, X =>
      liftSteps U (i + 1) steps (U.oneLift H i X)

@[simp] theorem liftSteps_zero (U : FatTree H) (i : Nat) (X : Set T) :
    U.liftSteps H i 0 X = X := rfl

@[simp] theorem liftSteps_succ (U : FatTree H)
    (i steps : Nat) (X : Set T) :
    U.liftSteps H i (steps + 1) X =
      U.liftSteps H (i + 1) steps (U.oneLift H i X) := rfl

/-- Iterating for `a+b` rows is the same as lifting for `a` rows
and then for the remaining `b` rows. -/
theorem liftSteps_add (U : FatTree H)
    (i a b : Nat) (X : Set T) :
    U.liftSteps H i (a + b) X =
      U.liftSteps H (i + a) b (U.liftSteps H i a X) := by
  induction a generalizing i X with
  | zero =>
      simp
  | succ a ih =>
      rw [Nat.succ_add, liftSteps_succ, liftSteps_succ]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i := i + 1) (X := U.oneLift H i X)

/-- Iterated lifting is monotone in its starting set. -/
theorem liftSteps_mono (U : FatTree H)
    (i steps : Nat) {X Y : Set T}
    (hXY : X ⊆ Y) :
    U.liftSteps H i steps X ⊆ U.liftSteps H i steps Y := by
  induction steps generalizing i X Y with
  | zero =>
      exact hXY
  | succ steps ih =>
      exact ih (i := i + 1)
        (X := U.oneLift H i X) (Y := U.oneLift H i Y)
        (U.oneLift_mono H i hXY)

/-- Lifting preserves the intended cut level. -/
theorem liftSteps_subset_level (U : FatTree H)
    (i steps : Nat) {X : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut i)) :
    U.liftSteps H i steps X ⊆
      TreeLevel (T := T) (U.cut (i + steps)) := by
  induction steps generalizing i X with
  | zero =>
      simpa using hX
  | succ steps ih =>
      have hnext : U.oneLift H i X ⊆
          TreeLevel (T := T) (U.cut (i + 1)) :=
        U.oneLift_subset_nextLevel H i hX
      have hrec := ih (i := i + 1) (X := U.oneLift H i X) hnext
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

/-- Every iterated lift node lies above a member of its starting set. -/
theorem liftSteps_descends (U : FatTree H)
    (i steps : Nat) {X : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut i))
    {z : T} (hz : z ∈ U.liftSteps H i steps X) :
    ∃ x ∈ X, x ≤ z := by
  induction steps generalizing i X z with
  | zero =>
      exact ⟨z, hz, le_rfl⟩
  | succ steps ih =>
      have hnext :
          U.oneLift H i X ⊆
            TreeLevel (T := T) (U.cut (i + 1)) :=
        U.oneLift_subset_nextLevel H i hX
      change
        z ∈ U.liftSteps H (i + 1) steps (U.oneLift H i X) at hz
      rcases ih (i := i + 1) (X := U.oneLift H i X)
          hnext hz with ⟨y, hy, hyz⟩
      rcases U.oneLift_descends H i hX hy with
        ⟨x, hx, hxy⟩
      exact ⟨x, hx, hxy.trans hyz⟩

/-- Locality for an iterated lift.

The endpoint of a lift determines its source ancestor.  Therefore if `z`
is obtained by lifting a level set `Y`, and `z` lies above some member of
another level set `X` on the same starting cut, then `z` is already
obtained by lifting `X`. -/
theorem liftSteps_mem_of_mem_of_source (U : FatTree H)
    (i steps : Nat) {X Y : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut i))
    (hY : Y ⊆ TreeLevel (T := T) (U.cut i))
    {z : T}
    (hz : z ∈ U.liftSteps H i steps Y)
    (hsource : ∃ x ∈ X, x ≤ z) :
    z ∈ U.liftSteps H i steps X := by
  induction steps generalizing i X Y z with
  | zero =>
      rcases hsource with ⟨x, hx, hxz⟩
      have hxLevel : LevelTree.lev x = U.cut i := hX hx
      have hzLevel : LevelTree.lev z = U.cut i := hY hz
      have hxz' : x = z :=
        LevelTree.same_level_of_le hxz (hxLevel.trans hzLevel.symm)
      simpa [← hxz'] using hx
  | succ steps ih =>
      have hXnext :
          U.oneLift H i X ⊆
            TreeLevel (T := T) (U.cut (i + 1)) :=
        U.oneLift_subset_nextLevel H i hX
      have hYnext :
          U.oneLift H i Y ⊆
            TreeLevel (T := T) (U.cut (i + 1)) :=
        U.oneLift_subset_nextLevel H i hY
      change
        z ∈ U.liftSteps H (i + 1) steps (U.oneLift H i Y) at hz
      rcases U.liftSteps_descends H (i + 1) steps hYnext hz with
        ⟨y, hy, hyz⟩
      rcases hsource with ⟨x, hx, hxz⟩
      have hxLevel : LevelTree.lev x = U.cut i := hX hx
      have hyLevel : LevelTree.lev y = U.cut (i + 1) := hYnext hy
      have hxy : x ≤ y := by
        rcases LevelTree.comparable_below hxz hyz with h | h
        · exact h
        · have hlev := LevelTree.level_le_of_le h
          have hcut := U.cut_lt_succ H i
          omega
      have hyFull :
          y ∈ U.oneLift H i (TreeLevel (T := T) (U.cut i)) := by
        exact U.oneLift_mono H i hY hy
      have hyX : y ∈ U.oneLift H i X :=
        U.oneLift_mem_of_mem_full_of_source H i hX hyFull
          ⟨x, hx, hxy⟩
      exact ih (i := i + 1)
        (X := U.oneLift H i X) (Y := U.oneLift H i Y)
        hXnext hYnext hz ⟨y, hyX, hyz⟩

/-- Paper notation `Lift_U(X,k)`, with the source cut `i` explicit. -/
noncomputable def liftTo (U : FatTree H)
    (i k : Nat) (hik : i ≤ k) (X : Set T) : Set T :=
  U.liftSteps H i (k - i) X

/-- Lifting across exactly one fat-tree row is the one-step lift. -/
theorem liftTo_succ (U : FatTree H) (i : Nat) (X : Set T) :
    U.liftTo H i (i + 1) (by omega) X = U.oneLift H i X := by
  unfold liftTo
  have hsub : i + 1 - i = 1 := by omega
  rw [hsub, liftSteps_succ, liftSteps_zero]

/-- The explicit-source version of the lift lands on the target cut. -/
theorem liftTo_subset_level (U : FatTree H)
    (i k : Nat) (hik : i ≤ k) {X : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut i)) :
    U.liftTo H i k hik X ⊆ TreeLevel (T := T) (U.cut k) := by
  change U.liftSteps H i (k - i) X ⊆ TreeLevel (T := T) (U.cut k)
  have h := U.liftSteps_subset_level H i (k - i) hX
  have hidx : i + (k - i) = k := by omega
  simpa [hidx] using h

/-- A lift through an intermediate cut factors as the two successive
lifts through that cut. -/
theorem liftTo_split (U : FatTree H)
    (i j k : Nat) (hij : i ≤ j) (hjk : j ≤ k)
    (X : Set T) :
    U.liftTo H i k (hij.trans hjk) X =
      U.liftTo H j k hjk (U.liftTo H i j hij X) := by
  change
    U.liftSteps H i (k - i) X =
      U.liftSteps H j (k - j) (U.liftSteps H i (j - i) X)
  have hsum : k - i = (j - i) + (k - j) := by omega
  have hidx : i + (j - i) = j := by omega
  rw [hsum, U.liftSteps_add H i (j - i) (k - j) X, hidx]

/-- `liftTo` is monotone in the starting set. -/
theorem liftTo_mono (U : FatTree H)
    (i k : Nat) (hik : i ≤ k)
    {X Y : Set T} (hXY : X ⊆ Y) :
    U.liftTo H i k hik X ⊆ U.liftTo H i k hik Y := by
  exact U.liftSteps_mono H i (k - i) hXY

/-- Every `liftTo` endpoint lies above a member of its starting set. -/
theorem liftTo_descends (U : FatTree H)
    (i k : Nat) (hik : i ≤ k)
    {X : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut i))
    {z : T} (hz : z ∈ U.liftTo H i k hik X) :
    ∃ x ∈ X, x ≤ z := by
  exact U.liftSteps_descends H i (k - i) hX hz

/-- Source locality in the paper's `Lift_U(X,k)` notation. -/
theorem liftTo_mem_of_mem_of_source (U : FatTree H)
    (i k : Nat) (hik : i ≤ k)
    {X Y : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut i))
    (hY : Y ⊆ TreeLevel (T := T) (U.cut i))
    {z : T}
    (hz : z ∈ U.liftTo H i k hik Y)
    (hsource : ∃ x ∈ X, x ≤ z) :
    z ∈ U.liftTo H i k hik X := by
  exact U.liftSteps_mem_of_mem_of_source H i (k - i)
    hX hY hz hsource

/-- The empty set stays empty under lifting. -/
@[simp] theorem oneLift_empty (U : FatTree H) (i : Nat) :
    U.oneLift H i (∅ : Set T) = ∅ := by
  ext y
  simp [oneLift, ImmediateSuccessors]

@[simp] theorem liftSteps_empty (U : FatTree H) (i steps : Nat) :
    U.liftSteps H i steps (∅ : Set T) = ∅ := by
  induction steps generalizing i with
  | zero => rfl
  | succ steps ih =>
      rw [liftSteps_succ, oneLift_empty]
      exact ih (i + 1)

end FatTree

namespace FiniteFatTree

variable (H : SMTree S)

/-- Row extensions commute with taking a finite prefix. -/
theorem initialSegment_rowExtension (U : FiniteFatTree H)
    (n : Nat) (hn : n ≤ U.height)
    (i : Fin (U.initialSegment H n hn).height) :
    (U.initialSegment H n hn).rowExtension H i =
      U.rowExtension H
        (⟨i.1, by
          have hi : i.1 < n := by
            simpa using i.2
          exact lt_of_lt_of_le hi hn⟩ : Fin U.height) := by
  rfl

/-- A canonical finite row extension fixes everything below its source cut. -/
theorem rowExtension_fixesBelow (U : FiniteFatTree H)
    (i : Fin U.height) :
    (U.rowExtension H i).FixesBelow H (U.cut i.castSucc) := by
  intro x hx
  calc
    U.rowExtension H i x =
        (U.row i).representative H x :=
      U.rowExtension_agrees H i x (Nat.le_of_lt hx)
    _ = x :=
      (U.row i).representative_fixesBelow H x hx

/-- A source-cut node lies below its image under a finite row extension. -/
theorem le_rowExtension_at_cut (U : FiniteFatTree H)
    (i : Fin U.height) {x : T}
    (hx : LevelTree.lev x = U.cut i.castSucc) :
    x ≤ U.rowExtension H i x := by
  exact (U.rowExtension H i).le_apply_of_fixesBelow
    H (U.rowExtension_fixesBelow H i) hx

/-- One step of lift inside a finite fat tree. -/
noncomputable def oneLift (U : FiniteFatTree H)
    (i : Fin U.height) (X : Set T) : Set T :=
  U.rowExtension H i '' ImmediateSuccessors (T := T) X

/-- One-step lift is unchanged when computed inside a prefix that
still contains the selected row. -/
theorem initialSegment_oneLift (U : FiniteFatTree H)
    (n : Nat) (hn : n ≤ U.height)
    (i : Fin (U.initialSegment H n hn).height) (X : Set T) :
    (U.initialSegment H n hn).oneLift H i X =
      U.oneLift H
        (⟨i.1, by
          have hi : i.1 < n := by
            simpa using i.2
          exact lt_of_lt_of_le hi hn⟩ : Fin U.height) X := by
  unfold oneLift
  rw [U.initialSegment_rowExtension H n hn i]

/-- Finite one-step lifting is monotone in the starting set. -/
theorem oneLift_mono (U : FiniteFatTree H)
    (i : Fin U.height) {X Y : Set T} (hXY : X ⊆ Y) :
    U.oneLift H i X ⊆ U.oneLift H i Y := by
  intro z hz
  rcases hz with ⟨y, hy, rfl⟩
  exact ⟨y, FatTree.immediateSuccessors_mono hXY hy, rfl⟩

/-- A finite one-row lift lands exactly on the next cut level. -/
theorem oneLift_subset_nextLevel (U : FiniteFatTree H)
    (i : Fin U.height) {X : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut i.castSucc)) :
    U.oneLift H i X ⊆
      TreeLevel (T := T) (U.cut i.succ) := by
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  have hzlev : LevelTree.lev z = U.cut i.castSucc + 1 :=
    FatTree.immediateSuccessors_subset_level hX hz
  change LevelTree.lev (U.rowExtension H i z) = U.cut i.succ
  calc
    LevelTree.lev (U.rowExtension H i z) =
        H.levelMap (U.rowExtension H i).map (LevelTree.lev z) :=
      (H.levelMap_eq (U.rowExtension H i).map (a := z)).symm
    _ = H.levelMap (U.rowExtension H i).map
          (U.cut i.castSucc + 1) := by rw [hzlev]
    _ = U.cut i.succ := U.rowExtension_level_succ H i

/-- Every node produced by one finite lift lies above a source node. -/
theorem oneLift_descends (U : FiniteFatTree H)
    (i : Fin U.height) {X : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut i.castSucc))
    {z : T} (hz : z ∈ U.oneLift H i X) :
    ∃ x ∈ X, x ≤ z := by
  rcases hz with ⟨y, hy, rfl⟩
  rcases hy with ⟨x, hx, hxy⟩
  refine ⟨x, hx, ?_⟩
  have hxLevel : LevelTree.lev x = U.cut i.castSucc := hX hx
  have hxrow : x ≤ U.rowExtension H i x :=
    U.le_rowExtension_at_cut H i hxLevel
  have hmap :
      U.rowExtension H i x ≤ U.rowExtension H i y :=
    (U.rowExtension H i).map.map_le_of_le hxy.le
  exact hxrow.trans hmap

/-- Source locality for one finite row. -/
theorem oneLift_mem_of_mem_full_of_source
    (U : FiniteFatTree H) (i : Fin U.height)
    {X : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut i.castSucc))
    {z : T}
    (hz :
      z ∈ U.oneLift H i
        (TreeLevel (T := T) (U.cut i.castSucc)))
    (hsource : ∃ x ∈ X, x ≤ z) :
    z ∈ U.oneLift H i X := by
  rcases hz with ⟨y, hy, rfl⟩
  rcases hy with ⟨x₀, hx₀Level, hx₀y⟩
  rcases hsource with ⟨x, hx, hxz⟩
  have hxLevel : LevelTree.lev x = U.cut i.castSucc := hX hx
  have hx₀Level' : LevelTree.lev x₀ = U.cut i.castSucc := hx₀Level
  have hx₀row : x₀ ≤ U.rowExtension H i x₀ :=
    U.le_rowExtension_at_cut H i hx₀Level'
  have hx₀z :
      x₀ ≤ U.rowExtension H i y :=
    hx₀row.trans ((U.rowExtension H i).map.map_le_of_le hx₀y.le)
  have hxx₀ : x = x₀ := by
    rcases LevelTree.comparable_below hxz hx₀z with h | h
    · exact LevelTree.same_level_of_le h
        (hxLevel.trans hx₀Level'.symm)
    · exact (LevelTree.same_level_of_le h
        (hx₀Level'.trans hxLevel.symm)).symm
  refine ⟨y, ?_, rfl⟩
  exact ⟨x₀, by simpa [hxx₀] using hx, hx₀y⟩

/-- Iterate finite rows.  The bound records that the terminal cut is
available; this is the finite analogue of `FatTree.liftSteps`. -/
noncomputable def liftSteps (U : FiniteFatTree H) :
    (i steps : Nat) → i + steps ≤ U.height → Set T → Set T
  | _, 0, _, X => X
  | i, steps + 1, h, X =>
      let rowIndex : Fin U.height := ⟨i, by omega⟩
      liftSteps U (i + 1) steps (by omega)
        (U.oneLift H rowIndex X)

@[simp] theorem liftSteps_zero (U : FiniteFatTree H)
    (i : Nat) (h : i + 0 ≤ U.height) (X : Set T) :
    U.liftSteps H i 0 h X = X := rfl

@[simp] theorem liftSteps_succ (U : FiniteFatTree H)
    (i steps : Nat) (h : i + (steps + 1) ≤ U.height)
    (X : Set T) :
    U.liftSteps H i (steps + 1) h X =
      U.liftSteps H (i + 1) steps (by omega)
        (U.oneLift H (⟨i, by omega⟩ : Fin U.height) X) := rfl

/-- Finite iterated lifting is monotone in its starting set. -/
theorem liftSteps_mono (U : FiniteFatTree H)
    (i steps : Nat) (h : i + steps ≤ U.height)
    {X Y : Set T} (hXY : X ⊆ Y) :
    U.liftSteps H i steps h X ⊆
      U.liftSteps H i steps h Y := by
  induction steps generalizing i X Y with
  | zero =>
      simpa using hXY
  | succ steps ih =>
      rw [U.liftSteps_succ H i steps h X,
          U.liftSteps_succ H i steps h Y]
      exact ih (i := i + 1) (by omega)
        (X := U.oneLift H (⟨i, by omega⟩ : Fin U.height) X)
        (Y := U.oneLift H (⟨i, by omega⟩ : Fin U.height) Y)
        (U.oneLift_mono H (⟨i, by omega⟩ : Fin U.height) hXY)

/-- A finite multi-row lift lands on the cut reached after the
specified number of rows. -/
theorem liftSteps_subset_level (U : FiniteFatTree H)
    (i steps : Nat) (h : i + steps ≤ U.height)
    {X : Set T}
    (hX : X ⊆
      TreeLevel (T := T) (U.cut (⟨i, by omega⟩ : Fin (U.height + 1)))) :
    U.liftSteps H i steps h X ⊆
      TreeLevel (T := T)
        (U.cut (⟨i + steps, by omega⟩ : Fin (U.height + 1))) := by
  induction steps generalizing i X with
  | zero =>
      simpa using hX
  | succ steps ih =>
      let ri : Fin U.height := ⟨i, by omega⟩
      have hXri :
          X ⊆ TreeLevel (T := T) (U.cut ri.castSucc) := by
        simpa [ri] using hX
      have hnext :
          U.oneLift H ri X ⊆
            TreeLevel (T := T) (U.cut ri.succ) :=
        U.oneLift_subset_nextLevel H ri hXri
      rw [U.liftSteps_succ H i steps h X]
      have hrec :=
        ih (i := i + 1) (by omega)
          (X := U.oneLift H ri X)
          (by simpa [ri] using hnext)
      simpa [ri, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

/-- Every endpoint of a finite multi-row lift lies above a node from the
starting set. -/
theorem liftSteps_descends (U : FiniteFatTree H)
    (i steps : Nat) (h : i + steps ≤ U.height)
    {X : Set T}
    (hX : X ⊆
      TreeLevel (T := T) (U.cut (⟨i, by omega⟩ : Fin (U.height + 1))))
    {z : T} (hz : z ∈ U.liftSteps H i steps h X) :
    ∃ x ∈ X, x ≤ z := by
  induction steps generalizing i X z with
  | zero =>
      exact ⟨z, hz, le_rfl⟩
  | succ steps ih =>
      let ri : Fin U.height := ⟨i, by omega⟩
      have hXri :
          X ⊆ TreeLevel (T := T) (U.cut ri.castSucc) := by
        simpa [ri] using hX
      have hnext :
          U.oneLift H ri X ⊆
            TreeLevel (T := T) (U.cut ri.succ) :=
        U.oneLift_subset_nextLevel H ri hXri
      rw [U.liftSteps_succ H i steps h X] at hz
      rcases ih (i := i + 1) (by omega)
          (X := U.oneLift H ri X)
          (by simpa [ri] using hnext) hz with
        ⟨y, hy, hyz⟩
      rcases U.oneLift_descends H ri hXri hy with
        ⟨x, hx, hxy⟩
      exact ⟨x, hx, hxy.trans hyz⟩

/-- Source locality persists through any finite number of rows.

If an endpoint is obtained by lifting a source set `Y` and lies above a
member of another source set `X` on the same initial cut, then it is already
obtained by lifting `X`. -/
theorem liftSteps_mem_of_mem_of_source (U : FiniteFatTree H)
    (i steps : Nat) (h : i + steps ≤ U.height)
    {X Y : Set T}
    (hX : X ⊆
      TreeLevel (T := T) (U.cut (⟨i, by omega⟩ : Fin (U.height + 1))))
    (hY : Y ⊆
      TreeLevel (T := T) (U.cut (⟨i, by omega⟩ : Fin (U.height + 1))))
    {z : T}
    (hz : z ∈ U.liftSteps H i steps h Y)
    (hsource : ∃ x ∈ X, x ≤ z) :
    z ∈ U.liftSteps H i steps h X := by
  induction steps generalizing i X Y z with
  | zero =>
      rcases hsource with ⟨x, hx, hxz⟩
      have hxLevel :
          LevelTree.lev x =
            U.cut (⟨i, by omega⟩ : Fin (U.height + 1)) :=
        hX hx
      have hzLevel :
          LevelTree.lev z =
            U.cut (⟨i, by omega⟩ : Fin (U.height + 1)) :=
        hY hz
      have hxeq : x = z :=
        LevelTree.same_level_of_le hxz
          (hxLevel.trans hzLevel.symm)
      simpa [hxeq] using hx
  | succ steps ih =>
      let ri : Fin U.height := ⟨i, by omega⟩
      have hXri :
          X ⊆ TreeLevel (T := T) (U.cut ri.castSucc) := by
        simpa [ri] using hX
      have hYri :
          Y ⊆ TreeLevel (T := T) (U.cut ri.castSucc) := by
        simpa [ri] using hY
      have hXnext :
          U.oneLift H ri X ⊆
            TreeLevel (T := T) (U.cut ri.succ) :=
        U.oneLift_subset_nextLevel H ri hXri
      have hYnext :
          U.oneLift H ri Y ⊆
            TreeLevel (T := T) (U.cut ri.succ) :=
        U.oneLift_subset_nextLevel H ri hYri
      rw [U.liftSteps_succ H i steps h Y] at hz
      rcases U.liftSteps_descends H (i + 1) steps (by omega)
          (X := U.oneLift H ri Y)
          (by simpa [ri] using hYnext) hz with
        ⟨y, hy, hyz⟩
      rcases hsource with ⟨x, hx, hxz⟩
      have hxLevel : LevelTree.lev x = U.cut ri.castSucc :=
        hXri hx
      have hyLevel : LevelTree.lev y = U.cut ri.succ :=
        hYnext hy
      have hxy : x ≤ y := by
        rcases LevelTree.comparable_below hxz hyz with hxy | hyx
        · exact hxy
        · have hlev := LevelTree.level_le_of_le hyx
          have hcut := U.cut_lt_succ H ri
          rw [hyLevel, hxLevel] at hlev
          omega
      have hyFull :
          y ∈ U.oneLift H ri
            (TreeLevel (T := T) (U.cut ri.castSucc)) :=
        U.oneLift_mono H ri hYri hy
      have hyX : y ∈ U.oneLift H ri X :=
        U.oneLift_mem_of_mem_full_of_source H ri hXri
          hyFull ⟨x, hx, hxy⟩
      rw [U.liftSteps_succ H i steps h X]
      exact ih (i := i + 1) (by omega)
        (X := U.oneLift H ri X)
        (Y := U.oneLift H ri Y)
        (by simpa [ri] using hXnext)
        (by simpa [ri] using hYnext)
        hz ⟨y, hyX, hyz⟩

/-- Changing the numerical step count along an equality only transports
the dependent height proof; the resulting lift is unchanged. -/
theorem liftSteps_congr_steps (U : FiniteFatTree H)
    (i s t : Nat)
    (hs : i + s ≤ U.height) (ht : i + t ≤ U.height)
    (hst : s = t) (X : Set T) :
    U.liftSteps H i s hs X = U.liftSteps H i t ht X := by
  subst t
  rfl

/-- Changing the numerical start index along an equality only transports
the dependent height proof; the resulting lift is unchanged. -/
theorem liftSteps_congr_start (U : FiniteFatTree H)
    (i j steps : Nat)
    (hi : i + steps ≤ U.height) (hj : j + steps ≤ U.height)
    (hij : i = j) (X : Set T) :
    U.liftSteps H i steps hi X = U.liftSteps H j steps hj X := by
  subst j
  rfl

/-- Finite lifts compose over adjacent intervals of row indices. -/
theorem liftSteps_add (U : FiniteFatTree H)
    (i a b : Nat) (h : i + (a + b) ≤ U.height)
    (X : Set T) :
    U.liftSteps H i (a + b) h X =
      U.liftSteps H (i + a) b (by omega)
        (U.liftSteps H i a (by omega) X) := by
  induction a generalizing i X with
  | zero =>
      calc
        U.liftSteps H i (0 + b) h X =
            U.liftSteps H i b (by omega) X :=
          U.liftSteps_congr_steps H i (0 + b) b
            h (by omega) (Nat.zero_add b) X
        _ = U.liftSteps H i b (by omega)
              (U.liftSteps H i 0 (by omega) X) := by
          rw [U.liftSteps_zero H i (by omega) X]
  | succ a ih =>
      let ri : Fin U.height := ⟨i, by omega⟩
      have hsum : (a + 1) + b = (a + b) + 1 := by omega
      calc
        U.liftSteps H i ((a + 1) + b) h X =
            U.liftSteps H i ((a + b) + 1) (by omega) X :=
          U.liftSteps_congr_steps H i
            ((a + 1) + b) ((a + b) + 1)
            h (by omega) hsum X
        _ = U.liftSteps H (i + 1) (a + b) (by omega)
              (U.oneLift H ri X) := by
          simpa [ri] using
            U.liftSteps_succ H i (a + b) (by omega) X
        _ = U.liftSteps H ((i + 1) + a) b (by omega)
              (U.liftSteps H (i + 1) a (by omega)
                (U.oneLift H ri X)) :=
          ih (i := i + 1) (by omega)
            (X := U.oneLift H ri X)
        _ = U.liftSteps H (i + (a + 1)) b (by omega)
              (U.liftSteps H i (a + 1) (by omega) X) := by
          have hinner :
              U.liftSteps H (i + 1) a (by omega)
                  (U.oneLift H ri X) =
                U.liftSteps H i (a + 1) (by omega) X := by
            symm
            simpa [ri] using
              U.liftSteps_succ H i a (by omega) X
          rw [hinner]
          exact U.liftSteps_congr_start H
            ((i + 1) + a) (i + (a + 1)) b
            (by omega) (by omega) (by omega)
            (U.liftSteps H i (a + 1) (by omega) X)

/-- Iterated lift is unchanged when all selected rows lie inside a
finite initial segment. -/
theorem initialSegment_liftSteps (U : FiniteFatTree H)
    (n : Nat) (hn : n ≤ U.height)
    (i steps : Nat) (h : i + steps ≤ n) (X : Set T) :
    (U.initialSegment H n hn).liftSteps H i steps h X =
      U.liftSteps H i steps (h.trans hn) X := by
  induction steps generalizing i X with
  | zero =>
      rfl
  | succ steps ih =>
      have hseg :
          i + (steps + 1) ≤ (U.initialSegment H n hn).height := by
        change i + (steps + 1) ≤ n
        exact h
      have hamb : i + (steps + 1) ≤ U.height := h.trans hn
      have hs :=
        (U.initialSegment H n hn).liftSteps_succ H i steps hseg X
      have hu := U.liftSteps_succ H i steps hamb X
      let iseg : Fin n := ⟨i, by omega⟩
      let iu : Fin U.height := ⟨i, by omega⟩
      have hone :
          (U.initialSegment H n hn).oneLift H iseg X =
            U.oneLift H iu X := by
        simpa [iseg, iu] using
          U.initialSegment_oneLift H n hn iseg X
      calc
        (U.initialSegment H n hn).liftSteps H i (steps + 1) h X =
            (U.initialSegment H n hn).liftSteps H (i + 1) steps
              (by omega)
              ((U.initialSegment H n hn).oneLift H iseg X) := by
                exact hs
        _ = (U.initialSegment H n hn).liftSteps H (i + 1) steps
              (by omega) (U.oneLift H iu X) := by
                rw [hone]
        _ = U.liftSteps H (i + 1) steps (by omega)
              (U.oneLift H iu X) := by
                exact ih (i := i + 1) (by omega)
                  (X := U.oneLift H iu X)
        _ = U.liftSteps H i (steps + 1) (h.trans hn) X := by
                exact hu.symm

/-- Lift between two finite cut indices. -/
noncomputable def liftTo (U : FiniteFatTree H)
    (a b : Fin (U.height + 1)) (hab : a ≤ b)
    (X : Set T) : Set T :=
  U.liftSteps H a.1 (b.1 - a.1) (by omega) X

/-- Finite interval lifts commute with taking an initial segment. -/
theorem initialSegment_liftTo (U : FiniteFatTree H)
    (n : Nat) (hn : n ≤ U.height)
    (a b : Fin ((U.initialSegment H n hn).height + 1))
    (hab : a ≤ b) (X : Set T) :
    (U.initialSegment H n hn).liftTo H a b hab X =
      U.liftTo H
        (⟨a.1, by
          have ha : a.1 ≤ n := by
            have ha0 := Nat.le_of_lt_succ a.2
            change a.1 ≤ n at ha0
            exact ha0
          omega⟩ : Fin (U.height + 1))
        (⟨b.1, by
          have hb : b.1 ≤ n := by
            have hb0 := Nat.le_of_lt_succ b.2
            change b.1 ≤ n at hb0
            exact hb0
          omega⟩ : Fin (U.height + 1))
        (by
          change a.1 ≤ b.1
          exact hab)
        X := by
  unfold liftTo
  exact U.initialSegment_liftSteps H n hn a.1 (b.1 - a.1)
    (by
      have hb : b.1 ≤ n := by
        have hb0 := Nat.le_of_lt_succ b.2
        change b.1 ≤ n at hb0
        exact hb0
      omega) X

/-- Endpoint equality transports a finite lift.  This packages the
proof-irrelevance bookkeeping for the dependent interval bound. -/
theorem liftTo_congr (U : FiniteFatTree H)
    {a b a' b' : Fin (U.height + 1)}
    (hab : a ≤ b) (hab' : a' ≤ b')
    (ha : a = a') (hb : b = b')
    (X : Set T) :
    U.liftTo H a b hab X = U.liftTo H a' b' hab' X := by
  subst a'
  subst b'
  rfl

@[simp] theorem liftTo_same (U : FiniteFatTree H)
    (a : Fin (U.height + 1)) (X : Set T) :
    U.liftTo H a a le_rfl X = X := by
  unfold liftTo
  calc
    U.liftSteps H a.1 (a.1 - a.1) (by omega) X =
        U.liftSteps H a.1 0 (by omega) X :=
      U.liftSteps_congr_steps H a.1 (a.1 - a.1) 0
        (by omega) (by omega) (Nat.sub_self a.1) X
    _ = X := U.liftSteps_zero H a.1 (by omega) X

/-- Crossing adjacent finite cut indices is exactly one row lift. -/
theorem liftTo_succ (U : FiniteFatTree H)
    (i : Fin U.height) (X : Set T) :
    U.liftTo H i.castSucc i.succ
        (by
          change i.1 ≤ i.1 + 1
          omega) X =
      U.oneLift H i X := by
  unfold liftTo
  have hdiff : i.succ.1 - i.castSucc.1 = 1 := by
    change i.1 + 1 - i.1 = 1
    omega
  calc
    U.liftSteps H i.1 (i.succ.1 - i.castSucc.1) (by omega) X =
        U.liftSteps H i.1 1 (by omega) X :=
      U.liftSteps_congr_steps H i.1
        (i.succ.1 - i.castSucc.1) 1
        (by omega) (by omega) hdiff X
    _ = U.oneLift H i X := by
      change
        U.oneLift H
          (⟨i.1, by omega⟩ : Fin U.height) X =
          U.oneLift H i X
      congr

/-- A finite lift through an intermediate cut factors as the two
successive lifts through that cut. -/
theorem liftTo_split (U : FiniteFatTree H)
    (a b c : Fin (U.height + 1))
    (hab : a ≤ b) (hbc : b ≤ c) (X : Set T) :
    U.liftTo H a c (hab.trans hbc) X =
      U.liftTo H b c hbc (U.liftTo H a b hab X) := by
  unfold liftTo
  have hsum :
      c.1 - a.1 = (b.1 - a.1) + (c.1 - b.1) := by
    omega
  have hmid : a.1 + (b.1 - a.1) = b.1 := by
    omega
  calc
    U.liftSteps H a.1 (c.1 - a.1) (by omega) X =
        U.liftSteps H a.1
          ((b.1 - a.1) + (c.1 - b.1)) (by omega) X :=
      U.liftSteps_congr_steps H a.1
        (c.1 - a.1) ((b.1 - a.1) + (c.1 - b.1))
        (by omega) (by omega) hsum X
    _ = U.liftSteps H (a.1 + (b.1 - a.1))
          (c.1 - b.1) (by omega)
          (U.liftSteps H a.1 (b.1 - a.1) (by omega) X) :=
      U.liftSteps_add H a.1 (b.1 - a.1) (c.1 - b.1)
        (by omega) X
    _ = U.liftSteps H b.1 (c.1 - b.1) (by omega)
          (U.liftSteps H a.1 (b.1 - a.1) (by omega) X) :=
      U.liftSteps_congr_start H
        (a.1 + (b.1 - a.1)) b.1 (c.1 - b.1)
        (by omega) (by omega) hmid
        (U.liftSteps H a.1 (b.1 - a.1) (by omega) X)

/-- Finite `liftTo` is monotone in its starting set. -/
theorem liftTo_mono (U : FiniteFatTree H)
    (a b : Fin (U.height + 1)) (hab : a ≤ b)
    {X Y : Set T} (hXY : X ⊆ Y) :
    U.liftTo H a b hab X ⊆ U.liftTo H a b hab Y := by
  unfold liftTo
  exact U.liftSteps_mono H a.1 (b.1 - a.1) (by omega) hXY

/-- A finite lift lands on its terminal selected cut. -/
theorem liftTo_subset_level (U : FiniteFatTree H)
    (a b : Fin (U.height + 1)) (hab : a ≤ b)
    {X : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut a)) :
    U.liftTo H a b hab X ⊆ TreeLevel (T := T) (U.cut b) := by
  unfold liftTo
  have hstart :
      X ⊆ TreeLevel (T := T)
        (U.cut (⟨a.1, by omega⟩ : Fin (U.height + 1))) := by
    simpa using hX
  have hres :=
    U.liftSteps_subset_level H a.1 (b.1 - a.1)
      (by omega) hstart
  have habNat : a.1 ≤ b.1 := hab
  have hidx : a.1 + (b.1 - a.1) = b.1 :=
    Nat.add_sub_of_le habNat
  have hendBound : a.1 + (b.1 - a.1) < U.height + 1 := by
    rw [hidx]
    exact b.2
  have hend :
      (⟨a.1 + (b.1 - a.1), hendBound⟩ :
        Fin (U.height + 1)) = b := by
    apply Fin.ext
    exact hidx
  simpa [hend] using hres

/-- Every endpoint of a finite `liftTo` lies above a node in the source set. -/
theorem liftTo_descends (U : FiniteFatTree H)
    (a b : Fin (U.height + 1)) (hab : a ≤ b)
    {X : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut a))
    {z : T} (hz : z ∈ U.liftTo H a b hab X) :
    ∃ x ∈ X, x ≤ z := by
  unfold liftTo at hz
  have hstart :
      X ⊆ TreeLevel (T := T)
        (U.cut (⟨a.1, by omega⟩ : Fin (U.height + 1))) := by
    simpa using hX
  exact U.liftSteps_descends H a.1 (b.1 - a.1)
    (by omega) hstart hz

/-- Source locality in finite `liftTo` notation. -/
theorem liftTo_mem_of_mem_of_source (U : FiniteFatTree H)
    (a b : Fin (U.height + 1)) (hab : a ≤ b)
    {X Y : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut a))
    (hY : Y ⊆ TreeLevel (T := T) (U.cut a))
    {z : T}
    (hz : z ∈ U.liftTo H a b hab Y)
    (hsource : ∃ x ∈ X, x ≤ z) :
    z ∈ U.liftTo H a b hab X := by
  unfold liftTo at hz ⊢
  have hX0 :
      X ⊆ TreeLevel (T := T)
        (U.cut (⟨a.1, by omega⟩ : Fin (U.height + 1))) := by
    simpa using hX
  have hY0 :
      Y ⊆ TreeLevel (T := T)
        (U.cut (⟨a.1, by omega⟩ : Fin (U.height + 1))) := by
    simpa using hY
  exact U.liftSteps_mem_of_mem_of_source H
    a.1 (b.1 - a.1) (by omega)
    hX0 hY0 hz hsource

end FiniteFatTree

namespace FatTree

variable (H : SMTree S)

/-- Canonical row extension agrees whether an infinite fat tree is viewed
directly or through a finite initial segment containing the row. -/
theorem initialSegment_rowExtension (U : FatTree H)
    (n : Nat) (i : Fin (U.initialSegment H n).height) :
    (U.initialSegment H n).rowExtension H i =
      U.rowExtension H i.1 := by
  rfl

/-- One-step Lift agrees with the ambient infinite fat tree on an initial
segment. -/
theorem initialSegment_oneLift (U : FatTree H)
    (n : Nat) (i : Fin (U.initialSegment H n).height) (X : Set T) :
    (U.initialSegment H n).oneLift H i X =
      U.oneLift H i.1 X := by
  unfold FiniteFatTree.oneLift FatTree.oneLift
  rw [U.initialSegment_rowExtension H n i]

/-- Multi-row Lift inside an initial segment is the same operation as in the
ambient infinite fat tree. -/
theorem initialSegment_liftSteps (U : FatTree H)
    (n i steps : Nat) (h : i + steps ≤ n) (X : Set T) :
    (U.initialSegment H n).liftSteps H i steps h X =
      U.liftSteps H i steps X := by
  induction steps generalizing i X with
  | zero =>
      rfl
  | succ steps ih =>
      have hseg :
          i + (steps + 1) ≤ (U.initialSegment H n).height := by
        change i + (steps + 1) ≤ n
        exact h
      have hs :=
        (U.initialSegment H n).liftSteps_succ H i steps hseg X
      have hu := U.liftSteps_succ H i steps X
      let iseg : Fin n := ⟨i, by omega⟩
      have hone :
          (U.initialSegment H n).oneLift H iseg X =
            U.oneLift H i X := by
        simpa [iseg] using
          U.initialSegment_oneLift H n iseg X
      calc
        (U.initialSegment H n).liftSteps H i (steps + 1) h X =
            (U.initialSegment H n).liftSteps H (i + 1) steps
              (by omega)
              ((U.initialSegment H n).oneLift H iseg X) := by
                exact hs
        _ = (U.initialSegment H n).liftSteps H (i + 1) steps
              (by omega) (U.oneLift H i X) := by
                rw [hone]
        _ = U.liftSteps H (i + 1) steps (U.oneLift H i X) := by
                exact ih (i := i + 1) (by omega)
                  (X := U.oneLift H i X)
        _ = U.liftSteps H i (steps + 1) X := hu.symm

/-- Interval Lift on a finite initial segment agrees with interval Lift in
the ambient infinite fat tree. -/
theorem initialSegment_liftTo (U : FatTree H)
    (n : Nat)
    (a b : Fin ((U.initialSegment H n).height + 1))
    (hab : a ≤ b) (X : Set T) :
    (U.initialSegment H n).liftTo H a b hab X =
      U.liftTo H a.1 b.1 (by
        change a.1 ≤ b.1
        exact hab) X := by
  unfold FiniteFatTree.liftTo FatTree.liftTo
  exact U.initialSegment_liftSteps H n a.1 (b.1 - a.1)
    (by
      have hb : b.1 ≤ n := by
        have hb0 := Nat.le_of_lt_succ b.2
        change b.1 ≤ n at hb0
        exact hb0
      omega) X

end FatTree

end SMTree
end SuccessorTree

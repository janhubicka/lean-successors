import SuccessorTree.Approximation
import RamseySpace.Basic

/-!
# Successor trees as an abstract Ramsey approximation system

This is the first bridge from the successor-tree formalization to
Todorčević's abstract Ramsey-space framework.

A point is an M-map. A refinement of G is a right-composition G ∘ K.
The zeroth approximation is empty, and approximation n+1 is the restriction
of the M-map to tree levels at most n.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Two M-maps are equal when they agree pointwise. -/
theorem MMap.ext_apply (H : SMTree S) {F G : MMap H}
    (h : ∀ a : T, F a = G a) : F = G := by
  cases F with
  | mk F hF =>
      cases G with
      | mk G hG =>
          have hFG : F = G := by
            apply ShapeMap.ext
            funext a
            exact h a
          cases hFG
          rfl

/-- Ramsey reduction: F is a refinement of G when F = G ∘ K extensionally
for some M-map K. -/
def RamseyReduction (H : SMTree S) (F G : MMap H) : Prop :=
  ∃ K : MMap H, ∀ a : T, F a = G (K a)

theorem ramseyReduction_refl (H : SMTree S) (F : MMap H) :
    RamseyReduction H F F := by
  refine ⟨MMap.id H, ?_⟩
  intro a
  rfl

theorem ramseyReduction_trans (H : SMTree S) {F G K : MMap H}
    (hFG : RamseyReduction H F G)
    (hGK : RamseyReduction H G K) :
    RamseyReduction H F K := by
  rcases hFG with ⟨U, hU⟩
  rcases hGK with ⟨V, hV⟩
  refine ⟨MMap.comp H V U, ?_⟩
  intro a
  calc
    F a = G (U a) := hU a
    _ = K (V (U a)) := hV (U a)
    _ = K ((MMap.comp H V U) a) := rfl

/-- Realized finite approximations.

Level zero is the unique empty approximation. At level n+1 we remember the
restriction of a total M-map to nodes on levels at most n. -/
def RamseyApprox (H : SMTree S) : Nat → Type u
  | 0 => PUnit
  | n + 1 =>
      {r : RestrictedMap T n // ∃ F : MMap H, F.restrictLe H n = r}

/-- The canonical finite approximation of an M-map. -/
def ramseyApprox (H : SMTree S) :
    (n : Nat) → MMap H → RamseyApprox H n
  | 0, _ => PUnit.unit
  | n + 1, F => ⟨F.restrictLe H n, ⟨F, rfl⟩⟩

/-- A.1 data for successor-tree M-maps. -/
def ramseyApproximationSystem (H : SMTree S) :
    RamseySpace.ApproximationSystem where
  Point := MMap H
  Approx := RamseyApprox H
  le := RamseyReduction H
  le_refl := ramseyReduction_refl H
  le_trans := by
    intro F G K hFG hGK
    exact ramseyReduction_trans H hFG hGK
  approx := ramseyApprox H
  approx_surjective := by
    intro n q
    cases n with
    | zero =>
        exact ⟨MMap.id H, Subsingleton.elim _ _⟩
    | succ n =>
        rcases q.2 with ⟨F, hF⟩
        refine ⟨F, ?_⟩
        apply Subtype.ext
        exact hF
  empty := PUnit.unit
  approx_zero := by
    intro F
    rfl
  separated := by
    intro F G h
    apply MMap.ext_apply H
    intro a
    let n := LevelTree.lev a
    have heq := h (n + 1)
    have hval := congrArg Subtype.val heq
    change F.restrictLe H n = G.restrictLe H n at hval
    exact congrFun hval ⟨a, le_rfl⟩
  coherent := by
    intro F G n h m hm
    cases n with
    | zero =>
        omega
    | succ n =>
        cases m with
        | zero =>
            rfl
        | succ m =>
            apply Subtype.ext
            change F.restrictLe H m = G.restrictLe H m
            funext a
            have hval := congrArg Subtype.val h
            change F.restrictLe H n = G.restrictLe H n at hval
            have hmn : m ≤ n := by omega
            exact congrFun hval ⟨a.1, a.2.trans hmn⟩

end SMTree
end SuccessorTree

import SuccessorTree.Successor
import Mathlib.Tactic

/-!
# Shape-preserving maps

Definition 1.3 and the first basic consequences from Proposition 2.1.
Order preservation is proved from the paper's axioms rather than added as an
extra field.
-/

namespace SuccessorTree

variable {Node : Type u} {Char : Type v} [PartialOrder Node]

structure ShapeMap (S : STree Node Char) where
  toFun : Node → Node
  injective : Function.Injective toFun
  levelMap : Nat → Nat
  level_apply :
    ∀ a : Node, S.tree.level (toFun a) = levelMap (S.tree.level a)

  -- Definition 1.3(ii)
  weak_succ :
    ∀ {a b : Node} {ps : List Node} {c : Char},
      S.succ a ps c = some b →
        ∃ y : Node,
          S.succ (toFun a) (ps.map toFun) c = some y ∧
            y ≤ toFun b

  -- Definition 1.3(iii)
  root_cone :
    ∀ {r b : Node},
      S.tree.IsRoot r → r ≤ b → r ≤ toFun b

namespace ShapeMap

instance (S : STree Node Char) :
    CoeFun (ShapeMap S) (fun _ => Node → Node) :=
  ⟨ShapeMap.toFun⟩

@[simp] theorem level_apply' (F : ShapeMap S) (a : Node) :
    S.tree.level (F a) = F.levelMap (S.tree.level a) :=
  F.level_apply a

/-- Proposition 2.1(i) for one immediate edge. -/
theorem map_lt_of_immediate
    (F : ShapeMap S) {a b : Node}
    (hab : S.tree.IsImmediateSuccessor a b) :
    F a < F b := by
  obtain ⟨ps, c, hsucc⟩ := S.succ_constructive hab
  obtain ⟨y, hy, hyb⟩ := F.weak_succ hsucc
  exact lt_of_lt_of_le (S.succ_base_lt hy) hyb

/-- Proposition 2.1(i): shape-preserving maps preserve strict tree order. -/
theorem map_lt
    (F : ShapeMap S) {a b : Node} (hab : a < b) :
    F a < F b := by
  generalize hn : S.tree.level b = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
      have hlab : S.tree.level a < S.tree.level b :=
        S.tree.level_strict hab
      by_cases himm :
          S.tree.level b = S.tree.level a + 1
      · exact F.map_lt_of_immediate ⟨hab, himm⟩
      · have hbpos : 0 < S.tree.level b := by omega
        obtain ⟨c, hc⟩ :=
          S.tree.exists_immediate_predecessor b hbpos
        have hlac : S.tree.level a ≤ S.tree.level c := by
          omega
        have hacle : a ≤ c :=
          S.tree.predecessor_le hab hc.1 hlac
        have hac : a < c := by
          rcases hacle.eq_or_lt with hEq | hlt
          · subst c
            exact False.elim (himm hc.2)
          · exact hlt
        have hclevel : S.tree.level c < n := by
          rw [← hn]
          exact S.tree.level_strict hc.1
        have hFac : F a < F c :=
          ih (S.tree.level c) hclevel a c rfl hac
        have hFcb : F c < F b :=
          F.map_lt_of_immediate hc
        exact lt_trans hFac hFcb

theorem monotone (F : ShapeMap S) : Monotone F := by
  intro a b hab
  rcases hab.eq_or_lt with hEq | hlt
  · subst b
    exact le_rfl
  · exact (F.map_lt hlt).le

def id (S : STree Node Char) : ShapeMap S where
  toFun := fun a => a
  injective := Function.injective_id
  levelMap := fun n => n
  level_apply := by
    intro a
    rfl
  weak_succ := by
    intro a b ps c h
    refine ⟨b, ?_, le_rfl⟩
    simpa using h
  root_cone := by
    intro r b hr hrb
    simpa using hrb

def comp (F G : ShapeMap S) : ShapeMap S where
  toFun := F ∘ G
  injective := F.injective.comp G.injective
  levelMap := F.levelMap ∘ G.levelMap
  level_apply := by
    intro a
    simp only [Function.comp_apply]
    rw [F.level_apply, G.level_apply]
  weak_succ := by
    intro a b ps c h
    obtain ⟨y, hy, hyb⟩ := G.weak_succ h
    obtain ⟨z, hz, hzy⟩ := F.weak_succ hy
    refine ⟨z, ?_, le_trans hzy (F.monotone hyb)⟩
    simpa [Function.comp_def, List.map_map] using hz
  root_cone := by
    intro r b hr hrb
    exact F.root_cone hr (G.root_cone hr hrb)

@[simp] theorem id_apply (S : STree Node Char) (a : Node) :
    ShapeMap.id S a = a := rfl

@[simp] theorem comp_apply (F G : ShapeMap S) (a : Node) :
    F.comp G a = F (G a) := rfl

def SkipsLevel (F : ShapeMap S) (m : Nat) : Prop :=
  ∀ n : Nat, F.levelMap n ≠ m

def SkipsOnlyLevel (F : ShapeMap S) (m : Nat) : Prop :=
  F.SkipsLevel m ∧
    ∀ k : Nat, k ≠ m → ∃ n : Nat, F.levelMap n = k

end ShapeMap

end SuccessorTree

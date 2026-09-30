import SuccessorTree.Successor
import Mathlib.Tactic

/-!
# Shape-preserving maps

Formalization of Definition `def:shape-pres` and the basic pre-pigeonhole
properties used in the successor-tree paper.
-/

namespace SuccessorTree

structure ShapeMap {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T] (S : STree T Label) where
  toFun : T → T
  injective' : Function.Injective toFun
  level_preserving' : ∀ {a b : T}, LevelTree.lev a = LevelTree.lev b →
    LevelTree.lev (toFun a) = LevelTree.lev (toFun b)
  weak_succ' : ∀ {a b : T} {p : List T} {c : Label},
    S.succ a p c = some b →
      ∃ d : T,
        S.succ (toFun a) (p.map toFun) c = some d ∧ d ≤ toFun b
  root_le' : ∀ {a : T}, LevelTree.lev a = 0 → a ≤ toFun a

namespace ShapeMap

variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

instance : CoeFun (ShapeMap S) (fun _ => T → T) := ⟨ShapeMap.toFun⟩

theorem injective (F : ShapeMap S) : Function.Injective F := F.injective'

theorem level_eq_of_level_eq (F : ShapeMap S) {a b : T}
    (h : LevelTree.lev a = LevelTree.lev b) :
    LevelTree.lev (F a) = LevelTree.lev (F b) :=
  F.level_preserving' h

/-- Weak successor preservation already implies strict order preservation on
one tree edge. -/
theorem map_lt_of_covBy (F : ShapeMap S) {a b : T} (hab : a ⋖ b) :
    F a < F b := by
  obtain ⟨p, c, hsucc⟩ := S.s3 hab
  obtain ⟨d, hFd, hdb⟩ := F.weak_succ' hsucc
  have hcover : F a ⋖ d := S.covBy_of_succ_eq_some hFd
  exact lt_of_lt_of_le hcover.lt hdb

/-- Shape-preserving maps preserve strict tree order. -/
theorem map_lt_of_lt (F : ShapeMap S) {a b : T} (hab : a < b) :
    F a < F b := by
  induction hdiff : LevelTree.lev b - LevelTree.lev a using Nat.strong_induction_on generalizing a b with
  | h d ih =>
      obtain ⟨c, hac, hcb⟩ := LevelTree.exists_covBy_between hab
      by_cases hbc : c = b
      · subst b
        exact F.map_lt_of_covBy hac
      · have hcb' : c < b := lt_of_le_of_ne hcb hbc
        have hfirst : F a < F c := F.map_lt_of_covBy hac
        have hlevels : LevelTree.lev c = LevelTree.lev a + 1 :=
          LevelTree.covBy_level_eq hac
        have habLevels : LevelTree.lev a < LevelTree.lev b :=
          LevelTree.lt_level_lt hab
        have hsmaller : LevelTree.lev b - LevelTree.lev c < d := by
          rw [← hdiff]
          omega
        have htail : F c < F b :=
          ih (LevelTree.lev b - LevelTree.lev c) hsmaller hcb' rfl
        exact hfirst.trans htail

theorem map_le_of_le (F : ShapeMap S) {a b : T} (hab : a ≤ b) :
    F a ≤ F b := by
  rcases hab.eq_or_lt with h | h
  · simpa [h]
  · exact (F.map_lt_of_lt h).le

/-- Relative order of levels is preserved, even for incomparable nodes. -/
theorem level_lt_of_level_lt (F : ShapeMap S) {a b : T}
    (hab : LevelTree.lev a < LevelTree.lev b) :
    LevelTree.lev (F a) < LevelTree.lev (F b) := by
  have hle : LevelTree.lev a ≤ LevelTree.lev b := Nat.le_of_lt hab
  let c := LevelTree.ancestor b (LevelTree.lev a) hle
  have hcb : c ≤ b := LevelTree.ancestor_le b (LevelTree.lev a) hle
  have hcLevel : LevelTree.lev c = LevelTree.lev a := by
    simp [c, LevelTree.level_ancestor]
  have hcbne : c ≠ b := by
    intro h
    have hlevels := congrArg LevelTree.lev h
    omega
  have hcb' : c < b := lt_of_le_of_ne hcb hcbne
  have hmap := F.map_lt_of_lt hcb'
  have hFaFc : LevelTree.lev (F a) = LevelTree.lev (F c) :=
    F.level_eq_of_level_eq hcLevel.symm
  have hlev := LevelTree.lt_level_lt hmap
  omega

/-- The level map induced by a shape-preserving map. -/
noncomputable def levelMap (F : ShapeMap S) (n : Nat) : Nat :=
  let a := Classical.choose (LevelTree.level_nonempty (T := T) n)
  LevelTree.lev (F a)

theorem levelMap_eq (F : ShapeMap S) {a : T} :
    F.levelMap (LevelTree.lev a) = LevelTree.lev (F a) := by
  unfold levelMap
  let x := Classical.choose (LevelTree.level_nonempty (T := T) (LevelTree.lev a))
  have hx : LevelTree.lev x = LevelTree.lev a :=
    Classical.choose_spec (LevelTree.level_nonempty (T := T) (LevelTree.lev a))
  exact F.level_eq_of_level_eq hx

/-- The identity map is shape-preserving. -/
def id (S : STree T Label) : ShapeMap S where
  toFun := fun a => a
  injective' := Function.injective_id
  level_preserving' := by intro a b h; exact h
  weak_succ' := by
    intro a b p c h
    refine ⟨b, ?_, le_rfl⟩
    simpa using h
  root_le' := by intro a ha; exact le_rfl

@[simp] theorem id_apply (a : T) : (id S) a = a := rfl

/-- Composition of shape-preserving maps. The proof uses order preservation
for the outer map; this is the dependency hidden by the paper's phrase
“follows directly from the definition”. -/
def comp (F G : ShapeMap S) : ShapeMap S where
  toFun := fun a => F (G a)
  injective' := F.injective.comp G.injective
  level_preserving' := by
    intro a b hab
    exact F.level_eq_of_level_eq (G.level_eq_of_level_eq hab)
  weak_succ' := by
    intro a b p c hab
    obtain ⟨d, hGd, hdb⟩ := G.weak_succ' hab
    obtain ⟨e, hFe, hed⟩ := F.weak_succ' hGd
    refine ⟨e, ?_, hed.trans (F.map_le_of_le hdb)⟩
    simpa [List.map_map, Function.comp_def] using hFe
  root_le' := by
    intro a ha
    have haG : a ≤ G a := G.root_le' ha
    have haF : a ≤ F a := F.root_le' ha
    exact haF.trans (F.map_le_of_le haG)

@[simp] theorem comp_apply (F G : ShapeMap S) (a : T) :
    (F.comp G) a = F (G a) := rfl

end ShapeMap

end SuccessorTree

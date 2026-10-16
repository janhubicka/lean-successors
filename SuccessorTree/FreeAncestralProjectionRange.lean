import SuccessorTree.FreeAncestralSMTree
import SuccessorTree.RamseySpace.Basic
import Mathlib.Tactic

/-!
# A genuine ancestral-parameter obstruction to right factorization

The smallest useful example has arity one and one successor
label. Let E₀ insert an empty code at level zero and E₂
insert a code with the ancestral parameter [0] at level two.

E₀ never produces a positive-level transition with parameter
0: every existing parameter level is shifted by one and the
inserted root code is empty. But E₂(E₀(a)) has last parameter
[0] for the specified source node a of level one.

This is a Lean-only algebraic obstruction; it does **not** yet
construct the full infinite fat-tree reduction in Section 4.
No axioms or sorry are permitted.
-/

namespace SuccessorTree.FreeAncestral

universe u

variable {Label : Type u} {arity : Nat} [Fintype Label]

/-- Inserting a gap at 0 shifts every parameter of a positive-level
last transition up by one. Thus the last parameter list
of the resulting image does not contain level 0. -/
theorem zeroGap_last_parameter_ne_zero
    (choose : History Label arity 0 → Code Label arity 0)
    (a : Node Label arity) (ha : 0 < a.level) :
    0 ∉ lastParamLevelsNode (gapNode 0 choose a) := by
  rcases a with ⟨n, h⟩
  cases n with
  | zero =>
      change 0 < 0 at ha
      omega
  | succ n =>
      cases h with
      | step p c =>
          rcases c with ⟨lab, tuple⟩
          change (0 : Nat) ∉ lastParamLevelsNode
            (gapNode 0 choose (child (⟨n, p⟩ : Node Label arity) tuple lab))
          rw [gapNode_child_of_ge 0 choose
            (⟨n, p⟩ : Node Label arity) tuple lab (Nat.zero_le n)]
          rw [lastParamLevelsNode_child]
          change (0 : Nat) ∉ levelList
            (gapShiftParamTuple 0 choose (⟨n, p⟩ : Node Label arity)
              tuple (Nat.zero_le n))
          rw [levelList_gapShiftParamTuple]
          intro hm
          obtain ⟨j, hj, hzero⟩ := List.mem_map.mp hm
          have hs : shiftNat 0 j = j + 1 := by simp [shiftNat]
          omega

/-- The empty root insertion code (arity one, singleton label). -/
def projectionEmptyCode : Code Unit 1 0 :=
  ⟨(), {len := ⟨0, by decide⟩, value := Fin.elim0}⟩

/-- The adversarial code at level 2, referring to ancestor 0. -/
def projectionRefZeroCode : Code Unit 1 2 :=
  ⟨(), {len := ⟨1, by decide⟩,
        value := fun _ => ⟨0, by decide⟩}⟩

noncomputable def projectionRootGap :
    ShapeMap (freeSTree (Label := Unit) (arity := 1)) :=
  oneGapShapeMap 0 (fun _ => projectionEmptyCode)

noncomputable def projectionParamGap :
    ShapeMap (freeSTree (Label := Unit) (arity := 1)) :=
  oneGapShapeMap 2 (fun _ => projectionRefZeroCode)

/-- Level-one history with an empty parameter tuple. -/
def projectionSource : Node Unit 1 :=
  ⟨1, History.step History.root projectionEmptyCode⟩

/-- The root gap inserts no ancestral zero parameter in **any**
image, including the source root. -/
theorem projectionRootGap_avoids_zero (a : Node Unit 1) :
    0 ∉ lastParamLevelsNode (projectionRootGap a) := by
  rcases a with ⟨n, h⟩
  cases n with
  | zero =>
      have hr : h = History.root := history_zero_unique h
      subst h
      change (0 : Nat) ∉ lastParamLevelsNode
        (gapNode 0 (fun _ => projectionEmptyCode)
          (⟨0, History.root⟩ : Node Unit 1))
      rw [gapNode_at_level, lastParamLevelsNode_child]
      decide
  | succ n =>
      change (0 : Nat) ∉ lastParamLevelsNode
        (gapNode 0 (fun _ => projectionEmptyCode)
          (⟨n + 1, h⟩ : Node Unit 1))
      have hpositive : 0 < (⟨n + 1, h⟩ : Node Unit 1).level := by
        change 0 < n + 1
        omega
      exact zeroGap_last_parameter_ne_zero
        (fun _ => projectionEmptyCode)
        ⟨n + 1, h⟩ hpositive

/-- The two-gap composite creates a parameter at forbidden
ancestral level zero. -/
theorem projectionParamGap_creates_zero :
    0 ∈ lastParamLevelsNode
      (projectionParamGap (projectionRootGap projectionSource)) := by
  have hlev : (projectionRootGap projectionSource).level = 2 := by
    change
      (gapNode 0 (fun _ => projectionEmptyCode)
        projectionSource).level = 2
    rw [gapNode_level]
    decide
  rcases heq : projectionRootGap projectionSource with ⟨n, h⟩
  change n = 2 at hlev
  subst n
  change (0 : Nat) ∈ lastParamLevelsNode
    (gapNode 2 (fun _ => projectionRefZeroCode)
      (⟨2, h⟩ : Node Unit 1))
  rw [gapNode_at_level, lastParamLevelsNode_child]
  decide

/-- This is stronger than failure of a shape-preserving
right factor: no arbitrary function G satisfies E₂∘E₀=E₀∘G. -/
theorem projectionComposite_no_function_factor
    (G : Node Unit 1 → Node Unit 1) :
    ¬ ∀ a : Node Unit 1,
      projectionParamGap (projectionRootGap a) =
        projectionRootGap (G a) := by
  intro hG
  have hImage := projectionParamGap_creates_zero
  rw [hG projectionSource] at hImage
  exact projectionRootGap_avoids_zero (G projectionSource) hImage

/-- The concrete verified free ancestral (S,M)-tree with
one possible ancestral parameter and one label. -/
noncomputable def projectionFreeSMTree :
    SMTree (freeSTree (Label := Unit) (arity := 1)) :=
  freeSMTree (Label := Unit) (arity := 1)

noncomputable def projectionRootGapM :
    SMTree.MMap projectionFreeSMTree :=
  ⟨projectionRootGap, by simp [projectionFreeSMTree, freeSMTree]⟩

noncomputable def projectionParamGapM :
    SMTree.MMap projectionFreeSMTree :=
  ⟨projectionParamGap, by simp [projectionFreeSMTree, freeSMTree]⟩

/-- The concrete projected map E₂∘E₀ is outside the
right-composition cone of E₀, even though both are
members of the verified free-ancestral monoid. -/
theorem projectionComposite_not_rightFactor :
    ¬ SMTree.RamseyReduction projectionFreeSMTree
      (SMTree.MMap.comp projectionFreeSMTree
        projectionParamGapM projectionRootGapM)
      projectionRootGapM := by
  rintro ⟨G, hG⟩
  apply projectionComposite_no_function_factor (fun a => G a)
  intro a
  exact hG a

end SuccessorTree.FreeAncestral

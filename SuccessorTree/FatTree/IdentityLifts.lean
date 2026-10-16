import SuccessorTree.FatTree.ApproximationSystem
import SuccessorTree.FatTree.Lift
import Mathlib.Tactic

/-!
# Full-level lifting through the identity fat-tree tail

This small general-purpose module is useful for reasoning about
the geometric fat reduction order. A genuinely identity row
lifts the *entire* current level to the entire next level,
including every admissible successor parameter choice.

The source `FatTree.identityFatTree` already exists as the
completion tail in the A1 proof. We prove that its canonical
row extensions are literally the identity in the original
SMTree monoid; this is stronger than merely agreeing on
finite prefixes. The full-level geometric lift identity
then follows by induction.

These facts require no additional axioms, are independent of
V10, and will be reused to construct arbitrarily delayed
free-ancestral insertion counterexamples to Section 4
projection compatibility.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

/-- The canonical total extension of a finite identity
one-level word is exactly the identity M-map. -/
theorem identityWord_rowExtension_id
    (H : SMTree S) (n : Nat) :
    H.canonicalExtension ((AM.id1 H n).representative H) n =
      MMap.id H := by
  have hagree :
      ∀ a : T, LevelTree.lev a ≤ n →
        (MMap.id H) a = (AM.id1 H n).representative H a := by
    intro a ha
    have htop := AM.representative_top H (AM.id1 H n)
    have hv := congrArg Subtype.val htop
    change
      ((AM.id1 H n).representative H).restrictLe H n =
        (MMap.id H).restrictLe H n at hv
    exact (congrFun hv ⟨a, ha⟩).symm
  have hfull :
      ∀ ell : Nat,
        H.levelMap ((AM.id1 H n).representative H).map n ≤ ell →
        ell ∈ (MMap.id H).map.levelRange := by
    intro ell _
    rcases H.level_nonempty ell with ⟨a, ha⟩
    change ∃ b : T, LevelTree.lev ((MMap.id H) b) = ell
    exact ⟨a, by simpa [MMap.id, ShapeMap.id] using ha⟩
  exact (H.canonicalExtension_unique
    ((AM.id1 H n).representative H) (MMap.id H) n
    hagree hfull).symm

/-- Every row of the canonical identity fat tree has
the identity as its canonical total extension. -/
theorem identityFatTree_rowExtension_id
    (H : SMTree S) (i : Nat) :
    (identityFatTree H).rowExtension H i = MMap.id H := by
  change H.canonicalExtension ((AM.id1 H i).representative H) i =
    MMap.id H
  exact identityWord_rowExtension_id H i

/-- The immediate successors of an entire level of a
levelled tree comprise the entire next level. -/
theorem immediateSuccessors_full_level (n : Nat) :
    ImmediateSuccessors (T := T) (TreeLevel (T := T) n) =
      TreeLevel (T := T) (n + 1) := by
  ext b
  constructor
  · rintro ⟨a, ha, hab⟩
    have hstep := LevelTree.covBy_level_eq hab
    change LevelTree.lev b = n + 1
    change LevelTree.lev a = n at ha
    omega
  · intro hb
    have hlevel : LevelTree.lev b = n + 1 := hb
    have hn : n ≤ LevelTree.lev b := by omega
    let a : T := LevelTree.ancestor b n hn
    refine ⟨a, ?_, ?_⟩
    · exact LevelTree.level_ancestor b n hn
    · apply LevelTree.covBy_of_le_level_succ
        (LevelTree.ancestor_le b n hn)
      rw [LevelTree.level_ancestor]
      omega

/-- One identity fat-tree row lifts a whole source level
to the whole next level, including parameter choices
that a particular shape-map image may omit. -/
theorem identityFatTree_oneLift_full
    (H : SMTree S) (i : Nat) :
    (identityFatTree H).oneLift H i
      (TreeLevel (T := T) i) =
      TreeLevel (T := T) (i + 1) := by
  change ((identityFatTree H).rowExtension H i) ''
      ImmediateSuccessors (T := T) (TreeLevel (T := T) i) =
    TreeLevel (T := T) (i + 1)
  rw [identityFatTree_rowExtension_id H i]
  simpa [MMap.id, ShapeMap.id] using
    (immediateSuccessors_full_level (T := T) i)

/-- Every finite block of identity fat-tree rows spans
the entire target level. -/
theorem identityFatTree_liftSteps_full
    (H : SMTree S) (i steps : Nat) :
    (identityFatTree H).liftSteps H i steps
      (TreeLevel (T := T) i) =
    TreeLevel (T := T) (i + steps) := by
  induction steps generalizing i with
  | zero =>
      rfl
  | succ k ih =>
      rw [FatTree.liftSteps_succ]
      rw [identityFatTree_oneLift_full H i]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ih (i := i + 1))

/-- Full-level identity-tail version in the exact
`liftTo` language of the fat-tree reduction witness. -/
theorem identityFatTree_liftTo_full
    (H : SMTree S) (i k : Nat) (hik : i ≤ k) :
    (identityFatTree H).liftTo H i k hik
      (TreeLevel (T := T) i) =
    TreeLevel (T := T) k := by
  change (identityFatTree H).liftSteps H i (k - i)
    (TreeLevel (T := T) i) = TreeLevel (T := T) k
  rw [identityFatTree_liftSteps_full H]
  have heq : i + (k - i) = k := by omega
  rw [heq]

end SuccessorTree.SMTree.FatTree

import SuccessorTree.V10.M3LiteralDuplication
import Mathlib.Tactic

/-!
# Genuine source successors at every positive Kpt level

The uniform level-removal proof (M2) needs to inspect the image of a
genuine successor at the first source level n across the gap.
An arbitrary finite witness of the boundary Kpt type is not enough:
its next ordinary column is not part of the represented socle.

The now-checked *literal* normalized M3 law implies that every
positive-level Kpt node has a genuine successor. Apply M3 at its
own level to duplicate its incoming canonical step. The argument
uses M3 but never assumes M2 or an SMTree instance.
-/

namespace SuccessorTree.V10

/-- Every positive-level admissible Kpt type has an immediate successor,
derived from the exact universally quantified M3 construction.
Unlike an abstract SMTree.pruned axiom, this is a theorem of the
normalized finite forbidden-free Kpt representation. -/
theorem admissibleKpt_exists_immediateSuccessor_of_level_pos
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (a : AdmissibleKptNode family)
    (hPos : 0 < LevelTree.lev a) :
    ∃ b : AdmissibleKptNode family, a ⋖ b := by
  let n : Nat := LevelTree.lev a - 1
  have hnlt : n < LevelTree.lev a := by
    dsimp [n]
    omega
  have hnle : n ≤ LevelTree.lev a := Nat.le_of_lt hnlt
  let q := LevelTree.ancestor a n hnle
  have hqLevel : LevelTree.lev q = n :=
    LevelTree.level_ancestor a n hnle
  have hqBelow : q ≤ a :=
    LevelTree.ancestor_le a n hnle
  have hqa : q ⋖ a := by
    apply LevelTree.covBy_of_le_level_succ hqBelow
    rw [hqLevel]
    dsimp [n]
    omega
  obtain ⟨p,c,hSucc⟩ := (admissibleKptSTree family).s3 hqa
  obtain ⟨D,_hD,_hSkip,hDuplicate⟩ :=
    m3OneGapShapeMap_literalM3 family n (LevelTree.lev a) hnlt
  have hAtA :
      (admissibleKptSTree family).succ a p c = some (D a) :=
    hDuplicate q a a p c hqLevel rfl hSucc le_rfl
  exact ⟨D a,(admissibleKptSTree family).covBy_of_succ_eq_some hAtA⟩

/-- The same conclusion in the successor notation used by the
boundary image-column proof: both a real parameter list and an
admissible terminal letter are available. -/
theorem admissibleKpt_exists_successor_step_of_level_pos
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (a : AdmissibleKptNode family)
    (hPos : 0 < LevelTree.lev a) :
    ∃ (b : AdmissibleKptNode family)
      (p : List (AdmissibleKptNode family))
      (c : AdmissibleKptSigma family),
      (admissibleKptSTree family).succ a p c = some b := by
  obtain ⟨b,hCover⟩ :=
    admissibleKpt_exists_immediateSuccessor_of_level_pos family a hPos
  obtain ⟨p,c,hSucc⟩ := (admissibleKptSTree family).s3 hCover
  exact ⟨b,p,c,hSucc⟩

end SuccessorTree.V10

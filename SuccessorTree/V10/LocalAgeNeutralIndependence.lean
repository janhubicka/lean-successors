import SuccessorTree.V10.LocalAgeNeutralEColumn
import Mathlib.Tactic

/-!
# Independence of ambient representation for neutral type insertion

A uniform Kpt map must send an admissible partial type to a new partial type
without inspecting which forbidden-free ambient structure happens to witness
its admissibility. We now prove exactly this for the NEUTRAL branch.

Two ambient witnesses of the same complete partial type give identical
complete partial types after inserting a neutral coordinate at ell, over the
extended cut. No choice of ambient witness is present in the conclusion.

The proof splits the target coordinates into the new ell-coordinate and all
old coordinates; the latter form the explicit image of the insertion map.
Old L+ atoms were checked in LocalAgeNeutralTransport. The newly inserted
binary/unary/diagonal atoms are neutral, and their E values are recovered
from the old E-row at ell-1 by LocalAgeNeutralEColumn.

The resulting well-defined neutral type map is the next construction.
Prescribed non-neutral crossings and the global ShapeMap are still open.
-/

namespace SuccessorTree.V10

/-- Every coordinate of an extended socle-plus-type record is either the
newly inserted ell coordinate or the image of a unique old coordinate. -/
theorem insertedTypeCoordinate_cases
    (cut ell : Nat) (hell : ell ≤ cut)
    (a : Option (Fin (cut + 1))) :
    a = some (⟨ell, by omega⟩ : Fin (cut + 1)) ∨
      ∃ b : Option (Fin cut), insertedTypeCoordinate ell b = a := by
  cases a with
  | none =>
      exact Or.inr ⟨none, rfl⟩
  | some i =>
      by_cases heq : i.val = ell
      · left
        exact congrArg Option.some (Fin.ext heq)
      · right
        let j : Fin cut := ⟨removeInserted ell i.val, by
          unfold removeInserted
          by_cases hlt : i.val < ell
          · simp [hlt] <;> omega
          · simp [hlt] <;> omega⟩
        refine ⟨some j, ?_⟩
        change (some (⟨insertAddress ell j.val, by
          unfold insertAddress
          split_ifs <;> omega⟩ : Fin (cut + 1))) = some i
        apply congrArg Option.some
        apply Fin.ext
        exact insertAddress_removeInserted ell i.val heq

/-- The complete *actual* L+ partial-type record of a neutral insertion is
independent of which forbidden-free finite ambient structure represented
the original record. It includes every positive and negative directed
binary fact, unary and diagonal fact, and all auxiliary E atoms. -/
theorem neutralInsert_partialType_independent
    {db du dd : Nat}
    (A C : EnumeratedPartialStructure db du dd)
    (ell cut v w : Nat)
    (hellA : ell ≤ A.size) (hellC : ell ≤ C.size) (hellPos : 0 < ell)
    (hCutLevel : ell ≤ cut)
    (hcutA : cut ≤ A.size) (hcutC : cut ≤ C.size)
    (hv : v < A.size) (hw : w < C.size)
    (hType : A.partialTypeAt cut v = C.partialTypeAt cut w) :
    (neutralInsert A ell hellA hellPos).partialTypeAt
        (cut + 1) (insertAddress ell v) =
      (neutralInsert C ell hellC hellPos).partialTypeAt
        (cut + 1) (insertAddress ell w) := by
  let B := neutralInsert A ell hellA hellPos
  let D := neutralInsert C ell hellC hellPos
  have hOldA := neutralInsert_partialType_old_atoms
    A ell hellA hellPos cut v hcutA hv
  have hOldC := neutralInsert_partialType_old_atoms
    C ell hellC hellPos cut w hcutC hw
  have hLA :
      (A.partialTypeAt cut v).lReduct =
        (C.partialTypeAt cut w).lReduct :=
    congrArg PartialTypeWithE.lReduct hType
  have hEA :
      (A.partialTypeAt cut v).eRelation =
        (C.partialTypeAt cut w).eRelation :=
    congrArg PartialTypeWithE.eRelation hType
  have hInA : ∀ a : Option (Fin cut),
      prefixVertexIndex v a < A.size :=
    fun a => prefixVertexIndex_inside v A.size hv hcutA a
  have hInC : ∀ a : Option (Fin cut),
      prefixVertexIndex w a < C.size :=
    fun a => prefixVertexIndex_inside w C.size hw hcutC a
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b t
      rcases insertedTypeCoordinate_cases cut ell hCutLevel a with
        ha | ⟨a0, ha⟩
      · subst a
        change B.L.binary ell
            (prefixVertexIndex (insertAddress ell v) b) t =
          D.L.binary ell
            (prefixVertexIndex (insertAddress ell w) b) t
        exact (neutralInsert_binary_from_inserted A ell hellA hellPos _ t).trans
          (neutralInsert_binary_from_inserted C ell hellC hellPos _ t).symm
      · subst a
        rcases insertedTypeCoordinate_cases cut ell hCutLevel b with
          hb | ⟨b0, hb⟩
        · subst b
          change B.L.binary
              (prefixVertexIndex (insertAddress ell v)
                (insertedTypeCoordinate ell a0)) ell t =
            D.L.binary
              (prefixVertexIndex (insertAddress ell w)
                (insertedTypeCoordinate ell a0)) ell t
          exact (neutralInsert_binary_to_inserted A ell hellA hellPos _ t).trans
            (neutralInsert_binary_to_inserted C ell hellC hellPos _ t).symm
        · subst b
          calc
            (B.partialTypeAt (cut+1) (insertAddress ell v)).lReduct.binary
                (insertedTypeCoordinate ell a0) (insertedTypeCoordinate ell b0) t
                = (A.partialTypeAt cut v).lReduct.binary a0 b0 t :=
                  hOldA.1 a0 b0 t
            _ = (C.partialTypeAt cut w).lReduct.binary a0 b0 t := by rw [hLA]
            _ = (D.partialTypeAt (cut+1) (insertAddress ell w)).lReduct.binary
                (insertedTypeCoordinate ell a0) (insertedTypeCoordinate ell b0) t :=
                  (hOldC.1 a0 b0 t).symm
    · intro a t
      rcases insertedTypeCoordinate_cases cut ell hCutLevel a with
        ha | ⟨a0, ha⟩
      · subst a
        change B.L.unary ell t = D.L.unary ell t
        exact (neutralInsert_unary_inserted A ell hellA hellPos t).trans
          (neutralInsert_unary_inserted C ell hellC hellPos t).symm
      · subst a
        calc
          (B.partialTypeAt (cut+1) (insertAddress ell v)).lReduct.unary
              (insertedTypeCoordinate ell a0) t
              = (A.partialTypeAt cut v).lReduct.unary a0 t := hOldA.2.1 a0 t
          _ = (C.partialTypeAt cut w).lReduct.unary a0 t := by rw [hLA]
          _ = (D.partialTypeAt (cut+1) (insertAddress ell w)).lReduct.unary
              (insertedTypeCoordinate ell a0) t := (hOldC.2.1 a0 t).symm
    · intro a t
      rcases insertedTypeCoordinate_cases cut ell hCutLevel a with
        ha | ⟨a0, ha⟩
      · subst a
        change B.L.diagonal ell t = D.L.diagonal ell t
        exact (neutralInsert_diagonal_inserted A ell hellA hellPos t).trans
          (neutralInsert_diagonal_inserted C ell hellC hellPos t).symm
      · subst a
        calc
          (B.partialTypeAt (cut+1) (insertAddress ell v)).lReduct.diagonal
              (insertedTypeCoordinate ell a0) t
              = (A.partialTypeAt cut v).lReduct.diagonal a0 t :=
                  hOldA.2.2.1 a0 t
          _ = (C.partialTypeAt cut w).lReduct.diagonal a0 t := by rw [hLA]
          _ = (D.partialTypeAt (cut+1) (insertAddress ell w)).lReduct.diagonal
              (insertedTypeCoordinate ell a0) t := (hOldC.2.2.1 a0 t).symm
  · intro a b
    rcases insertedTypeCoordinate_cases cut ell hCutLevel a with
      ha | ⟨a0, ha⟩
    · subst a
      rcases insertedTypeCoordinate_cases cut ell hCutLevel b with
        hb | ⟨b0, hb⟩
      · subst b
        change B.E ell ell = D.E ell ell
        exact (neutralInsert_new_E_loop_false A ell hellA hellPos).trans
          (neutralInsert_new_E_loop_false C ell hellC hellPos).symm
      · subst b
        change B.E ell
            (prefixVertexIndex (insertAddress ell v)
              (insertedTypeCoordinate ell b0)) =
          D.E ell
            (prefixVertexIndex (insertAddress ell w)
              (insertedTypeCoordinate ell b0))
        rw [prefixVertexIndex_insertedTypeCoordinate,
          prefixVertexIndex_insertedTypeCoordinate]
        calc
          B.E ell (insertAddress ell (prefixVertexIndex v b0)) =
              A.E (ell-1) (prefixVertexIndex v b0) :=
            neutralInsert_new_E_row A ell hellA hellPos _ (hInA b0)
          _ = C.E (ell-1) (prefixVertexIndex w b0) := by
            exact congrFun
              (congrFun hEA (some (⟨ell-1, by omega⟩ : Fin cut))) b0
          _ = D.E ell (insertAddress ell (prefixVertexIndex w b0)) :=
            (neutralInsert_new_E_row C ell hellC hellPos _ (hInC b0)).symm
    · subst a
      rcases insertedTypeCoordinate_cases cut ell hCutLevel b with
        hb | ⟨b0, hb⟩
      · subst b
        change B.E
            (prefixVertexIndex (insertAddress ell v)
              (insertedTypeCoordinate ell a0)) ell =
          D.E
            (prefixVertexIndex (insertAddress ell w)
              (insertedTypeCoordinate ell a0)) ell
        rw [prefixVertexIndex_insertedTypeCoordinate,
          prefixVertexIndex_insertedTypeCoordinate]
        exact (neutralInsert_old_E_to_new_false A ell hellA hellPos _).trans
          (neutralInsert_old_E_to_new_false C ell hellC hellPos _).symm
      · subst b
        calc
          (B.partialTypeAt (cut+1) (insertAddress ell v)).eRelation
              (insertedTypeCoordinate ell a0) (insertedTypeCoordinate ell b0)
              = (A.partialTypeAt cut v).eRelation a0 b0 :=
                  hOldA.2.2.2 a0 b0
          _ = (C.partialTypeAt cut w).eRelation a0 b0 := by rw [hEA]
          _ = (D.partialTypeAt (cut+1) (insertAddress ell w)).eRelation
              (insertedTypeCoordinate ell a0) (insertedTypeCoordinate ell b0) :=
                  (hOldC.2.2.2 a0 b0).symm

end SuccessorTree.V10

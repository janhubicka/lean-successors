import SuccessorTree.FreeAncestralSuccessor

/-! # Canonical intrinsic code of a cover in the free ancestral tree -/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat} [Fintype Label]

noncomputable def coverTuple
    {a b : Node Label arity}
    (hab : a ⋖ b) :
    ParamTuple arity a.level :=
  Classical.choose (exists_child_of_covBy hab)

noncomputable def coverLabel
    {a b : Node Label arity}
    (hab : a ⋖ b) :
    Label :=
  Classical.choose
    (Classical.choose_spec (exists_child_of_covBy hab))

theorem cover_eq_child
    {a b : Node Label arity}
    (hab : a ⋖ b) :
    b = child a (coverTuple hab) (coverLabel hab) :=
  Classical.choose_spec
    (Classical.choose_spec (exists_child_of_covBy hab))

noncomputable def coverCode
    {a b : Node Label arity}
    (hab : a ⋖ b) :
    Code Label arity a.level where
  label := coverLabel hab
  params := coverTuple hab

theorem freeSucc_cover
    {a b : Node Label arity}
    (hab : a ⋖ b) :
    freeSucc a
        (paramNodes a (coverTuple hab))
        (coverLabel hab) =
      some b := by
  calc
    freeSucc a
        (paramNodes a (coverTuple hab))
        (coverLabel hab) =
      some (child a (coverTuple hab) (coverLabel hab)) :=
        freeSucc_paramNodes
          a (coverTuple hab) (coverLabel hab)
    _ = some b :=
      congrArg some (cover_eq_child hab).symm

theorem cover_data_eq_of_child
    {a b : Node Label arity}
    (hab : a ⋖ b)
    (t : ParamTuple arity a.level)
    (c : Label)
    (hbc : b = child a t c) :
    coverTuple hab = t ∧ coverLabel hab = c := by
  have hchild :
      child a (coverTuple hab) (coverLabel hab) =
        child a t c :=
    (cover_eq_child hab).symm.trans hbc
  exact child_eq_data hchild

end FreeAncestral
end SuccessorTree

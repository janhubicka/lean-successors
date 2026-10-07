import SuccessorTree.FreeAncestralM2
import SuccessorTree.FreeAncestralM3
import SuccessorTree.Monoid

/-! # The free ancestral tree as an SMTree

All shape-preserving maps are admitted to the monoid family.  Hence M1 is
automatic; the content is exactly the explicit M2 and M3 constructions.
-/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat}
variable [Fintype Label] [Nonempty Label]

noncomputable def freeSMTree :
    SMTree (freeSTree (Label := Label) (arity := arity)) where
  M := Set.univ
  id_mem := by
    simp
  comp_mem := by
    intro F G hF hG
    simp
  fusion_mem := by
    intro F hmem hstable
    simp
  m2 := by
    intro n F hFM a ha hpos hskip
    obtain ⟨F1, F2, hF2skip, hEq⟩ :=
      free_m2_exists
        (Label := Label) (arity := arity)
        n F a ha hpos hskip
    refine ⟨F1, F2, ?_, ?_, hF2skip, hEq⟩ <;> simp
  m3 := by
    intro n m hnm
    obtain ⟨D, hDskip, hdup⟩ :=
      free_m3_exists
        (Label := Label) (arity := arity)
        n m hnm
    refine ⟨D, ?_, hDskip, hdup⟩
    simp

end FreeAncestral
end SuccessorTree

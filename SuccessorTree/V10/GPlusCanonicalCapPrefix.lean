import SuccessorTree.V10.GPlusNeutralCapType
import Mathlib.Tactic

/-!
# Observation 6.42: canonical neutral caps respect G+ finite prefixes

The full neutral-cap type is a deterministic extension of the finite
ordinary L+ code. Its raw Kpt node is therefore determined by the code,
even if its actual admissibility witness was chosen using Classical.choose.

Because the canonical type commutes with exact finite-table restriction,
the raw (and hence admissible) neutral caps over A and B are comparable
whenever A is a finite-code prefix of B.

This is the structural ingredient for preservation of comparability
under the genuine induced ShapeMap action. The next step takes the
corresponding lower image ancestors at levels lambda(|A|-1)+1 and
lambda(|B|-1)+1 and extracts their ordinary codes.

No extra Kpt prefix or ShapeMap axiom is assumed.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- The raw Kpt neutral type associated to the COMPLETE finite ordinary
code, without storing any uncountable off-carrier values. -/
def RawPartialTypeNode.neutralCapOfCode
    (C : FinitePartialCode db du dd) : RawPartialTypeNode db du dd :=
  ⟨C.size, C.neutralCapType⟩

/-- The raw Kpt node of every genuine canonical cap depends exactly
on the finite code, and not on the choice of raw witness. -/
theorem FiniteGPlusVertex.canonicalCap_raw_eq
    (A : FiniteGPlusVertex family) :
    A.canonicalCap.1 =
      RawPartialTypeNode.neutralCapOfCode A.val := by
  let W := A.chosenStructure
  have hNode :
      A.canonicalCap.1 =
        RawPartialTypeNode.neutralCapOfCode
          (FinitePartialCode.ofEnumerated W) := by
    change
      (⟨W.size,(NonedgePadding.socleCap W).partialTypeAt
        W.size (W.size+1)⟩ : RawPartialTypeNode db du dd) =
      (⟨W.size,(FinitePartialCode.ofEnumerated W).neutralCapType⟩ :
        RawPartialTypeNode db du dd)
    exact congrArg (Sigma.mk W.size)
      (NonedgePadding.socleCapNode_neutralCapType
        W (A.chosenStructure_spec).2.2)
  calc
    A.canonicalCap.1 =
        RawPartialTypeNode.neutralCapOfCode
          (FinitePartialCode.ofEnumerated W) := hNode
    _ = RawPartialTypeNode.neutralCapOfCode A.val := by
      rw [← (A.chosenStructure_spec).1]

/-- Literal finite prefixes give raw prefixes of their full
canonical neutral Kpt types, including the fixed type-vertex
column and all four original on-carrier tables. -/
theorem RawPartialTypeNode.neutralCapOfCode_isPrefix
    (A B : FinitePartialCode db du dd)
    (hAB : A.IsPrefix B) :
    RawPartialTypeNode.neutralCapOfCode A ≤
      RawPartialTypeNode.neutralCapOfCode B := by
  rcases hAB with ⟨hLen, hData⟩
  refine ⟨hLen, ?_⟩
  change A.neutralCapType = B.neutralCapType.restrict hLen
  have hRestr :
      (B.restrict A.size hLen).neutralCapType =
        B.neutralCapType.restrict hLen :=
    (B.neutralCapType_restrict A.size hLen).symm
  rw [←hData] at hRestr
  exact hRestr

/-- Genuine admissible canonical caps respect every initial-segment
order relation of the actual finite G+ tree. -/
theorem FiniteGPlusVertex.canonicalCap_le_of_prefix
    (A B : FiniteGPlusVertex family)
    (hAB : A.val.IsPrefix B.val) :
    A.canonicalCap ≤ B.canonicalCap := by
  change A.canonicalCap.1 ≤ B.canonicalCap.1
  rw [A.canonicalCap_raw_eq, B.canonicalCap_raw_eq]
  exact RawPartialTypeNode.neutralCapOfCode_isPrefix A.val B.val hAB

end SuccessorTree.V10

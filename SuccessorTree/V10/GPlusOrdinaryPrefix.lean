import SuccessorTree.V10.GPlusCanonicalRepresentatives
import Mathlib.Tactic

/-!
# Ordinary-code restriction commutes with Kpt partial-type restriction

The genuine Kpt forest is built from complete finite L+ records. This
module shows that taking the initial-socle prefix of such a record and
forgetting its distinguished type vertex gives precisely the
corresponding restriction of its finite ordinary G+ code.

All four tables (directed binary, unary, diagonal and E) are retained,
including false atoms. Consequently the already verified full
ordinary-code compatibility can be restricted to an earlier level,
and the genuine Kpt prefix order projects to the actual G+ prefix order.

This is a reusable finite-table lemma for Observation 6.42; it does not
postulate the full induced action of a ShapeMap on G+.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- Restricting a raw Kpt type and then taking its ordinary finite code
is literally finite-table restriction, including all auxiliary E bits. -/
theorem RawPartialTypeNode.ordinaryCode_ancestor
    (N : RawPartialTypeNode db du dd)
    (n : Nat) (hn : n ≤ N.1) :
    RawPartialTypeNode.ordinaryCode (rawPartialTypeAncestor N n hn) =
      (RawPartialTypeNode.ordinaryCode N).restrict n hn := by
  rfl

/-- Genuine raw full-type prefixes produce literal prefixes of finite
ordinary codes, rather than merely a positive relational homomorphism. -/
theorem RawPartialTypeNode.ordinaryCode_isPrefix
    {A B : RawPartialTypeNode db du dd} (h : A ≤ B) :
    (RawPartialTypeNode.ordinaryCode A).IsPrefix
      (RawPartialTypeNode.ordinaryCode B) := by
  rcases h with ⟨hn, hData⟩
  refine ⟨hn, ?_⟩
  rcases A with ⟨n,T⟩
  rcases B with ⟨m,U⟩
  change n ≤ m at hn
  change T = U.restrict hn at hData
  subst T
  exact RawPartialTypeNode.ordinaryCode_ancestor
    (⟨m,U⟩ : RawPartialTypeNode db du dd) n hn

/-- Genuine admissible Kpt prefixes induce real finite-code prefixes
between their extracted G+ vertices. -/
theorem admissibleKpt_toGPlus_isPrefix
    {A B : AdmissibleKptNode family}
    (hab : A ≤ B)
    (hA : 0 < A.1.1) (hB : 0 < B.1.1) :
    (AdmissibleKptNode.toGPlus A hA).val.IsPrefix
      (AdmissibleKptNode.toGPlus B hB).val := by
  have hRaw : A.1 ≤ B.1 := hab
  have hCode := RawPartialTypeNode.ordinaryCode_isPrefix hRaw
  rw [AdmissibleKptNode.toGPlus_code A hA,
      AdmissibleKptNode.toGPlus_code B hB]
  exact hCode

/-- Complete ordinary L+ compatibility survives truncation of the
common socle, without losing absent directed or E relation atoms. -/
theorem sameOrdinaryAtCut_restrict
    {n m : Nat} (T U : PartialTypeWithE n db du dd)
    (hm : m ≤ n) (h : SameOrdinaryAtCut T U) :
    SameOrdinaryAtCut (T.restrict hm) (U.restrict hm) := by
  have hCode := ordinaryCode_eq_of_sameOrdinary T U h
  have hRestricted :
      (RawPartialTypeNode.ordinaryCode
        (⟨n,T⟩ : RawPartialTypeNode db du dd)).restrict m hm =
      (RawPartialTypeNode.ordinaryCode
        (⟨n,U⟩ : RawPartialTypeNode db du dd)).restrict m hm := by
    rw [hCode]
  have hT := RawPartialTypeNode.ordinaryCode_ancestor
    (⟨n,T⟩ : RawPartialTypeNode db du dd) m hm
  have hU := RawPartialTypeNode.ordinaryCode_ancestor
    (⟨n,U⟩ : RawPartialTypeNode db du dd) m hm
  rw [←hT, ←hU] at hRestricted
  exact sameOrdinary_of_ordinaryCode_eq
    (T.restrict hm) (U.restrict hm) hRestricted

end SuccessorTree.V10

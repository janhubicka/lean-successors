import SuccessorTree.V10.GPlusNeutralCapType
import Mathlib.Tactic

/-!
# V10 Definition 6.43: actual G+ vertices represented below one Kpt node

Let U be a genuine admissible Kpt node of level m. Every positive
finite G+ code A which is an exact initial ordinary-code prefix of U
has a representation v(S,U)=A by taking S to be the Kpt ancestor
of U on level |A|-1.

This is the concrete common-upper representation required in the
envelope argument: a finite chain of G+ prefixes lying inside
the ordinary socle of a single admissible ambient type can use
one common actual upper Kpt node. The proof depends on the already
verified literal ordinary-code restriction and Kpt ancestor uniqueness,
not a new representation or action hypothesis.

The Algorithm 5.4 envelope still has to be shown to contain the
chosen lower ancestors, and its finite-approximation domain has to
contain the common upper U. Neither is assumed here.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

namespace GPlusRepresentingPair

/-- A genuine strict pair with a prescribed common upper Kpt node:
the lower node is its ancestor just BEFORE the requested prefix size. -/
noncomputable def fromUpper
    (U : AdmissibleKptNode family)
    (n : Nat) (hPos : 0 < n)
    (hn : n ≤ LevelTree.lev U) : GPlusRepresentingPair family := by
  have hnRaw : n ≤ U.1.1 := by
    change n ≤ U.1.1 at hn
    exact hn
  have hLower : n-1 ≤ U.1.1 := by omega
  let S := admissibleKptAncestor U (n-1) hLower
  have hSU : S ≤ U :=
    admissibleKptAncestor_le U (n-1) hLower
  have hSLevel : LevelTree.lev S = n-1 := rfl
  have hNe : S ≠ U := by
    intro h
    have hLevel := congrArg LevelTree.lev h
    rw [hSLevel] at hLevel
    omega
  exact ⟨S,U,lt_of_le_of_ne hSU hNe⟩

/-- The pair really represents a vertex with exactly n ordinary
coordinates, rather than n-1 or n+1. -/
@[simp] theorem fromUpper_cut
    (U : AdmissibleKptNode family)
    (n : Nat) (hPos : 0 < n) (hn : n ≤ LevelTree.lev U) :
    (fromUpper U n hPos hn).cut = n := by
  change n-1+1 = n
  omega

/-- Its represented partial-type node is the literal n-prefix of U.
Both are genuine admissible ancestors of one upper Kpt node,
and hence equal by uniqueness at the common level. -/
theorem fromUpper_representedNode
    (U : AdmissibleKptNode family)
    (n : Nat) (hPos : 0 < n) (hn : n ≤ LevelTree.lev U) :
    (fromUpper U n hPos hn).representedNode =
      admissibleKptAncestor U n hn := by
  let P := fromUpper U n hPos hn
  have hPLe : P.representedNode ≤ U :=
    admissibleKptAncestor_le U P.cut P.cut_le_upper
  have hPLevel : LevelTree.lev P.representedNode = n := by
    rw [P.representedNode_level, fromUpper_cut U n hPos hn]
  have hALe : admissibleKptAncestor U n hn ≤ U :=
    admissibleKptAncestor_le U n hn
  have hALevel : LevelTree.lev (admissibleKptAncestor U n hn) = n := rfl
  have hPAncestor : P.representedNode = LevelTree.ancestor U n hn :=
    LevelTree.eq_ancestor_of_le hPLe hPLevel hn
  have hAAncestor :
      admissibleKptAncestor U n hn = LevelTree.ancestor U n hn :=
    LevelTree.eq_ancestor_of_le hALe hALevel hn
  exact hPAncestor.trans hAAncestor.symm

/-- If A is already a genuine positive G+ prefix of U's complete
ordinary code, its ACTUAL common-upper representing pair returns A
with equality of every finite L+ atomic table. -/
theorem fromUpper_vertex_eq_of_prefix
    (U : AdmissibleKptNode family)
    (A : FiniteGPlusVertex family)
    (hAU : A.val.IsPrefix (RawPartialTypeNode.ordinaryCode U.1)) :
    (fromUpper U A.val.size (finiteGPlusVertex_size_pos A) hAU.1).vertex =
      A := by
  let P := fromUpper U A.val.size (finiteGPlusVertex_size_pos A) hAU.1
  have hN : P.representedNode =
      admissibleKptAncestor U A.val.size hAU.1 :=
    fromUpper_representedNode U A.val.size
      (finiteGPlusVertex_size_pos A) hAU.1
  apply Subtype.ext
  calc
    P.vertex.val = RawPartialTypeNode.ordinaryCode P.representedNode.1 :=
      P.vertex_code
    _ = RawPartialTypeNode.ordinaryCode
        (admissibleKptAncestor U A.val.size hAU.1).1 :=
      congrArg
        (fun T : AdmissibleKptNode family =>
          RawPartialTypeNode.ordinaryCode T.1) hN
    _ = (RawPartialTypeNode.ordinaryCode U.1).restrict
        A.val.size hAU.1 :=
      RawPartialTypeNode.ordinaryCode_ancestor U.1 A.val.size hAU.1
    _ = A.val := hAU.2.symm

/-- Every finite chain of genuine G+ vertices, each an exact prefix
of the same upper ordinary socle, has a family of REAL representing
pairs sharing that same upper Kpt node. This is the geometric
precursor to proving Algorithm 5.4 envelope coverage. -/
theorem commonUpper_represents_all
    (U : AdmissibleKptNode family)
    (X : Finset (FiniteGPlusVertex family))
    (hX : ∀ A, A ∈ X →
      A.val.IsPrefix (RawPartialTypeNode.ordinaryCode U.1)) :
    ∀ A, A ∈ X →
      ∃ P : GPlusRepresentingPair family,
        P.upper = U ∧ P.vertex = A := by
  intro A hA
  let hAU := hX A hA
  exact ⟨fromUpper U A.val.size (finiteGPlusVertex_size_pos A)
    hAU.1, rfl, fromUpper_vertex_eq_of_prefix U A hAU⟩

end GPlusRepresentingPair

end SuccessorTree.V10

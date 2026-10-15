import SuccessorTree.V10.GPlusRepresentingPairs
import Mathlib.Tactic

/-!
# Observation 6.42: every finite G+ code has a genuine canonical pair

The standard neutral cap of an actual finite forbidden-free L+ partial
structure preserves the ENTIRE ordinary finite code, including both
directed binary orientations, negative atoms, unary and diagonal records,
and the auxiliary E relation.  Its Kpt node therefore has exactly the
original structure as its intrinsic ordinary finite code.

For an arbitrary valid finite G+ vertex A, the canonical representing
pair uses the cap and its predecessor at |A|-1. The associated v(S,T)
cuts the cap at exactly |A|, hence returns its complete ordinary code A.

This is a genuine surjectivity theorem for the representing-pair map,
not a representation hypothesis.  The separately checked compatibility
and full-record recovery theorems are subsequently used to make the
ShapeMap image independent of a chosen pair.

No conclusion about the full Observation 6.42 action or Ramsey theorem is
assumed by this module.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- The intrinsic ordinary code of the neutral cap is literally the
entire original finite L+ table. All Boolean values are compared. -/
theorem NonedgePadding.socleCapNode_ordinaryCode
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    RawPartialTypeNode.ordinaryCode
      (NonedgePadding.socleCapNode family A hAvoid).1 =
        FinitePartialCode.ofEnumerated A := by
  change
    (FinitePartialCode.mk A.size
      (fun i j t => (NonedgePadding.socleCap A).L.binary i.val j.val t)
      (fun i t => (NonedgePadding.socleCap A).L.unary i.val t)
      (fun i t => (NonedgePadding.socleCap A).L.diagonal i.val t)
      (fun i j => (NonedgePadding.socleCap A).E i.val j.val)) =
    (FinitePartialCode.mk A.size
      (fun i j t => A.L.binary i.val j.val t)
      (fun i t => A.L.unary i.val t)
      (fun i t => A.L.diagonal i.val t)
      (fun i j => A.E i.val j.val))
  have hBinary :
      (fun i j : Fin A.size => fun t : Fin db =>
        (NonedgePadding.socleCap A).L.binary i.val j.val t) =
      (fun i j : Fin A.size => fun t : Fin db =>
        A.L.binary i.val j.val t) := by
    funext i j t
    exact NonedgePadding.twoNeutralL_old_binary A i.val j.val
      i.isLt j.isLt t
  have hUnary :
      (fun i : Fin A.size => fun t : Fin du =>
        (NonedgePadding.socleCap A).L.unary i.val t) =
      (fun i : Fin A.size => fun t : Fin du =>
        A.L.unary i.val t) := by
    funext i t
    exact NonedgePadding.twoNeutralL_old_unary A i.val i.isLt t
  have hDiagonal :
      (fun i : Fin A.size => fun t : Fin dd =>
        (NonedgePadding.socleCap A).L.diagonal i.val t) =
      (fun i : Fin A.size => fun t : Fin dd =>
        A.L.diagonal i.val t) := by
    funext i t
    exact NonedgePadding.twoNeutralL_old_diagonal A i.val i.isLt t
  have hE :
      (fun i j : Fin A.size =>
        (NonedgePadding.socleCap A).E i.val j.val) =
      (fun i j : Fin A.size => A.E i.val j.val) := by
    funext i j
    exact NonedgePadding.socleCap_old_E A i.val j.val j.isLt
  rw [hBinary, hUnary, hDiagonal, hE]

/-- Cap(A) has the original G+ vertex's genuine finite code; the chosen
raw partial-structure witness plays no role in the final equality. -/
theorem FiniteGPlusVertex.canonicalCap_ordinaryCode
    (A : FiniteGPlusVertex family) :
    RawPartialTypeNode.ordinaryCode A.canonicalCap.1 = A.val := by
  calc
    RawPartialTypeNode.ordinaryCode A.canonicalCap.1 =
        FinitePartialCode.ofEnumerated A.chosenStructure := by
      change RawPartialTypeNode.ordinaryCode
        (NonedgePadding.socleCapNode family A.chosenStructure
          (A.chosenStructure_spec).2.2).1 =
        FinitePartialCode.ofEnumerated A.chosenStructure
      exact NonedgePadding.socleCapNode_ordinaryCode
        A.chosenStructure (A.chosenStructure_spec).2.2
    _ = A.val := (A.chosenStructure_spec).1.symm

/-- Cutting the canonical cap at the represented pair's cut returns
the cap itself, as a genuine Kpt node, not just an equal-sized record. -/
theorem GPlusRepresentingPair.canonical_representedNode
    (A : FiniteGPlusVertex family) :
    (GPlusRepresentingPair.canonical A).representedNode =
      A.canonicalCap := by
  let P := GPlusRepresentingPair.canonical A
  have hLe : P.representedNode ≤ P.upper :=
    admissibleKptAncestor_le P.upper P.cut P.cut_le_upper
  have hLevel : P.representedNode.1.1 = P.upper.1.1 := by
    change P.cut = LevelTree.lev P.upper
    rw [GPlusRepresentingPair.canonical_cut A]
    exact (A.canonicalCap_level).symm
  have hRaw : P.representedNode.1 = P.upper.1 :=
    rawPartialTypePrefix_eq_of_same_level hLe hLevel
  have hEq : P.representedNode = P.upper := Subtype.ext hRaw
  calc
    (GPlusRepresentingPair.canonical A).representedNode =
        P.upper := hEq
    _ = A.canonicalCap := rfl

/-- Every genuine G+ vertex is represented by its canonical neutral-cap
pair: the original surjectivity half of Observation 6.42. -/
theorem GPlusRepresentingPair.canonical_vertex
    (A : FiniteGPlusVertex family) :
    (GPlusRepresentingPair.canonical A).vertex = A := by
  apply Subtype.ext
  calc
    (GPlusRepresentingPair.canonical A).vertex.val =
        RawPartialTypeNode.ordinaryCode
          (GPlusRepresentingPair.canonical A).representedNode.1 :=
      GPlusRepresentingPair.vertex_code _
    _ = RawPartialTypeNode.ordinaryCode A.canonicalCap.1 := by
      rw [GPlusRepresentingPair.canonical_representedNode A]
    _ = A.val := A.canonicalCap_ordinaryCode

/-- The genuine representing-pair map is surjective, with an explicit
canonical right inverse. No arbitrary representation is postulated. -/
theorem GPlusRepresentingPair.vertex_surjective :
    Function.Surjective (GPlusRepresentingPair.vertex (family:=family)) := by
  intro A
  exact ⟨GPlusRepresentingPair.canonical A,
    GPlusRepresentingPair.canonical_vertex A⟩

end SuccessorTree.V10

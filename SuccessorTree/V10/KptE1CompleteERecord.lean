import SuccessorTree.V10.KptE1AssembledSource
import SuccessorTree.V10.PartialTypeRestriction
import Mathlib.Tactic

/-!
# Literal auxiliary E record of the concrete Kpt E1 source witness

The preceding source construction proves exact forbidden L-age, its
complete L-reduct, and the true canonical free level of the last witness.
Here we compute every E atom of that ACTUAL finite partial structure.

For two ordinary coordinates the column is precisely the padded
free-cut predicate, without an additional admissibility hypothesis.
For the last distinguished type vertex, every ordinary coordinate is
E-related TO that witness, every reverse E relation is false and its
loop is false, as theorems from SpacedE and the actual final free cut.

Thus to show equality with a proposed source type Q, it suffices to
establish ordinary column cuts and the three canonical type-vertex
properties of Q. These must later be DERIVED from the genuine target
successor, the reindexing and the canonical parameter; we do not
postulate that an arbitrary raw type has these properties.
-/

namespace SuccessorTree.V10

/-- On ordinary coordinates the constructed source has EXACTLY the
prescribed E-profile bits, positive or negative. -/
theorem e1PaddedSourceStructure_ordinary_E
    {db du dd : Nat} {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (oldCut : Nat → Nat) (f : Nat)
    (hOld : ∀ v, v < n → oldCut v = 0 ∨ oldCut v < v)
    (hNew : f = 0 ∨ f < n)
    (hOrd : E1PaddedOrdinaryLinked Q oldCut f)
    (i j : Fin (n + 1)) :
    ((e1PaddedSourceStructure Q oldCut f hOld hNew hOrd).partialTypeAt
      (n + 1) (n + 2)).eRelation (some i) (some j) =
    decide (i.val < paddedE1FreeCutProfile n oldCut f j.val) := by
  have hj : j.val < n + 3 := by omega
  change decide (j.val < n + 3 ∧
    i.val < paddedE1FreeCutProfile n oldCut f j.val) =
    decide (i.val < paddedE1FreeCutProfile n oldCut f j.val)
  simp [hj]

/-- If Q's actual ordinary E columns are the prescribed initial cuts
and its distinguished type vertex has the standard fully-linked
socle, reverse E absence and loop absence, the actual source witness
reproduces ALL of Q's auxiliary E atoms literally. -/
theorem e1PaddedSourceStructure_complete_E
    {db du dd : Nat} {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (oldCut : Nat → Nat) (f : Nat)
    (hOld : ∀ v, v < n → oldCut v = 0 ∨ oldCut v < v)
    (hNew : f = 0 ∨ f < n)
    (hOrd : E1PaddedOrdinaryLinked Q oldCut f)
    (hColumns : ∀ i j : Fin (n + 1),
      Q.eRelation (some i) (some j) =
        decide (i.val < paddedE1FreeCutProfile n oldCut f j.val))
    (hType : ∀ i : Fin (n + 1),
      Q.eRelation (some i) none = true)
    (hReverse : ∀ i : Fin (n + 1),
      Q.eRelation none (some i) = false)
    (hLoop : Q.eRelation none none = false) :
    ∀ x y : Option (Fin (n + 1)),
      ((e1PaddedSourceStructure Q oldCut f hOld hNew hOrd).partialTypeAt
        (n + 1) (n + 2)).eRelation x y = Q.eRelation x y := by
  let A := e1PaddedSourceStructure Q oldCut f hOld hNew hOrd
  have hFree : A.freeLevel (n + 2) = n + 1 :=
    e1PaddedSourceStructure_freeLevel Q oldCut f hOld hNew hOrd
  have hCut : n + 1 ≤ A.freeLevel (n + 2) := by
    rw [hFree]
  intro x y
  cases x with
  | none =>
      cases y with
      | none =>
          exact (A.partialTypeAt_no_typeE_loop (n + 1) (n + 2)).trans
            hLoop.symm
      | some j =>
          exact (A.partialTypeAt_no_reverseE (n + 1) (n + 2) hCut j).trans
            (hReverse j).symm
  | some i =>
      cases y with
      | none =>
          exact (A.partialTypeAt_fullESocle (n + 1) (n + 2) hCut i).trans
            (hType i).symm
      | some j =>
          exact (e1PaddedSourceStructure_ordinary_E Q oldCut f
            hOld hNew hOrd i j).trans (hColumns i j).symm

/-- The resulting complete source L+ type is literally Q. This
requires neither an invented L/E witness nor a new global E1 axiom:
every E assumption is the corresponding explicit finite column fact
about the target-derived record Q. -/
theorem e1PaddedSourceStructure_complete_type
    {db du dd : Nat} {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (oldCut : Nat → Nat) (f : Nat)
    (hOld : ∀ v, v < n → oldCut v = 0 ∨ oldCut v < v)
    (hNew : f = 0 ∨ f < n)
    (hOrd : E1PaddedOrdinaryLinked Q oldCut f)
    (hColumns : ∀ i j : Fin (n + 1),
      Q.eRelation (some i) (some j) =
        decide (i.val < paddedE1FreeCutProfile n oldCut f j.val))
    (hType : ∀ i : Fin (n + 1),
      Q.eRelation (some i) none = true)
    (hReverse : ∀ i : Fin (n + 1),
      Q.eRelation none (some i) = false)
    (hLoop : Q.eRelation none none = false) :
    (e1PaddedSourceStructure Q oldCut f hOld hNew hOrd).partialTypeAt
      (n + 1) (n + 2) = Q := by
  apply PartialTypeWithE.eq_of_atoms
  · exact e1PaddedSourceStructure_L_type Q oldCut f
      hOld hNew hOrd
  · exact e1PaddedSourceStructure_complete_E Q oldCut f
      hOld hNew hOrd hColumns hType hReverse hLoop

/-- The padded finite L+ structure is an ACTUAL witness of full
Kpt admissibility, not merely of L-age avoidance, once the explicit
target-derived E-column facts are supplied. -/
theorem e1PaddedSourceStructure_isAdmissible
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (oldCut : Nat → Nat) (f : Nat)
    (hOld : ∀ v, v < n → oldCut v = 0 ∨ oldCut v < v)
    (hNew : f = 0 ∨ f < n)
    (hOrd : E1PaddedOrdinaryLinked Q oldCut f)
    (hColumns : ∀ i j : Fin (n + 1),
      Q.eRelation (some i) (some j) =
        decide (i.val < paddedE1FreeCutProfile n oldCut f j.val))
    (hType : ∀ i : Fin (n + 1),
      Q.eRelation (some i) none = true)
    (hReverse : ∀ i : Fin (n + 1),
      Q.eRelation none (some i) = false)
    (hLoop : Q.eRelation none none = false)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids Q.ageModel) :
    IsAdmissibleRawType family
      (⟨n+1,Q⟩ : RawPartialTypeNode db du dd) := by
  let A := e1PaddedSourceStructure Q oldCut f hOld hNew hOrd
  have hFree : A.freeLevel (n+2) = n+1 :=
    e1PaddedSourceStructure_freeLevel Q oldCut f hOld hNew hOrd
  have hRecord : A.partialTypeAt (n+1) (n+2) = Q :=
    e1PaddedSourceStructure_complete_type Q oldCut f
      hOld hNew hOrd hColumns hType hReverse hLoop
  refine ⟨A,n+2,?_,?_,?_⟩
  · change n+2 < n+3
    omega
  · exact e1PaddedSourceStructure_avoids family Q oldCut f
      hOld hNew hOrd hAvoid
  · change (⟨n+1,Q⟩ : RawPartialTypeNode db du dd) =
      ⟨A.freeLevel (n+2), A.partialTypeAt (A.freeLevel (n+2)) (n+2)⟩
    rw [hFree]
    exact congrArg (Sigma.mk (n+1)) hRecord.symm

end SuccessorTree.V10

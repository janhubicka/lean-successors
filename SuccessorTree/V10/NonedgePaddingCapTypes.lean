import SuccessorTree.V10.NonedgePaddingSocleCap
import SuccessorTree.V10.ShapeMapParameterPrefix
import Mathlib.Tactic

/-!
# All padded upper records in one genuine Kpt socle

The one-cap construction does not merely contain the padded L reduct.
It makes every selected upper vertex's original complete partial type
a literal ordinary-vertex parameter inside the SAME admissible Kpt
node. This includes all negative/directed L+ and E atoms. It is the
source-side conclusion needed before applying an arbitrary F.
-/

namespace SuccessorTree.V10

/-- If the full type of w is taken over s ordinary vertices, then the
ordinary type of its i-th socle vertex over a shorter cut is literally
that vertex's original type. No successor or age premise is needed. -/
theorem EnumeratedPartialStructure.fullSocle_ordinaryType
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (s w j n : Nat) (hj : j < s) (hn : n ≤ s) :
    (A.partialTypeAt s w).ordinaryType j hj n hn = A.partialTypeAt n j := by
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y t
      cases x <;> cases y <;> rfl
    · intro x t
      cases x <;> rfl
    · intro x t
      cases x <;> rfl
  · intro x y
    cases x <;> cases y <;> rfl

namespace NonedgePadding

/-- The entire complete type of an original ordinary vertex is
retrievable as an ordinary-vertex parameter of the ONE capped Kpt
node, without any arbitrary realization assumption. -/
theorem socleCapNode_ordinaryType {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (n j : Nat) (hn : n ≤ j) (hj : j < A.size) :
    (socleCapNode family A hAvoid).1.2.ordinaryType j hj n
       (le_trans hn (Nat.le_of_lt hj)) =
      A.partialTypeAt n j := by
  change ((socleCap A).partialTypeAt A.size (A.size+1)).ordinaryType
      j hj n (le_trans hn (Nat.le_of_lt hj)) = A.partialTypeAt n j
  calc
    ((socleCap A).partialTypeAt A.size (A.size+1)).ordinaryType
         j hj n (le_trans hn (Nat.le_of_lt hj)) =
      (socleCap A).partialTypeAt n j :=
        (socleCap A).fullSocle_ordinaryType A.size (A.size+1)
          j n hj (le_trans hn (Nat.le_of_lt hj))
    _ = A.partialTypeAt n j := socleCap_partialTypeAt A n j hn hj

/-- The simultaneous source padding theorem produces ONE Kpt node
which literally contains all selected complete upper source types at
their spaced addresses. There is no classwise choice and upper-upper
L relations remain unchanged. -/
theorem simultaneous_types_in_socleCapNode {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (C : EnumeratedPartialStructure db du dd)
    (A : AgeTestModel db du dd) (n N : Nat)
    (hC : n ≤ C.size)
    (hSocle : ∀ x y, x < n → y < n → ∀ t : Fin db,
      A.binary x y t = C.L.binary x y t)
    (hn : n ≤ N) (hCarrier : ∀ x, x ∈ A.carrier ↔ x < N)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A)
    (T : Nat → PartialTypeWithE n db du dd)
    (hAd : ∀ i, n ≤ i → i < N → IsAdmissibleRawType family
      (⟨n,T i⟩ : RawPartialTypeNode db du dd))
    (hL : ∀ i, n ≤ i → i < N →
      RelationalPrefixType.ofAgeModel A n i = (T i).lReduct)
    (hE : ∀ i, n ≤ i → i < N → ∀ j k : Fin n,
      C.E j.val k.val = (T i).eRelation (some j) (some k)) :
    ∃ X : AdmissibleKptNode family,
      LevelTree.lev X = size n N ∧
      ∀ i, n ≤ i → i < N →
        ∃ (hj : address n i < LevelTree.lev X)
          (hf : n ≤ LevelTree.lev X),
          X.1.2.ordinaryType (address n i) hj n hf = T i := by
  let B := partialStructure C A n N hC hSocle
  obtain ⟨hAvoidB,hTypeB⟩ :=
    simultaneous_full_types family C A n N hC hSocle hn hCarrier
      hAvoid T hAd hL hE
  let X := socleCapNode family B hAvoidB
  refine ⟨X,rfl,?_⟩
  intro i hni hi
  have hAddr : n ≤ address n i := by
    simp only [address]
    split_ifs <;> omega
  have hj : address n i < B.size := by
    change address n i < size n N
    exact address_lt_size n N i hi
  have hf : n ≤ B.size := by
    change n ≤ size n N
    exact size_ge n N
  refine ⟨hj,hf,?_⟩
  have hOrig := socleCapNode_ordinaryType family B hAvoidB
    n (address n i) hAddr hj
  have hType := hTypeB i hni hi
  exact hOrig.trans hType

end NonedgePadding
end SuccessorTree.V10

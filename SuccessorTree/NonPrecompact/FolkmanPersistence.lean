import SuccessorTree.NonPrecompact.CopyRamseyDegree
import SuccessorTree.NonPrecompact.ColouringWrappers

/-!
# Persistent copy colourings for Folkman--BANANA

Finite Boolean rings are represented by their finite atom sets.  A non-unital
embedding sends every source atom to a nonempty block of target atoms; these
blocks are pairwise disjoint, while unused target atoms are allowed.  We
encode this by an `Option`-valued owner map, with `none` for unused atoms.

The bilinear map is determined by its values on atom pairs.  The ordinary
integer count in the manuscript is the number of incident atom pairs inside
two chosen blocks.  We define it as a double finite sum; this makes its
additivity over disjoint atom blocks explicit.

The main theorem fixes one ambient colouring before any target embedding and
proves that every embedded diagonal `B_q^{FU}` sees the full odd residue
palette.  The final theorem turns this into infinite copy Ramsey degree with
the manuscript's quantifier order.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- Ordinary integer number of incident atom pairs inside `X × Y`. -/
def folkmanEdgeCount
    {l r : ℕ}
    (edge : Fin l → Fin r → F2)
    (X : Finset (Fin l)) (Y : Finset (Fin r)) : ℕ :=
  ∑ x ∈ X, ∑ y ∈ Y, if edge x y = 1 then 1 else 0

/-- The atom block owned by source atom `j`. -/
def folkmanFiber
    {q n : ℕ}
    (owner : Fin n → Option (Fin q))
    (j : Fin q) : Finset (Fin n) :=
  Finset.univ.filter fun x => owner x = some j

/-- Distinct owner fibres are disjoint. -/
theorem folkmanFiber_pairwiseDisjoint
    {q n : ℕ}
    (owner : Fin n → Option (Fin q))
    (labels : Finset (Fin q)) :
    (labels : Set (Fin q)).PairwiseDisjoint (folkmanFiber owner) := by
  intro i hi j hj hij
  change Disjoint (folkmanFiber owner i) (folkmanFiber owner j)
  rw [Finset.disjoint_left]
  intro x hxi hxj
  have hxi' := (Finset.mem_filter.mp hxi).2
  have hxj' := (Finset.mem_filter.mp hxj).2
  apply hij
  exact Option.some.inj (hxi'.symm.trans hxj')

/-- Edge count is additive over disjoint owner fibres on the left. -/
theorem folkmanEdgeCount_biUnion_left
    {q l r : ℕ}
    (edge : Fin l → Fin r → F2)
    (owner : Fin l → Option (Fin q))
    (labels : Finset (Fin q))
    (Y : Finset (Fin r)) :
    folkmanEdgeCount edge
        (labels.biUnion (folkmanFiber owner)) Y =
      ∑ j ∈ labels,
        folkmanEdgeCount edge (folkmanFiber owner j) Y := by
  unfold folkmanEdgeCount
  rw [Finset.sum_biUnion (folkmanFiber_pairwiseDisjoint owner labels)]

/-- Edge count is additive over disjoint owner fibres on the right. -/
theorem folkmanEdgeCount_biUnion_right
    {q l r : ℕ}
    (edge : Fin l → Fin r → F2)
    (X : Finset (Fin l))
    (owner : Fin r → Option (Fin q))
    (labels : Finset (Fin q)) :
    folkmanEdgeCount edge X
        (labels.biUnion (folkmanFiber owner)) =
      ∑ j ∈ labels,
        folkmanEdgeCount edge X (folkmanFiber owner j) := by
  unfold folkmanEdgeCount
  calc
    (∑ x ∈ X,
        ∑ y ∈ labels.biUnion (folkmanFiber owner),
          if edge x y = 1 then 1 else 0) =
      ∑ x ∈ X, ∑ j ∈ labels,
        ∑ y ∈ folkmanFiber owner j,
          if edge x y = 1 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_biUnion
          (folkmanFiber_pairwiseDisjoint owner labels)]
    _ = ∑ j ∈ labels, ∑ x ∈ X,
        ∑ y ∈ folkmanFiber owner j,
          if edge x y = 1 then 1 else 0 := by
        rw [Finset.sum_comm]

/-- A finite Folkman--BANANA structure in atom coordinates. -/
structure FolkmanAtomStructure where
  leftCount : ℕ
  rightCount : ℕ
  edge : Fin leftCount → Fin rightCount → F2

/-- A non-unital Boolean-ring embedding in atom coordinates.

An ambient atom is owned by at most one source atom; `none` means that the
ambient atom is unused by the embedding.  Every source atom has a nonempty
fibre.  The final field is precisely preservation of the bilinear map on
source atoms. -/
structure FolkmanAtomEmbedding
    (A B : FolkmanAtomStructure) where
  leftOwner : Fin B.leftCount → Option (Fin A.leftCount)
  rightOwner : Fin B.rightCount → Option (Fin A.rightCount)
  left_fibre_nonempty :
    ∀ i, (folkmanFiber leftOwner i).Nonempty
  right_fibre_nonempty :
    ∀ j, (folkmanFiber rightOwner j).Nonempty
  pairing_parity :
    ∀ i j,
      (folkmanEdgeCount B.edge
          (folkmanFiber leftOwner i)
          (folkmanFiber rightOwner j) : F2) =
        A.edge i j

namespace FolkmanAtomStructure

/-- The `q`-atom diagonal target `B_q^{FU}`. -/
def diagonal (q : ℕ) : FolkmanAtomStructure where
  leftCount := q
  rightCount := q
  edge := fun i j => if i = j then 1 else 0

end FolkmanAtomStructure

/-- A copy of the one-atom-per-side source `A_×`.

The copy is determined by nonempty left and right atom blocks.  Pairing one
is equivalent to the ordinary incident-pair count being odd. -/
structure FolkmanAxCopy (C : FolkmanAtomStructure) where
  leftBlock : Finset (Fin C.leftCount)
  rightBlock : Finset (Fin C.rightCount)
  left_nonempty : leftBlock.Nonempty
  right_nonempty : rightBlock.Nonempty
  edgeCount_odd :
    Odd (folkmanEdgeCount C.edge leftBlock rightBlock)

namespace FolkmanAxCopy

/-- A source copy lies inside the range of a target embedding iff each of its
two atom blocks is a union of target owner fibres. -/
def Inside
    {B C : FolkmanAtomStructure}
    (P : FolkmanAxCopy C)
    (f : FolkmanAtomEmbedding B C) : Prop :=
  ∃ leftLabels : Finset (Fin B.leftCount),
    ∃ rightLabels : Finset (Fin B.rightCount),
      P.leftBlock =
          leftLabels.biUnion (folkmanFiber f.leftOwner) ∧
      P.rightBlock =
          rightLabels.biUnion (folkmanFiber f.rightOwner)

namespace Colour

/-- The incident-pair residue of an `A_×` copy is always an odd residue. -/
noncomputable def residue
    {C : FolkmanAtomStructure}
    (P : FolkmanAxCopy C) (k : ℕ) :
    ResidueParityColour k 1 := by
  refine ⟨
    (folkmanEdgeCount C.edge P.leftBlock P.rightBlock :
      ZMod (2 ^ (k + 1))), ?_⟩
  simp only [BananaMatrixStructure.residueParityPalette,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [residueParityHom_natCast]
  exact P.edgeCount_odd.natCast_zmod_two

/-- Enumerate the odd residue palette by `Fin (2^k)`. -/
noncomputable def fin
    {C : FolkmanAtomStructure}
    (P : FolkmanAxCopy C) (k : ℕ) :
    Fin (2 ^ k) :=
  residueParityColourEquivFin k 1 (residue P k)

end Colour

end FolkmanAxCopy

namespace FolkmanAtomEmbedding

variable {B C : FolkmanAtomStructure}

/-- In an embedded diagonal target, the ordinary count between one left
source-atom fibre and the union of all right fibres is odd. -/
theorem diagonal_left_to_allRight_odd
    (k : ℕ)
    (f :
      FolkmanAtomEmbedding
        (FolkmanAtomStructure.diagonal (2 ^ (k + 1))) C)
    (i : Fin (2 ^ (k + 1))) :
    Odd
      (folkmanEdgeCount C.edge
        (folkmanFiber f.leftOwner i)
        (Finset.univ.biUnion (folkmanFiber f.rightOwner))) := by
  apply ZMod.natCast_eq_one_iff_odd.mp
  rw [folkmanEdgeCount_biUnion_right, Nat.cast_sum]
  calc
    (∑ j ∈ (Finset.univ : Finset (Fin (2 ^ (k + 1)))),
        (folkmanEdgeCount C.edge
          (folkmanFiber f.leftOwner i)
          (folkmanFiber f.rightOwner j) : F2)) =
      ∑ j ∈ (Finset.univ : Finset (Fin (2 ^ (k + 1)))),
        (if i = j then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact f.pairing_parity i j
    _ = 1 := by simp

end FolkmanAtomEmbedding

/-- The full fixed-ambient persistent colouring for Folkman--BANANA.

For every ambient structure, one `2^k`-colouring is fixed before the target
embedding.  Every embedded diagonal target with `2^(k+1)` atoms on each
side contains every colour. -/
theorem exists_folkmanPersistentColouring
    (k : ℕ)
    (C : FolkmanAtomStructure) :
    ∃ colouring : FolkmanAxCopy C → Fin (2 ^ k),
      ∀ f :
          FolkmanAtomEmbedding
            (FolkmanAtomStructure.diagonal (2 ^ (k + 1))) C,
        ∀ colour : Fin (2 ^ k),
          ∃ P : FolkmanAxCopy C,
            P.Inside f ∧ colouring P = colour := by
  classical
  let colouring : FolkmanAxCopy C → Fin (2 ^ k) :=
    fun P => FolkmanAxCopy.Colour.fin P k
  refine ⟨colouring, ?_⟩
  intro f colour

  let allRight : Finset (Fin C.rightCount) :=
    Finset.univ.biUnion (folkmanFiber f.rightOwner)
  let a : Fin (2 ^ (k + 1)) → ℕ :=
    fun i =>
      folkmanEdgeCount C.edge
        (folkmanFiber f.leftOwner i) allRight
  let omitted : Fin (2 ^ (k + 1)) := 0
  let s : Finset (Fin (2 ^ (k + 1))) :=
    Finset.univ.erase omitted

  have hcard : s.card + 1 = 2 ^ (k + 1) := by
    dsimp [s]
    rw [Finset.card_erase_add_one (Finset.mem_univ omitted)]
    simp

  have ha : ∀ i ∈ s, Odd (a i) := by
    intro i hi
    exact f.diagonal_left_to_allRight_odd k i

  let z : ResidueParityColour k 1 :=
    (residueParityColourEquivFin k 1).symm colour

  have hzParity : residueParityHom k z.1 = 1 :=
    (Finset.mem_filter.mp z.2).2

  have hzValParity : (z.1.val : F2) = 1 := by
    calc
      (z.1.val : F2) =
          residueParityHom k
            (z.1.val : ZMod (2 ^ (k + 1))) :=
        (residueParityHom_natCast k z.1.val).symm
      _ = residueParityHom k z.1 := by
        rw [ZMod.natCast_zmod_val]
      _ = 1 := hzParity

  have hzOdd : Odd z.1.val :=
    ZMod.natCast_eq_one_iff_odd.mp hzValParity

  obtain ⟨t, ht, htne, hsumOdd, hresidue⟩ :=
    folkman_odd_residue_copy_witness
      (k := k + 1) (by omega)
      s a hcard ha z.1.val hzOdd

  let leftBlock : Finset (Fin C.leftCount) :=
    t.biUnion (folkmanFiber f.leftOwner)

  have hcount :
      folkmanEdgeCount C.edge leftBlock allRight =
        ∑ i ∈ t, a i := by
    simpa only [leftBlock, a] using
      folkmanEdgeCount_biUnion_left
        C.edge f.leftOwner t allRight

  have hleftNonempty : leftBlock.Nonempty := by
    obtain ⟨i, hi⟩ := htne
    obtain ⟨x, hx⟩ := f.left_fibre_nonempty i
    refine ⟨x, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩

  have hrightNonempty : allRight.Nonempty := by
    let j : Fin (2 ^ (k + 1)) := 0
    obtain ⟨y, hy⟩ := f.right_fibre_nonempty j
    refine ⟨y, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hy⟩

  let P : FolkmanAxCopy C := {
    leftBlock := leftBlock
    rightBlock := allRight
    left_nonempty := hleftNonempty
    right_nonempty := hrightNonempty
    edgeCount_odd := by
      rw [hcount]
      exact hsumOdd
  }

  have hinside : P.Inside f := by
    refine ⟨t, Finset.univ, ?_, ?_⟩
    · rfl
    · rfl

  refine ⟨P, hinside, ?_⟩

  have hcolourResidue :
      (folkmanEdgeCount C.edge leftBlock allRight :
        ZMod (2 ^ (k + 1))) = z.1 := by
    rw [hcount, Nat.cast_sum]
    calc
      (∑ i ∈ t, (a i : ZMod (2 ^ (k + 1)))) =
          (z.1.val : ZMod (2 ^ (k + 1))) := hresidue
      _ = z.1 := ZMod.natCast_zmod_val z.1

  have hsub : FolkmanAxCopy.Colour.residue P k = z := by
    apply Subtype.ext
    exact hcolourResidue

  change residueParityColourEquivFin k 1 (FolkmanAxCopy.Colour.residue P k) = colour
  rw [hsub]
  exact (residueParityColourEquivFin k 1).apply_symm_apply colour

/-- Copy Ramsey degree at most `t` for the one-atom-per-side source
`A_×`, using actual copy-ranges in the finite atom presentation. -/
def folkmanAxCopyRamseyDegreeLE (t : ℕ) : Prop :=
  ∀ (B : FolkmanAtomStructure)
      (numColours : ℕ), 0 < numColours →
    ∃ C : FolkmanAtomStructure,
      ∀ colouring : FolkmanAxCopy C → Fin numColours,
        ∃ f : FolkmanAtomEmbedding B C,
          ∃ colours : Finset (Fin numColours),
            colours.card ≤ t ∧
            ∀ P : FolkmanAxCopy C,
              P.Inside f → colouring P ∈ colours

/-- The Folkman source `A_×` has infinite copy Ramsey degree. -/
def folkmanAxCopyRamseyDegreeInfinite : Prop :=
  ∀ t : ℕ, ¬ folkmanAxCopyRamseyDegreeLE t

/-- The persistent power-of-two colourings rule out every finite copy
Ramsey-degree bound for `A_×`. -/
theorem folkmanAxCopyRamseyDegree_infinite :
    folkmanAxCopyRamseyDegreeInfinite := by
  intro t hdegree
  let B := FolkmanAtomStructure.diagonal (2 ^ (t + 1))
  obtain ⟨C, hC⟩ :=
    hdegree B (2 ^ t) (by positivity)
  obtain ⟨colouring, hpersistent⟩ :=
    exists_folkmanPersistentColouring t C
  obtain ⟨f, colours, hcard, hcolours⟩ :=
    hC colouring

  have huniv : colours = Finset.univ := by
    ext colour
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨P, hinside, hPcolour⟩ :=
      hpersistent f colour
    have hmem := hcolours P hinside
    rw [hPcolour] at hmem
    exact hmem

  have hle : 2 ^ t ≤ t := by
    rw [huniv] at hcard
    simpa using hcard
  exact (Nat.not_le_of_gt t.lt_two_pow_self) hle

end SuccessorTree.NonPrecompact

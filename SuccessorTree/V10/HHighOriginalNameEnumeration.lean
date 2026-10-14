import SuccessorTree.V10.HGenerationHighBudget
import Mathlib.Tactic

/-!
# Proposition 6.44: enumerate high names inside one fixed original pool

The stage-pool invariant supplies a finite set V of actual ambient
original ADDRESSES. Its Fin V.card enumeration gives the fixed
name universe used by the indexed I3 signatures.

At generation r only names whose real H coordinates have
generation >r may appear above the tested level (Lemma 6.53).
We construct precisely the finite subset of those names and
enumerate it without changing the underlying original addresses.

The resulting high-name cardinal is no greater than the
already-checked hGenerationHighOriginals count that bounds
the (I1)/(I2) meet levels. Therefore the two contributions can
use one and the same M_r in the manuscript's recursion.
-/

namespace SuccessorTree.V10

/-- An original name in the finite stage-pool enumeration retains
the actual ambient address, rather than merely its partial type. -/
noncomputable def hOriginalName
    {N : Nat} (V : Finset (Fin N)) (i : Fin V.card) : Fin N :=
  (V.equivFin.symm i).val

theorem hOriginalName_mem
    {N : Nat} (V : Finset (Fin N)) (i : Fin V.card) :
    hOriginalName V i ∈ V :=
  (V.equivFin.symm i).property

theorem hOriginalName_injective
    {N : Nat} (V : Finset (Fin N)) :
    Function.Injective (hOriginalName V) := by
  intro i j h
  apply V.equivFin.symm.injective
  exact Subtype.ext h

/-- Exactly the indices naming members of V in real H
generation strictly greater than r. -/
noncomputable def hHighOriginalNameIndices
    {N : Nat} (k r : Nat) (V : Finset (Fin N)) :
    Finset (Fin V.card) := by
  classical
  exact Finset.univ.filter
    (fun i => hOriginalName V i ∈ hGenerationHighOriginals k r V)

theorem hHighOriginalNameIndices_mem_iff
    {N : Nat} (k r : Nat) (V : Finset (Fin N)) (i : Fin V.card) :
    i ∈ hHighOriginalNameIndices k r V ↔
      hOriginalName V i ∈ hGenerationHighOriginals k r V := by
  classical
  simp [hHighOriginalNameIndices]

/-- The high-name enumeration covers every actually high name.
No representative outside V may be introduced. -/
noncomputable def hHighOriginalName
    {N : Nat} (k r : Nat) (V : Finset (Fin N))
    (j : Fin (hHighOriginalNameIndices k r V).card) : Fin V.card :=
  ((hHighOriginalNameIndices k r V).equivFin.symm j).val

theorem hHighOriginalName_surjective_on_high
    {N : Nat} (k r : Nat) (V : Finset (Fin N))
    (i : Fin V.card)
    (hi : hOriginalName V i ∈ hGenerationHighOriginals k r V) :
    ∃ j : Fin (hHighOriginalNameIndices k r V).card,
      hHighOriginalName k r V j = i := by
  let W := hHighOriginalNameIndices k r V
  have hiW : i ∈ W :=
    (hHighOriginalNameIndices_mem_iff k r V i).2 hi
  refine ⟨W.equivFin ⟨i,hiW⟩,?_⟩
  simp [hHighOriginalName, W]

/-- Injectivity of actual original addresses gives a cardinal
injection from high names into actual higher-generation
originals of the SAME stage pool. -/
theorem hHighOriginalNameIndices_card_le
    {N : Nat} (k r : Nat) (V : Finset (Fin N)) :
    (hHighOriginalNameIndices k r V).card ≤
      (hGenerationHighOriginals k r V).card := by
  classical
  let W := hHighOriginalNameIndices k r V
  have hInjective : Set.InjOn (hOriginalName V) (W : Set (Fin V.card)) := by
    intro a _ b _ h
    exact hOriginalName_injective V h
  have hCardImage :
      (W.image (hOriginalName V)).card = W.card :=
    Finset.card_image_iff.mpr hInjective
  have hImageSub :
      W.image (hOriginalName V) ⊆ hGenerationHighOriginals k r V := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact (hHighOriginalNameIndices_mem_iff k r V i).1 hi
  calc
    W.card = (W.image (hOriginalName V)).card := hCardImage.symm
    _ ≤ (hGenerationHighOriginals k r V).card :=
      Finset.card_le_card hImageSub

/-- If every actual higher-generation original is covered by
an inductive cardinal budget M_r, then the enumeration of
higher original NAMES has at most M_r elements. -/
theorem hHighOriginalNameIndices_card_le_budget
    {N : Nat} (k r : Nat) (V : Finset (Fin N))
    (Mr : Nat)
    (hBudget : (hGenerationHighOriginals k r V).card ≤ Mr) :
    (hHighOriginalNameIndices k r V).card ≤ Mr :=
  (hHighOriginalNameIndices_card_le k r V).trans hBudget

/-- Apply the real-position formula for higher generation,
then choose the original NAME in the checked smaller
enumeration. This is the exact coverage interface required
by the selected-stage R(M_r) theorem. -/
theorem hHighOriginalName_covers_real_higher
    {N : Nat} (k r : Nat) (V : Finset (Fin N))
    (i : Fin V.card)
    (hReal : ∃ p m : Nat,
      r < m ∧ m ≤ k ∧
        (hOriginalName V i).val = hPosition k p m) :
    ∃ j : Fin (hHighOriginalNameIndices k r V).card,
      hHighOriginalName k r V j = i := by
  have hiHigh : hOriginalName V i ∈
      hGenerationHighOriginals k r V := by
    classical
    simp only [hGenerationHighOriginals, Finset.mem_filter,
      hOriginalName_mem, true_and]
    exact hReal
  exact hHighOriginalName_surjective_on_high k r V i hiHigh

end SuccessorTree.V10

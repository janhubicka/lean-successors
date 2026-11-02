import SuccessorTree.HalesJewett.AlphabetInduction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-!
# A finite window for starred Hales--Jewett

The proved theorem `starHJ_finite` colours all finite words at once.  For
finite structural applications we only need a finite initial window.  Compactness
of the product of the finite discrete colour space gives a uniform window
depending only on the alphabet and the colour type.
-/

namespace SuccessorTree
namespace HalesJewett

universe u v

/-- Words available in the initial length window. -/
abbrev WindowWord (α : Type u) (N : Nat) :=
  {w : List α // w.length ≤ N}

/-- The starred Hales--Jewett conclusion using only words of length at most
`N`.  The raw line itself also has length at most `N`, so its star and every
ordinary evaluation belong to the same window. -/
def StarHJWindow (α : Type u) (κ : Type v)
    [Fintype α] [Fintype κ] (N : Nat) : Prop :=
  ∀ colour : WindowWord α N → κ,
    ∃ L : StarLine α, ∃ hL : L.word.length ≤ N,
      ∀ a : α,
        colour ⟨L.eval a, by simpa using hL⟩ =
        colour ⟨L.star,
          le_trans L.length_star_le_word_length hL⟩

/-- For fixed finite alphabet and finite nonempty colour type, one finite word
window already contains a monochromatic starred line for every colouring.

The proof is a compactness corollary of `starHJ_finite`: for each line, the
set of global colourings making that line monochromatic is an open cylinder.
These cylinders cover the compact product of the finite discrete colour space,
so finitely many lines suffice. -/
theorem exists_starHJWindow
    (α : Type u) (κ : Type v)
    [Fintype α] [Fintype κ] [Nonempty κ] :
    ∃ N : Nat, StarHJWindow α κ N := by
  classical
  letI : TopologicalSpace κ := ⊥
  letI : DiscreteTopology κ := discreteTopology_bot κ
  letI : CompactSpace κ := Finite.compactSpace
  let Colour := List α → κ
  let U : StarLine α → Set Colour :=
    fun L => {c | StarMonochromatic c L}

  have hUopen : ∀ L : StarLine α, IsOpen (U L) := by
    intro L
    have hEq :
        U L =
          ⋂ a : α, {c : Colour | c (L.eval a) = c L.star} := by
      ext c
      simp [U, StarMonochromatic]
    rw [hEq]
    apply isOpen_iInter_of_finite
    intro a
    let pair : Colour → κ × κ :=
      fun c => (c (L.eval a), c L.star)
    have hpair : Continuous pair := by
      fun_prop
    have hopen : IsOpen {p : κ × κ | p.1 = p.2} :=
      isOpen_discrete _
    exact hopen.preimage hpair

  have hcover :
      (Set.univ : Set Colour) ⊆ ⋃ L : StarLine α, U L := by
    intro c hc
    obtain ⟨L, hL⟩ :=
      (starHJ_finite (α := α) (κ := κ)) c
    exact Set.mem_iUnion.mpr ⟨L, hL⟩

  obtain ⟨lines : Finset (StarLine α), hlines⟩ :=
    isCompact_univ.elim_finite_subcover U hUopen hcover
  let N : Nat := lines.sup fun L => L.word.length
  refine ⟨N, ?_⟩
  intro colour

  let defaultColour : κ := Classical.choice (inferInstance : Nonempty κ)
  let ext : Colour := fun w =>
    if h : w.length ≤ N then colour ⟨w, h⟩ else defaultColour

  have hext : ext ∈ (Set.univ : Set Colour) := Set.mem_univ ext
  have hfinite := hlines hext
  obtain ⟨L, hL⟩ := Set.mem_iUnion.mp hfinite
  obtain ⟨hLs, hmono⟩ := Set.mem_iUnion.mp hL
  have hLen : L.word.length ≤ N := by
    exact Finset.le_sup (f := fun L : StarLine α => L.word.length) hLs
  refine ⟨L, hLen, ?_⟩
  intro a
  have hEval : (L.eval a).length ≤ N := by
    simpa using hLen
  have hStar : L.star.length ≤ N :=
    le_trans L.length_star_le_word_length hLen
  have hmono' : ext (L.eval a) = ext L.star := hmono a
  simpa [ext, hEval, hStar] using hmono'

end HalesJewett
end SuccessorTree

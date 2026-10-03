import SuccessorTree.NonPrecompact.PrebananaPersistence

/-!
# Copy Ramsey degree of the two-marked-atom pre-BANANA source

This file adds the abstract degree layer to the fixed-ambient colouring in
`PrebananaPersistence.lean`.

Finite pre-BANANA structures are written in standard atom coordinates.
A structure is therefore a nonempty finite atom set together with a marking
whose total marked count is even.  A unital Boolean-algebra embedding is
represented by the induced partition of the target atoms into nonempty
fibres; preservation of the unary marking is exactly preservation of the
marked-count parity on every fibre.

This is the usual finite-atom presentation from the circulation manuscript.
It lets the copy Ramsey degree be stated with the manuscript's actual
copy-ranges: a two-atom copy is canonically oriented by atom zero of the
ambient standard coordinate presentation, and “inside a target copy” means
that its selected block is a union of target fibres.
-/

namespace SuccessorTree.NonPrecompact

/-- A finite pre-BANANA structure in standard atom coordinates. -/
structure PrebananaAtomStructure where
  atomCount : ℕ
  atomCount_pos : 0 < atomCount
  mark : Fin atomCount → F2
  total_mark_parity :
    (prebananaMarkedCount mark Finset.univ : F2) = 0

namespace PrebananaAtomStructure

/-- The canonical atom used only to orient unordered two-block copies. -/
def zeroAtom (A : PrebananaAtomStructure) : Fin A.atomCount :=
  ⟨0, A.atomCount_pos⟩

/-- The all-marked target with `2^(k+1)` atoms. -/
def allMarkedPower (k : ℕ) : PrebananaAtomStructure where
  atomCount := 2 ^ (k + 1)
  atomCount_pos := by positivity
  mark := fun _ => 1
  total_mark_parity := by
    have hEven : Even (2 ^ (k + 1)) :=
      even_two.pow_of_ne_zero (Nat.succ_ne_zero k)
    simpa [prebananaMarkedCount] using hEven.natCast_zmod_two

end PrebananaAtomStructure

/-- A unital pre-BANANA embedding in atom coordinates.

`part b = a` means that the target atom `b` lies below the image of
source atom `a`. -/
structure PrebananaAtomEmbedding
    (A B : PrebananaAtomStructure) where
  part : Fin B.atomCount → Fin A.atomCount
  fibre_nonempty :
    ∀ a, (prebananaFiber part a).Nonempty
  fibre_mark_parity :
    ∀ a,
      (prebananaMarkedCount B.mark (prebananaFiber part a) : F2) =
        A.mark a

namespace PrebananaAtomEmbedding

variable {A B : PrebananaAtomStructure}

/-- An embedding of the all-marked power-of-two target gives exactly the
partition object used by the persistent-colouring theorem. -/
def toAllMarkedTargetCopy
    (k : ℕ)
    (f :
      PrebananaAtomEmbedding
        (PrebananaAtomStructure.allMarkedPower k) B) :
    PrebananaAllMarkedTargetCopy
      (2 ^ (k + 1)) B.atomCount B.mark where
  part := f.part
  fibre_marked_odd := by
    intro j
    apply ZMod.natCast_eq_one_iff_odd.mp
    have h := f.fibre_mark_parity j
    simpa [PrebananaAtomStructure.allMarkedPower] using h

end PrebananaAtomEmbedding

/-- The actual copy-range type of the two-atom, both-marked source in a
standard-coordinate pre-BANANA structure. -/
abbrev PrebananaTwoMarkedCopy (A : PrebananaAtomStructure) :=
  PrebananaTwoAtomCopy A.mark A.zeroAtom

namespace PrebananaTwoAtomCopy

/-- A source copy lies inside the range of a target embedding exactly when
its canonically selected block is a union of target atom fibres. -/
def Inside
    {B C : PrebananaAtomStructure}
    (P : PrebananaTwoMarkedCopy C)
    (f : PrebananaAtomEmbedding B C) : Prop :=
  ∃ labels : Finset (Fin B.atomCount),
    P.block =
      Finset.univ.filter fun i => f.part i ∈ labels

end PrebananaTwoAtomCopy

/-- Copy Ramsey degree at most `t` for the two-marked-atom source, in the
standard atom-coordinate presentation of the pre-BANANA class. -/
def prebananaTwoMarkedCopyRamseyDegreeLE (t : ℕ) : Prop :=
  ∀ (B : PrebananaAtomStructure)
      (numColours : ℕ), 0 < numColours →
    ∃ C : PrebananaAtomStructure,
      ∀ colouring : PrebananaTwoMarkedCopy C → Fin numColours,
        ∃ f : PrebananaAtomEmbedding B C,
          ∃ colours : Finset (Fin numColours),
            colours.card ≤ t ∧
            ∀ P : PrebananaTwoMarkedCopy C,
              P.Inside f → colouring P ∈ colours

/-- The two-marked-atom source has infinite copy Ramsey degree. -/
def prebananaTwoMarkedCopyRamseyDegreeInfinite : Prop :=
  ∀ t : ℕ, ¬ prebananaTwoMarkedCopyRamseyDegreeLE t

/-- The persistent power-of-two colourings rule out every finite copy
Ramsey-degree bound. -/
theorem prebananaTwoMarkedCopyRamseyDegree_infinite :
    prebananaTwoMarkedCopyRamseyDegreeInfinite := by
  intro t hdegree
  let B := PrebananaAtomStructure.allMarkedPower t
  obtain ⟨C, hC⟩ :=
    hdegree B (2 ^ t) (by positivity)
  letI : NeZero C.atomCount :=
    ⟨Nat.ne_of_gt C.atomCount_pos⟩
  obtain ⟨colouring, hpersistent⟩ :=
    exists_prebananaPersistentColouring t C.mark
  obtain ⟨f, colours, hcard, hcolours⟩ :=
    hC colouring
  let T := f.toAllMarkedTargetCopy t

  have huniv : colours = Finset.univ := by
    ext colour
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨P, hPcolour, labels, hPblock⟩ :=
      hpersistent T colour
    have hinside : P.Inside f := by
      exact ⟨labels, hPblock⟩
    have hmem := hcolours P hinside
    rw [hPcolour] at hmem
    exact hmem

  have hle : 2 ^ t ≤ t := by
    rw [huniv] at hcard
    simpa using hcard
  exact (Nat.not_le_of_gt t.lt_two_pow_self) hle

end SuccessorTree.NonPrecompact

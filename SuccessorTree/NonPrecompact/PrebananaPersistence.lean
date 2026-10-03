import SuccessorTree.NonPrecompact.CopyRamseyDegree
import SuccessorTree.NonPrecompact.ColouringWrappers

/-!
# Persistent copy colourings for pre-BANANA

This file formalises the full quantifier order of the circulation theorem for
pre-BANANA, beyond the local subset-sum witness already proved in
`ColouringWrappers.lean`.

A finite Boolean algebra is represented by its finite atom set.  We use
standard coordinates `Fin n`; the marking predicate is a function
`mark : Fin n → F2`.  A unital embedding of the all-marked `q`-atom
target is exactly a partition of the ambient atom set into `q` nonempty
blocks whose marked-atom counts are odd.  The nonemptiness is automatic from
oddness.

For the two-marked-atom source, an unordered two-block copy is represented
canonically relative to one ambient atom `cstar`: we keep the unique block
containing `cstar`.  This is exactly the choice made in the manuscript to
define one ambient colouring; the target embedding need not preserve
`cstar`.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- Number of marked atoms in a finite set of atoms. -/
def prebananaMarkedCount
    {n : ℕ} (mark : Fin n → F2) (s : Finset (Fin n)) : ℕ :=
  (s.filter fun i => mark i = 1).card

/-- The fibre of one target atom under the atom-partition representation of
a Boolean-algebra embedding. -/
def prebananaFiber
    {q n : ℕ} (part : Fin n → Fin q) (j : Fin q) : Finset (Fin n) :=
  Finset.univ.filter fun i => part i = j

/-- Sum of the marked counts of selected fibres is the marked count of their
union. -/
theorem prebanana_sum_fiber_markedCount
    {q n : ℕ}
    (mark : Fin n → F2)
    (part : Fin n → Fin q)
    (labels : Finset (Fin q)) :
    (∑ j ∈ labels, prebananaMarkedCount mark (prebananaFiber part j)) =
      prebananaMarkedCount mark
        (Finset.univ.filter fun i => part i ∈ labels) := by
  classical
  let marked : Finset (Fin n) :=
    Finset.univ.filter fun i => mark i = 1
  calc
    (∑ j ∈ labels, prebananaMarkedCount mark (prebananaFiber part j)) =
        ∑ j ∈ labels, (marked.filter fun i => part i = j).card := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [prebananaMarkedCount, prebananaFiber, marked,
        Finset.filter_filter, and_left_comm, and_comm, and_assoc]
    _ = (marked.filter fun i => part i ∈ labels).card :=
      Finset.sum_card_fiberwise_eq_card_filter marked labels part
    _ = prebananaMarkedCount mark
          (Finset.univ.filter fun i => part i ∈ labels) := by
      simp [prebananaMarkedCount, marked, Finset.filter_filter,
        and_left_comm, and_comm, and_assoc]

/-- An all-marked `q`-atom pre-BANANA target copy inside an ambient
pre-BANANA atom structure.

The function `part` records to which source atom each ambient atom belongs.
Because pre-BANANA embeddings are unital, every ambient atom belongs to one
block.  Preservation of the marking says precisely that every fibre has an
odd number of marked ambient atoms. -/
structure PrebananaAllMarkedTargetCopy
    (q n : ℕ) (mark : Fin n → F2) where
  part : Fin n → Fin q
  fibre_marked_odd :
    ∀ j, Odd (prebananaMarkedCount mark (prebananaFiber part j))

/-- A copy of the two-atom, both-marked source, canonically oriented by one
ambient atom `cstar`.

An unordered two-block partition has exactly one block containing
`cstar`, so this is a faithful representation of copy-ranges rather than
of ordered embeddings. -/
structure PrebananaTwoAtomCopy
    {n : ℕ} (mark : Fin n → F2) (cstar : Fin n) where
  block : Finset (Fin n)
  cstar_mem : cstar ∈ block
  block_marked_odd : Odd (prebananaMarkedCount mark block)
  complement_marked_odd :
    Odd (prebananaMarkedCount mark (Finset.univ \ block))

namespace PrebananaTwoAtomCopy

variable {n : ℕ} {mark : Fin n → F2} {cstar : Fin n}

/-- The residue of the canonically selected block is an odd residue modulo
`2^(k+1)`. -/
noncomputable def residueColour
    (P : PrebananaTwoAtomCopy mark cstar) (k : ℕ) :
    ResidueParityColour k 1 := by
  refine ⟨
    (prebananaMarkedCount mark P.block :
      ZMod (2 ^ (k + 1))), ?_⟩
  simp only [BananaMatrixStructure.residueParityPalette,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [residueParityHom_natCast]
  exact P.block_marked_odd.natCast_zmod_two

/-- Enumerate odd residues by `Fin (2^k)`, matching the manuscript's
ordinary finite-colour convention. -/
noncomputable def residueFinColour
    (P : PrebananaTwoAtomCopy mark cstar) (k : ℕ) :
    Fin (2 ^ k) :=
  residueParityColourEquivFin k 1 (P.residueColour k)

end PrebananaTwoAtomCopy

/-- The full fixed-ambient persistent colouring for pre-BANANA.

For every ambient finite atom structure and every `k`, one atom `cstar`
and one `2^k`-colouring are fixed first.  Every embedded all-marked target
with `2^(k+1)` atoms then contains every colour. -/
theorem exists_prebananaPersistentColouring
    (k : ℕ) {n : ℕ} [NeZero n]
    (mark : Fin n → F2) :
    ∃ colouring :
        PrebananaTwoAtomCopy mark (0 : Fin n) → Fin (2 ^ k),
      ∀ T :
          PrebananaAllMarkedTargetCopy (2 ^ (k + 1)) n mark,
        ∀ colour : Fin (2 ^ k),
          ∃ P : PrebananaTwoAtomCopy mark (0 : Fin n),
            colouring P = colour := by
  classical
  let cstar : Fin n := 0
  let colouring :
      PrebananaTwoAtomCopy mark cstar → Fin (2 ^ k) :=
    fun P => P.residueFinColour k
  refine ⟨colouring, ?_⟩
  intro T colour

  let jstar : Fin (2 ^ (k + 1)) := T.part cstar
  let s : Finset (Fin (2 ^ (k + 1))) :=
    Finset.univ.erase jstar
  let a : Fin (2 ^ (k + 1)) → ℕ :=
    fun j => prebananaMarkedCount mark (prebananaFiber T.part j)

  have hcard : s.card + 1 = 2 ^ (k + 1) := by
    dsimp [s]
    rw [Finset.card_erase_add_one (Finset.mem_univ jstar)]
    simp

  have ha : ∀ j ∈ s, Odd (a j) := by
    intro j hj
    exact T.fibre_marked_odd j

  have hc : Odd (a jstar) :=
    T.fibre_marked_odd jstar

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

  obtain ⟨t, ht, hteven, hchosenCard, hdiffCard, hdiffNonempty,
      hchosenOdd, hcomplementOdd, hresidue⟩ :=
    prebanana_odd_residue_copy_witness
      (k := k + 1) (by omega)
      s a hcard ha (a jstar) z.1.val hc hzOdd

  have hjstar_not_mem_t : jstar ∉ t := by
    intro hj
    have hj' := ht hj
    exact (Finset.mem_erase.mp hj').1 rfl

  let labels : Finset (Fin (2 ^ (k + 1))) :=
    insert jstar t
  let block : Finset (Fin n) :=
    Finset.univ.filter fun i => T.part i ∈ labels

  have hblockCount :
      prebananaMarkedCount mark block =
        a jstar + ∑ j ∈ t, a j := by
    have hsum :=
      prebanana_sum_fiber_markedCount mark T.part labels
    rw [Finset.sum_insert hjstar_not_mem_t] at hsum
    simpa [block, labels, a] using hsum.symm

  have hremaining :
      Finset.univ \ labels = s \ t := by
    ext j
    simp [labels, s, and_left_comm, and_assoc]

  have hblockComplement :
      Finset.univ \ block =
        Finset.univ.filter
          (fun i => T.part i ∈ (Finset.univ \ labels)) := by
    ext i
    simp [block]

  have hcomplementCount :
      prebananaMarkedCount mark (Finset.univ \ block) =
        ∑ j ∈ s \ t, a j := by
    rw [hblockComplement, hremaining]
    have hsum :=
      prebanana_sum_fiber_markedCount mark T.part (s \ t)
    simpa [a] using hsum.symm

  have hcstar : cstar ∈ block := by
    simp [block, labels, jstar]

  let P : PrebananaTwoAtomCopy mark cstar := {
    block := block
    cstar_mem := hcstar
    block_marked_odd := by
      rw [hblockCount]
      exact hchosenOdd
    complement_marked_odd := by
      rw [hcomplementCount]
      exact hcomplementOdd
  }

  refine ⟨P, ?_⟩

  have hcolourResidue :
      (prebananaMarkedCount mark block :
        ZMod (2 ^ (k + 1))) = z.1 := by
    rw [hblockCount, Nat.cast_add, Nat.cast_sum]
    calc
      (a jstar : ZMod (2 ^ (k + 1))) +
          ∑ j ∈ t, (a j : ZMod (2 ^ (k + 1))) =
          (z.1.val : ZMod (2 ^ (k + 1))) := hresidue
      _ = z.1 := ZMod.natCast_zmod_val z.1

  have hsub : P.residueColour k = z := by
    apply Subtype.ext
    exact hcolourResidue

  change residueParityColourEquivFin k 1 (P.residueColour k) = colour
  rw [hsub]
  exact (residueParityColourEquivFin k 1).apply_symm_apply colour

end SuccessorTree.NonPrecompact

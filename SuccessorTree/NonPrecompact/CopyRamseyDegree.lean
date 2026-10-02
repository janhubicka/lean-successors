import SuccessorTree.NonPrecompact.CompletionPersistence

/-!
# Copy Ramsey degrees for the BANANA line-pair sources

The persistent-colouring files prove that, after fixing one completion of an
ambient BANANA structure, every embedded perfect target sees the full parity
palette.  This file supplies the abstract Ramsey-degree layer that turns that
finite statement into the manuscript's conclusion that the four-element
sources `A₀` and `A₁` have infinite copy Ramsey degree.

For a fixed pairing value `b`, a copy of `A_b` in a finite BANANA
structure is exactly a pair of nonzero vectors, one in each sort, whose
pairing is `b`.  Since `A_b` is rigid over `F₂`, this is the manuscript's
copy notion, not merely an embedding surrogate.

The definition of `linePairCopyRamseyDegreeLE` quantifies over arbitrary
finite colour types rather than `Fin r`.  This is equivalent to the usual
finite-colour formulation and avoids choosing an irrelevant enumeration of
the parity palette.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- A copy of the four-element source `A_b` inside an arbitrary finite
BANANA structure. -/
structure BananaLinePairCopy
    {l r : ℕ} (A : BananaMatrixStructure l r) (b : F2) where
  left : Fin l → F2
  right : Fin r → F2
  left_ne_zero : left ≠ 0
  right_ne_zero : right ≠ 0
  pairing : A.eval left right = b

namespace BananaMatrixEmbedding

variable {l r l' r' : ℕ}
variable {A : BananaMatrixStructure l r}
variable {B : BananaMatrixStructure l' r'}

/-- A BANANA embedding sends a line-pair copy to a line-pair copy. -/
def mapLinePairCopy
    {b : F2}
    (f : BananaMatrixEmbedding A B)
    (P : BananaLinePairCopy A b) :
    BananaLinePairCopy B b where
  left := f.left P.left
  right := f.right P.right
  left_ne_zero := by
    intro h
    apply P.left_ne_zero
    apply f.left_injective
    simpa using h
  right_ne_zero := by
    intro h
    apply P.right_ne_zero
    apply f.right_injective
    simpa using h
  pairing := (f.pairing_apply P.left P.right).trans P.pairing

@[simp] theorem mapLinePairCopy_left
    {b : F2}
    (f : BananaMatrixEmbedding A B)
    (P : BananaLinePairCopy A b) :
    (f.mapLinePairCopy P).left = f.left P.left := rfl

@[simp] theorem mapLinePairCopy_right
    {b : F2}
    (f : BananaMatrixEmbedding A B)
    (P : BananaLinePairCopy A b) :
    (f.mapLinePairCopy P).right = f.right P.right := rfl

end BananaMatrixEmbedding

namespace LinePairCopy

/-- The perfect-pair line-copy representation is the arbitrary-BANANA
line-copy representation specialised to the standard perfect pairing. -/
def toBananaLinePairCopy
    {d : ℕ} {b : F2}
    (P : LinePairCopy d b) :
    BananaLinePairCopy (perfectBanana d) b where
  left := P.left
  right := P.right
  left_ne_zero := P.left_ne_zero
  right_ne_zero := P.right_ne_zero
  pairing := by
    simpa only [perfectBanana_eval] using P.pairing

@[simp] theorem toBananaLinePairCopy_left
    {d : ℕ} {b : F2}
    (P : LinePairCopy d b) :
    P.toBananaLinePairCopy.left = P.left := rfl

@[simp] theorem toBananaLinePairCopy_right
    {d : ℕ} {b : F2}
    (P : LinePairCopy d b) :
    P.toBananaLinePairCopy.right = P.right := rfl

end LinePairCopy

/-- The finite colour type consisting of exactly those residues whose parity
is the source pairing value `b`. -/
abbrev ResidueParityColour (k : ℕ) (b : F2) :=
  ↥(BananaMatrixStructure.residueParityPalette k b)

/-- The parity palette has exactly `2^k` elements. -/
theorem residueParityColour_card (k : ℕ) (b : F2) :
    Fintype.card (ResidueParityColour k b) = 2 ^ k := by
  simpa using BananaMatrixStructure.residueParityPalette_card k b

/-- Reduction of a natural-number residue modulo `2^(k+1)` and then modulo
two agrees with direct reduction modulo two. -/
theorem residueParityHom_natCast (k n : ℕ) :
    residueParityHom k (n : ZMod (2 ^ (k + 1))) = (n : F2) := by
  simp [residueParityHom]

namespace BananaLinePairCopy

variable {l r : ℕ}
variable {A : BananaMatrixStructure l r}
variable {b : F2}

/-- The fixed-completion residue colouring of a line-pair copy.  The subtype
proof records that its residue automatically has the prescribed parity. -/
noncomputable def completionResidueColour
    (P : BananaLinePairCopy A b) (k : ℕ) :
    ResidueParityColour k b := by
  refine ⟨
    (A.completionIntersectionCount P.left P.right :
      ZMod (2 ^ (k + 1))), ?_⟩
  simp only [BananaMatrixStructure.residueParityPalette,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [residueParityHom_natCast]
  exact
    (A.completionIntersectionCount_parity P.left P.right).trans P.pairing

end BananaLinePairCopy

/-- The copy Ramsey degree of the rigid line-pair source `A_b` is at most
`t`.

A target copy is represented by a BANANA embedding `f : B → C`.  The last
line says that all colours on source copies lying inside that target range
belong to one finite set of size at most `t`. -/
def linePairCopyRamseyDegreeLE (b : F2) (t : ℕ) : Prop :=
  ∀ (lB rB : ℕ) (B : BananaMatrixStructure lB rB)
      (ι : Type) [Fintype ι] [DecidableEq ι],
    ∃ (lC rC : ℕ) (C : BananaMatrixStructure lC rC),
      ∀ colouring : BananaLinePairCopy C b → ι,
        ∃ f : BananaMatrixEmbedding B C,
          ∃ colours : Finset ι,
            colours.card ≤ t ∧
            ∀ P : BananaLinePairCopy B b,
              colouring (f.mapLinePairCopy P) ∈ colours

/-- The line-pair source has infinite copy Ramsey degree if it admits no
finite degree bound. -/
def linePairCopyRamseyDegreeInfinite (b : F2) : Prop :=
  ∀ t : ℕ, ¬ linePairCopyRamseyDegreeLE b t

/-- If `t < 2^k`, the persistent parity palette rules out copy Ramsey
degree at most `t`. -/
theorem not_linePairCopyRamseyDegreeLE_of_lt_pow
    (k t : ℕ) (b : F2) (ht : t < 2 ^ k) :
    ¬ linePairCopyRamseyDegreeLE b t := by
  intro hdegree
  obtain ⟨lC, rC, C, hC⟩ :=
    hdegree
      ((2 ^ (k + 1) - 1) + 1)
      ((2 ^ (k + 1) - 1) + 1)
      (perfectBanana ((2 ^ (k + 1) - 1) + 1))
      (ResidueParityColour k b)
  let colouring :
      BananaLinePairCopy C b → ResidueParityColour k b :=
    fun P => P.completionResidueColour k
  obtain ⟨f, colours, hcard, hcolours⟩ := hC colouring
  have huniv : colours = Finset.univ := by
    ext z
    simp only [Finset.mem_univ, iff_true]
    have hz : residueParityHom k z.1 = b :=
      (Finset.mem_filter.mp z.2).2
    obtain ⟨P, hP⟩ :=
      C.completionIntersectionColours_cover_parity k b f z.1 hz
    let P' :
        BananaLinePairCopy
          (perfectBanana ((2 ^ (k + 1) - 1) + 1)) b :=
      P.toBananaLinePairCopy
    have hmem := hcolours P'
    have hcolour : colouring (f.mapLinePairCopy P') = z := by
      apply Subtype.ext
      simpa [colouring, BananaLinePairCopy.completionResidueColour, P'] using hP
    rw [hcolour] at hmem
    exact hmem
  have hle : 2 ^ k ≤ t := by
    rw [huniv] at hcard
    simpa only [Finset.card_univ, residueParityColour_card] using hcard
  exact (Nat.not_le_of_gt ht) hle

private theorem nat_lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      calc
        n + 1 < 2 ^ n + 1 := by omega
        _ ≤ 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by ring

/-- Both four-element BANANA sources have infinite copy Ramsey degree.  The
argument is uniform in the pairing value `b`. -/
theorem linePairCopyRamseyDegree_infinite (b : F2) :
    linePairCopyRamseyDegreeInfinite b := by
  intro t
  exact not_linePairCopyRamseyDegreeLE_of_lt_pow
    t t b (nat_lt_two_pow t)

end SuccessorTree.NonPrecompact

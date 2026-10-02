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

The Ramsey-degree definition below deliberately uses colourings into
`Fin r`, with `r > 0`, exactly as in the circulation manuscript.
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
  change
    Fintype.card ↥(BananaMatrixStructure.residueParityPalette k b) =
      2 ^ k
  rw [Fintype.card_coe]
  exact BananaMatrixStructure.residueParityPalette_card k b

/-- A fixed enumeration of the parity-`b` palette by the manuscript's
ordinary colour type `Fin (2^k)`. -/
noncomputable def residueParityColourEquivFin (k : ℕ) (b : F2) :
    ResidueParityColour k b ≃ Fin (2 ^ k) :=
  Fintype.equivFinOfCardEq (residueParityColour_card k b)

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

/-- The same colouring, enumerated by `Fin (2^k)` to match the Ramsey-degree
definition used in the manuscript. -/
noncomputable def completionResidueFinColour
    (P : BananaLinePairCopy A b) (k : ℕ) :
    Fin (2 ^ k) :=
  residueParityColourEquivFin k b (P.completionResidueColour k)

end BananaLinePairCopy

/-- The fixed ambient completion gives a `2^k`-colouring for which every
embedded perfect target of dimension `2^(k+1)` sees every colour.

This is the finite persistent-colouring assertion in the manuscript with
`q = 2^(k+1)`. -/
theorem exists_completionResiduePersistentColouring
    {l r : ℕ}
    (A : BananaMatrixStructure l r)
    (k : ℕ) (b : F2) :
    ∃ colouring : BananaLinePairCopy A b → Fin (2 ^ k),
      ∀ f :
          BananaMatrixEmbedding
            (perfectBanana ((2 ^ (k + 1) - 1) + 1)) A,
        ∀ c : Fin (2 ^ k),
          ∃ P :
              BananaLinePairCopy
                (perfectBanana ((2 ^ (k + 1) - 1) + 1)) b,
            colouring (f.mapLinePairCopy P) = c := by
  let colouring : BananaLinePairCopy A b → Fin (2 ^ k) :=
    fun P => P.completionResidueFinColour k
  refine ⟨colouring, ?_⟩
  intro f c
  let z : ResidueParityColour k b :=
    (residueParityColourEquivFin k b).symm c
  have hz : residueParityHom k z.1 = b :=
    (Finset.mem_filter.mp z.2).2
  obtain ⟨P, hP⟩ :=
    A.completionIntersectionColours_cover_parity k b f z.1 hz
  let P' :
      BananaLinePairCopy
        (perfectBanana ((2 ^ (k + 1) - 1) + 1)) b :=
    P.toBananaLinePairCopy
  refine ⟨P', ?_⟩
  have hsub :
      (f.mapLinePairCopy P').completionResidueColour k = z := by
    apply Subtype.ext
    simpa [BananaLinePairCopy.completionResidueColour, P'] using hP
  change
    residueParityColourEquivFin k b
      ((f.mapLinePairCopy P').completionResidueColour k) = c
  rw [hsub]
  simpa [z] using (residueParityColourEquivFin k b).apply_symm_apply c

/-- Every parity-one residue is already forced by a perfect target of
dimension `2^(k+1)-1`. -/
theorem completionIntersectionColours_cover_one_sharp
    {l r : ℕ}
    (A : BananaMatrixStructure l r)
    (k : ℕ)
    (f :
      BananaMatrixEmbedding
        (perfectBanana (2 ^ (k + 1) - 1)) A) :
    ∀ z : ZMod (2 ^ (k + 1)),
      residueParityHom k z = 1 →
      ∃ P : LinePairCopy (2 ^ (k + 1) - 1) 1,
        (A.completionIntersectionCount
            (f.left P.left) (f.right P.right) :
          ZMod (2 ^ (k + 1))) = z := by
  intro z hz
  have hval : (z.val : F2) = 1 := by
    calc
      (z.val : F2) =
          residueParityHom k
            (z.val : ZMod (2 ^ (k + 1))) :=
        (residueParityHom_natCast k z.val).symm
      _ = residueParityHom k z := by
        rw [ZMod.natCast_zmod_val]
      _ = 1 := hz
  have hodd : Odd z.val :=
    ZMod.natCast_eq_one_iff_odd.mp hval
  obtain ⟨P, hP⟩ :=
    A.exists_pairingOne_completionIntersectionColour
      k f z.val hodd
  refine ⟨P, ?_⟩
  simpa only [ZMod.natCast_zmod_val] using hP

/-- Sharper persistent colouring for the pairing-one source: the same
`2^k` colours are already all present in every perfect target of dimension
`2^(k+1)-1`. -/
theorem exists_pairingOne_completionResiduePersistentColouring
    {l r : ℕ}
    (A : BananaMatrixStructure l r)
    (k : ℕ) :
    ∃ colouring : BananaLinePairCopy A 1 → Fin (2 ^ k),
      ∀ f :
          BananaMatrixEmbedding
            (perfectBanana (2 ^ (k + 1) - 1)) A,
        ∀ c : Fin (2 ^ k),
          ∃ P :
              BananaLinePairCopy
                (perfectBanana (2 ^ (k + 1) - 1)) 1,
            colouring (f.mapLinePairCopy P) = c := by
  let colouring : BananaLinePairCopy A 1 → Fin (2 ^ k) :=
    fun P => P.completionResidueFinColour k
  refine ⟨colouring, ?_⟩
  intro f c
  let z : ResidueParityColour k 1 :=
    (residueParityColourEquivFin k 1).symm c
  have hz : residueParityHom k z.1 = 1 :=
    (Finset.mem_filter.mp z.2).2
  obtain ⟨P, hP⟩ :=
    completionIntersectionColours_cover_one_sharp A k f z.1 hz
  let P' :
      BananaLinePairCopy
        (perfectBanana (2 ^ (k + 1) - 1)) 1 :=
    P.toBananaLinePairCopy
  refine ⟨P', ?_⟩
  have hsub :
      (f.mapLinePairCopy P').completionResidueColour k = z := by
    apply Subtype.ext
    simpa [BananaLinePairCopy.completionResidueColour, P'] using hP
  change
    residueParityColourEquivFin k 1
      ((f.mapLinePairCopy P').completionResidueColour k) = c
  rw [hsub]
  simpa [z] using (residueParityColourEquivFin k 1).apply_symm_apply c

/-- The copy Ramsey degree of the rigid line-pair source `A_b` is at most
`t`, stated with exactly the finite-colour convention from the manuscript.

A target copy is represented by a BANANA embedding `f : B → C`.  The last
line says that all colours on source copies lying inside that target range
belong to one finite set of size at most `t`. -/
def linePairCopyRamseyDegreeLE (b : F2) (t : ℕ) : Prop :=
  ∀ (lB rB : ℕ) (B : BananaMatrixStructure lB rB)
      (numColours : ℕ), 0 < numColours →
    ∃ (lC rC : ℕ) (C : BananaMatrixStructure lC rC),
      ∀ colouring : BananaLinePairCopy C b → Fin numColours,
        ∃ f : BananaMatrixEmbedding B C,
          ∃ colours : Finset (Fin numColours),
            colours.card ≤ t ∧
            ∀ P : BananaLinePairCopy B b,
              colouring (f.mapLinePairCopy P) ∈ colours

/-- The line-pair source has infinite copy Ramsey degree if it admits no
finite degree bound. -/
def linePairCopyRamseyDegreeInfinite (b : F2) : Prop :=
  ∀ t : ℕ, ¬ linePairCopyRamseyDegreeLE b t

/-- If `t < 2^k`, the persistent `2^k`-colouring rules out copy Ramsey
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
      (2 ^ k) (by positivity)
  obtain ⟨colouring, hpersistent⟩ :=
    exists_completionResiduePersistentColouring C k b
  obtain ⟨f, colours, hcard, hcolours⟩ := hC colouring
  have huniv : colours = Finset.univ := by
    ext c
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨P, hP⟩ := hpersistent f c
    have hmem := hcolours P
    rw [hP] at hmem
    exact hmem
  have hle : 2 ^ k ≤ t := by
    rw [huniv] at hcard
    simpa using hcard
  exact (Nat.not_le_of_gt ht) hle

private theorem nat_lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      calc
        n + 1 < 2 ^ n + 1 := by omega
        _ ≤ 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by
          rw [pow_succ]
          omega

/-- Both four-element BANANA sources have infinite copy Ramsey degree.  The
argument is uniform in the pairing value `b`. -/
theorem linePairCopyRamseyDegree_infinite (b : F2) :
    linePairCopyRamseyDegreeInfinite b := by
  intro t
  exact not_linePairCopyRamseyDegreeLE_of_lt_pow
    t t b (nat_lt_two_pow t)

end SuccessorTree.NonPrecompact

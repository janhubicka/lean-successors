import SuccessorTree.V10.AdmissibleKptLevelTree
import Mathlib.Tactic

/-!
# Canonical representation of binary diagonal and off-diagonal data

The finite Boolean-vector presentation uses a directed binary table
B on ordered pairs of distinct vertices and a separate unary-like
table D to encode the diagonal instances of binary relations.
Its induced-copy predicate checks B only for distinct vertices,
and checks D separately on every vertex.

Until now B(x,x) was left as an unused Boolean value. That creates
spurious distinct raw type records and prevents literal comparison
with the paper's ordinary relational language.

The canonical normalization sets every unused B(x,x) bit to false.
We prove that this changes no induced ordered copy, no forbidden
age condition and no auxiliary E relation. The original binary
loops remain in the separate D table. The resulting induced
L+ types have a canonical off-diagonal representation.

The identification of D's coordinates with the loops of the
original binary symbols and of uniformly fixed nullary symbols
remains an explicit *language-coding* obligation; it is not a
new axiom or a statement that the two signatures already coincide.
-/

namespace SuccessorTree.V10

/-- Forget unused self-pair values in the off-diagonal B table.
True diagonal binary atoms are encoded by A.diagonal. -/
def AgeTestModel.canonicalBinary
    {db du dd : Nat}
    (A : AgeTestModel db du dd) : AgeTestModel db du dd :=
  { carrier := A.carrier
    binary := fun x y r => if x = y then false else A.binary x y r
    unary := A.unary
    diagonal := A.diagonal }

/-- The canonical off-diagonal table has no self-pair facts. -/
@[simp] theorem AgeTestModel.canonicalBinary_self
    {db du dd : Nat}
    (A : AgeTestModel db du dd)
    (v : Nat) (r : Fin db) :
    A.canonicalBinary.binary v v r = false := by
  simp [AgeTestModel.canonicalBinary]

/-- All ordered off-diagonal bits, including negative facts and
both directed orientations, are unchanged by normalization. -/
theorem AgeTestModel.canonicalBinary_offdiagonal
    {db du dd : Nat}
    (A : AgeTestModel db du dd)
    (x y : Nat) (hxy : x ≠ y) (r : Fin db) :
    A.canonicalBinary.binary x y r = A.binary x y r := by
  simp [AgeTestModel.canonicalBinary, hxy]

/-- Normalization is idempotent. -/
theorem AgeTestModel.canonicalBinary_idempotent
    {db du dd : Nat}
    (A : AgeTestModel db du dd) :
    A.canonicalBinary.canonicalBinary = A.canonicalBinary := by
  cases A with
  | mk carrier B U D =>
    simp only [AgeTestModel.canonicalBinary]
    congr 1
    funext x y r
    by_cases h : x = y <;> simp [h]

/-- Induced ordered embeddings are identical before and after
normalization: distinct vertices only use B's off-diagonal data,
and singletons only use the unchanged unary/diagonal channels. -/
theorem AgeTestModel.realizes_canonicalBinary_iff
    {r db du dd : Nat}
    (A : AgeTestModel db du dd)
    (F : ForbiddenAtomicPattern r db du dd)
    (f : Fin r → Nat) :
    A.canonicalBinary.Realizes F f ↔ A.Realizes F f := by
  constructor
  · rintro ⟨hMono, hDomain, hB, hU, hD⟩
    refine ⟨hMono, hDomain, ?_, hU, hD⟩
    intro a b hab t
    have hDistinct : f a ≠ f b := fun heq => hab (hMono.injective heq)
    simpa [AgeTestModel.canonicalBinary, hDistinct]
      using hB a b hab t
  · rintro ⟨hMono, hDomain, hB, hU, hD⟩
    refine ⟨hMono, hDomain, ?_, hU, hD⟩
    intro a b hab t
    have hDistinct : f a ≠ f b := fun heq => hab (hMono.injective heq)
    simpa [AgeTestModel.canonicalBinary, hDistinct]
      using hB a b hab t

/-- Normalize the L-reduct of a finite enumerated partial structure,
leaving its E relation and every other structural datum unchanged. -/
def EnumeratedPartialStructure.canonicalBinary
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd) :
    EnumeratedPartialStructure db du dd := by
  refine
    { size := A.size
      L := A.L.canonicalBinary
      carrier_iff := ?_
      E := A.E
      E_inside := A.E_inside
      spaced := A.spaced
      downward := A.downward
      linked_E := ?_ }
  · exact A.carrier_iff
  · intro u v huv hu hv hLink
    have hne : u ≠ v := ne_of_lt huv
    have hne' : v ≠ u := hne.symm
    obtain ⟨t, hRel⟩ := hLink
    have hOriginal :
        ∃ t : Fin db,
          A.L.binary u v t = true ∨ A.L.binary v u t = true := by
      refine ⟨t, ?_⟩
      simpa [AgeTestModel.canonicalBinary, hne, hne']
        using hRel
    exact A.linked_E u v huv hu hv hOriginal

/-- The auxiliary E relation is literally unchanged. -/
@[simp] theorem EnumeratedPartialStructure.canonicalBinary_E
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (u v : Nat) :
    A.canonicalBinary.E u v = A.E u v := rfl

/-- The determined E-free level is unchanged by normalization. -/
@[simp] theorem EnumeratedPartialStructure.canonicalBinary_freeLevel
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) :
    A.canonicalBinary.freeLevel v = A.freeLevel v := rfl

/-- An induced type extracted from the canonical L-reduct has no
spurious self-pair B-bit, even at the distinguished type vertex.
The D table continues to encode its genuine diagonal L-facts. -/
theorem EnumeratedPartialStructure.canonicalBinary_type_diagonal
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (cut v : Nat)
    (x : Option (Fin cut)) (r : Fin db) :
    (A.canonicalBinary.partialTypeAt cut v).lReduct.binary x x r =
      false := by
  change (A.L.canonicalBinary).binary
      (prefixVertexIndex v x) (prefixVertexIndex v x) r = false
  exact AgeTestModel.canonicalBinary_self A.L (prefixVertexIndex v x) r

/-- Every forbidden pattern in the normalized family is avoided
by A iff it is avoided by the canonical off-diagonal L-reduct. -/
theorem NormalizedForbidden.avoids_canonicalBinary_iff
    {db du dd : Nat}
    (bad : NormalizedForbidden db du dd)
    (A : AgeTestModel db du dd) :
    bad.Avoids A.canonicalBinary ↔ bad.Avoids A := by
  cases bad with
  | singleton F hN =>
      simp only [NormalizedForbidden.Avoids]
      simp_rw [AgeTestModel.realizes_canonicalBinary_iff]
  | nontrivial r F hr hIrred =>
      simp only [NormalizedForbidden.Avoids]
      simp_rw [AgeTestModel.realizes_canonicalBinary_iff]

end SuccessorTree.V10

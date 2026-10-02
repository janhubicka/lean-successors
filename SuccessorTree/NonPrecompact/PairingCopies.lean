import SuccessorTree.NonPrecompact.PerfectCopy

/-!
# Abstract perfect-pair copies for the BANANA colouring obstruction

The matrix formalisation is convenient for proving the residue theorem, but
the Ramsey statement is about copies of finite structures.  This file packages
the source line pairs and target perfect-pair embeddings independently of a
chosen matrix representation.

A perfect-pair embedding consists of injective linear maps on the two sorts
which preserve the standard dot-product pairing.  Every
`PerfectCopyMatrices` gives such an embedding.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- A copy of the four-element source `A_b` inside the perfect pairing of
dimension `d`: two nonzero vectors with prescribed pairing `b`. -/
structure LinePairCopy (d : ℕ) (b : F2) where
  left : Fin d → F2
  right : Fin d → F2
  left_ne_zero : left ≠ 0
  right_ne_zero : right ≠ 0
  pairing : left ⬝ᵥ right = b

/-- An embedding of the perfect pairing `B_d` into `B_n`. -/
structure PerfectPairEmbedding (d n : ℕ) where
  left : (Fin d → F2) →ₗ[F2] (Fin n → F2)
  right : (Fin d → F2) →ₗ[F2] (Fin n → F2)
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  pairing_apply :
    ∀ x y : Fin d → F2, left x ⬝ᵥ right y = x ⬝ᵥ y

namespace PerfectPairEmbedding

variable {d n : ℕ} (E : PerfectPairEmbedding d n)

/-- An embedding of perfect pairs sends an `A_b`-copy to an
`A_b`-copy. -/
def mapLinePair {b : F2} (A : LinePairCopy d b) : LinePairCopy n b where
  left := E.left A.left
  right := E.right A.right
  left_ne_zero := by
    intro h
    apply A.left_ne_zero
    apply E.left_injective
    simpa using h
  right_ne_zero := by
    intro h
    apply A.right_ne_zero
    apply E.right_injective
    simpa using h
  pairing := (E.pairing_apply A.left A.right).trans A.pairing

@[simp] theorem mapLinePair_left {b : F2} (A : LinePairCopy d b) :
    (E.mapLinePair A).left = E.left A.left := rfl

@[simp] theorem mapLinePair_right {b : F2} (A : LinePairCopy d b) :
    (E.mapLinePair A).right = E.right A.right := rfl

end PerfectPairEmbedding

namespace PerfectCopyMatrices

variable {d n : ℕ} (E : PerfectCopyMatrices d n)

/-- Forget the coordinate matrices and retain only the induced structure
embedding. -/
def toPerfectPairEmbedding : PerfectPairEmbedding d n where
  left := E.leftMap
  right := E.rightMap
  left_injective := E.leftMap_injective
  right_injective := E.rightMap_injective
  pairing_apply := E.pairing_apply

@[simp] theorem toPerfectPairEmbedding_left (x : Fin d → F2) :
    E.toPerfectPairEmbedding.left x = E.leftMap x := rfl

@[simp] theorem toPerfectPairEmbedding_right (y : Fin d → F2) :
    E.toPerfectPairEmbedding.right y = E.rightMap y := rfl

/-- Structure-level form of the full BANANA persistent-colouring witness.

For every residue, a coordinate target copy of `B_q` contains an
`A_b`-copy, where `b` is the residue parity, whose ambient
support-intersection colour is exactly that residue. -/
theorem exists_embedded_linePair_intersectionColour
    (k : ℕ)
    (E : PerfectCopyMatrices ((2 ^ (k + 1) - 1) + 1) n)
    (r : ZMod (2 ^ (k + 1))) :
    ∃ A : LinePairCopy ((2 ^ (k + 1) - 1) + 1) (residueParityHom k r),
      (ambientIntersectionCount
          (E.toPerfectPairEmbedding.mapLinePair A).left
          (E.toPerfectPairEmbedding.mapLinePair A).right :
        ZMod (2 ^ (k + 1))) = r := by
  obtain ⟨x, y, hline, hcolour⟩ := E.exists_intersectionColour k r
  let A : LinePairCopy ((2 ^ (k + 1) - 1) + 1) (residueParityHom k r) := {
    left := x
    right := y
    left_ne_zero := hline.1
    right_ne_zero := hline.2.1
    pairing := hline.2.2
  }
  refine ⟨A, ?_⟩
  change
    (ambientIntersectionCount (E.leftMap x) (E.rightMap y) :
      ZMod (2 ^ (k + 1))) = r
  rw [← E.intersectionCount_eq_ambientIntersectionCount x y]
  exact hcolour

/-- Structure-level form of the sharper pairing-one obstruction: the
`B_{q-1}` target already contains every odd colour. -/
theorem exists_embedded_pairingOne_intersectionColour
    (k : ℕ)
    (E : PerfectCopyMatrices (2 ^ (k + 1) - 1) n)
    (r : ℕ) (hr : Odd r) :
    ∃ A : LinePairCopy (2 ^ (k + 1) - 1) 1,
      (ambientIntersectionCount
          (E.toPerfectPairEmbedding.mapLinePair A).left
          (E.toPerfectPairEmbedding.mapLinePair A).right :
        ZMod (2 ^ (k + 1))) =
        (r : ZMod (2 ^ (k + 1))) := by
  obtain ⟨x, y, hline, hcolour⟩ :=
    E.exists_pairingOne_intersectionColour k r hr
  let A : LinePairCopy (2 ^ (k + 1) - 1) 1 := {
    left := x
    right := y
    left_ne_zero := hline.1
    right_ne_zero := hline.2.1
    pairing := hline.2.2
  }
  refine ⟨A, ?_⟩
  change
    (ambientIntersectionCount (E.leftMap x) (E.rightMap y) :
      ZMod (2 ^ (k + 1))) =
        (r : ZMod (2 ^ (k + 1)))
  rw [← E.intersectionCount_eq_ambientIntersectionCount x y]
  exact hcolour

end PerfectCopyMatrices

end SuccessorTree.NonPrecompact

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

/-- The binary relation of the BANANA language on a standard perfect
pairing: an edge means that the pairing is one. -/
def pairingEdge {d : ℕ} (x y : Fin d → F2) : Prop :=
  x ⬝ᵥ y = 1

namespace PerfectPairEmbedding

variable {d n : ℕ} (E : PerfectPairEmbedding d n)

/-- The linear maps preserve the named zero constants. -/
@[simp] theorem left_zero : E.left 0 = 0 := by
  exact E.left.map_zero

@[simp] theorem right_zero : E.right 0 = 0 := by
  exact E.right.map_zero

/-- The linear maps preserve the addition functions in the two sorts. -/
@[simp] theorem left_add (x y : Fin d → F2) :
    E.left (x + y) = E.left x + E.left y := by
  exact E.left.map_add x y

@[simp] theorem right_add (x y : Fin d → F2) :
    E.right (x + y) = E.right x + E.right y := by
  exact E.right.map_add x y

/-- Pairing preservation is exactly preservation and reflection of the
binary relation `E(x,y) ↔ β(x,y)=1` from the BANANA language. -/
theorem pairingEdge_iff (x y : Fin d → F2) :
    pairingEdge (E.left x) (E.right y) ↔ pairingEdge x y := by
  unfold pairingEdge
  rw [E.pairing_apply x y]

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

/-- Recover the standard coordinate matrices of an arbitrary embedding of
perfect pairs.  This is the converse direction to
`PerfectCopyMatrices.toPerfectPairEmbedding`. -/
noncomputable def toPerfectCopyMatrices : PerfectCopyMatrices d n where
  left := (LinearMap.toMatrix' E.left)ᵀ
  right := (LinearMap.toMatrix' E.right)ᵀ
  pairing := by
    ext i j
    have h :=
      E.pairing_apply (Pi.single i (1 : F2)) (Pi.single j (1 : F2))
    simpa [Matrix.mul_apply, LinearMap.toMatrix'_apply,
      Matrix.one_apply, single_dotProduct, Pi.single_apply] using h

@[simp] theorem toPerfectCopyMatrices_leftMap_apply
    (x : Fin d → F2) :
    E.toPerfectCopyMatrices.leftMap x = E.left x := by
  simp [toPerfectCopyMatrices, PerfectCopyMatrices.leftMap]

@[simp] theorem toPerfectCopyMatrices_rightMap_apply
    (y : Fin d → F2) :
    E.toPerfectCopyMatrices.rightMap y = E.right y := by
  simp [toPerfectCopyMatrices, PerfectCopyMatrices.rightMap]

/-- Arbitrary-embedding form of the full BANANA persistent-colouring
witness.  No coordinate-matrix presentation of the target embedding is
assumed by the caller. -/
theorem exists_linePair_intersectionColour
    (k : ℕ)
    (E :
      PerfectPairEmbedding ((2 ^ (k + 1) - 1) + 1) n)
    (r : ZMod (2 ^ (k + 1))) :
    ∃ A : LinePairCopy ((2 ^ (k + 1) - 1) + 1) (residueParityHom k r),
      (PerfectCopyMatrices.ambientIntersectionCount
          (E.mapLinePair A).left
          (E.mapLinePair A).right :
        ZMod (2 ^ (k + 1))) = r := by
  let M := E.toPerfectCopyMatrices
  obtain ⟨x, y, hline, hcolour⟩ := M.exists_intersectionColour k r
  let A : LinePairCopy
      ((2 ^ (k + 1) - 1) + 1) (residueParityHom k r) := {
    left := x
    right := y
    left_ne_zero := hline.1
    right_ne_zero := hline.2.1
    pairing := hline.2.2
  }
  refine ⟨A, ?_⟩
  rw [M.intersectionCount_eq_ambientIntersectionCount x y] at hcolour
  simpa [A, M] using hcolour

/-- Arbitrary-embedding form of the sharper pairing-one obstruction:
the target of dimension `q-1` already sees every odd residue. -/
theorem exists_pairingOne_intersectionColour
    (k : ℕ)
    (E : PerfectPairEmbedding (2 ^ (k + 1) - 1) n)
    (r : ℕ) (hr : Odd r) :
    ∃ A : LinePairCopy (2 ^ (k + 1) - 1) 1,
      (PerfectCopyMatrices.ambientIntersectionCount
          (E.mapLinePair A).left
          (E.mapLinePair A).right :
        ZMod (2 ^ (k + 1))) =
          (r : ZMod (2 ^ (k + 1))) := by
  let M := E.toPerfectCopyMatrices
  obtain ⟨x, y, hline, hcolour⟩ :=
    M.exists_pairingOne_intersectionColour k r hr
  let A : LinePairCopy (2 ^ (k + 1) - 1) 1 := {
    left := x
    right := y
    left_ne_zero := hline.1
    right_ne_zero := hline.2.1
    pairing := hline.2.2
  }
  refine ⟨A, ?_⟩
  rw [M.intersectionCount_eq_ambientIntersectionCount x y] at hcolour
  simpa [A, M] using hcolour

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

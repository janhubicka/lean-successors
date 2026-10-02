import SuccessorTree.NonPrecompact.Completion

/-!
# Persistent colours through a fixed BANANA completion

The manuscript first fixes one coordinate realisation of the ambient
BANANA structure and then colours line-pair copies by ordinary support
intersection size modulo a power of two.  The quantifier order matters:
the coordinate realisation must not depend on the later target copy.

Here the fixed coordinate realisation is the explicit completion from
`Completion.lean`.  Any embedding of a standard perfect target is
composed with that completion, producing a `PerfectPairEmbedding`.
The arbitrary-embedding persistence theorem from `PairingCopies.lean`
then supplies every required residue inside the target copy.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

namespace BananaMatrixEmbedding

variable {l r l' r' l'' r'' : ℕ}
variable {A : BananaMatrixStructure l r}
variable {B : BananaMatrixStructure l' r'}
variable {C : BananaMatrixStructure l'' r''}

@[simp] theorem comp_left_apply
    (g : BananaMatrixEmbedding B C)
    (f : BananaMatrixEmbedding A B)
    (x : Fin l → F2) :
    (comp g f).left x = g.left (f.left x) := rfl

@[simp] theorem comp_right_apply
    (g : BananaMatrixEmbedding B C)
    (f : BananaMatrixEmbedding A B)
    (y : Fin r → F2) :
    (comp g f).right y = g.right (f.right y) := rfl

@[simp] theorem toPerfectPairEmbedding_left_apply
    {d n : ℕ}
    (f : BananaMatrixEmbedding (perfectBanana d) (perfectBanana n))
    (x : Fin d → F2) :
    f.toPerfectPairEmbedding.left x = f.left x := rfl

@[simp] theorem toPerfectPairEmbedding_right_apply
    {d n : ℕ}
    (f : BananaMatrixEmbedding (perfectBanana d) (perfectBanana n))
    (y : Fin d → F2) :
    f.toPerfectPairEmbedding.right y = f.right y := rfl

end BananaMatrixEmbedding

namespace BananaMatrixStructure

variable {l r : ℕ} (A : BananaMatrixStructure l r)

/-- The palette of residues whose parity is the fixed source pairing `b`. -/
def residueParityPalette (k : ℕ) (b : F2) :
    Finset (ZMod (2 ^ (k + 1))) :=
  Finset.univ.filter (fun z => residueParityHom k z = b)

/-- Reduction modulo two is onto. -/
theorem residueParityHom_surjective (k : ℕ) :
    Function.Surjective (residueParityHom k) := by
  intro b
  refine ⟨(b.val : ZMod (2 ^ (k + 1))), ?_⟩
  simp [residueParityHom]

/-- Exactly half of the residues modulo `2^(k+1)` have either prescribed
parity.  Thus the manuscript's fixed-`b` palette has `2^k=q/2`
colours. -/
theorem residueParityPalette_card (k : ℕ) (b : F2) :
    (residueParityPalette k b).card = 2 ^ k := by
  classical
  let h := residueParityHom k
  have hsurj : Function.Surjective h :=
    residueParityHom_surjective k
  have hsame :
      ∀ c : F2,
        (Finset.univ.filter (fun z : ZMod (2 ^ (k + 1)) => h z = c)).card =
          (Finset.univ.filter (fun z : ZMod (2 ^ (k + 1)) => h z = b)).card := by
    intro c
    exact AddMonoidHom.card_fiber_eq_of_mem_range h.toAddMonoidHom
      ⟨(hsurj c), rfl⟩ ⟨(hsurj b), rfl⟩
  have htotal :=
    Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ : Finset (ZMod (2 ^ (k + 1))))
      (t := Finset.univ : Finset F2)
      (f := h)
      (by intro z hz; simp)
  simp_rw [hsame] at htotal
  simp [residueParityPalette, h, ZMod.card, pow_succ] at htotal ⊢
  omega

/-- The fixed ordinary support-intersection count obtained from the explicit
perfect completion of the ambient BANANA structure. -/
noncomputable def completionIntersectionCount
    (x : Fin l → F2) (y : Fin r → F2) : ℕ :=
  PerfectCopyMatrices.ambientIntersectionCount
    (A.completionLeft x) (A.completionRight y)

/-- The parity of the fixed completion colour is exactly the original
BANANA pairing.  Thus reducing the integer colour modulo any even modulus
never assigns a wrong-parity colour to a line-pair copy. -/
theorem completionIntersectionCount_parity
    (x : Fin l → F2) (y : Fin r → F2) :
    (A.completionIntersectionCount x y : F2) = A.eval x y := by
  classical
  unfold completionIntersectionCount
    PerfectCopyMatrices.ambientIntersectionCount
  rw [Nat.cast_sum]
  simp_rw [ZMod.natCast_zmod_val]
  change
    A.completionLeft x ⬝ᵥ A.completionRight y = A.eval x y
  simpa only [perfectBanana_eval] using A.completion_pairing_apply x y

/-- On the image of a standard perfect target, the parity of the fixed
ambient colour is the standard dot-product pairing of the source vectors. -/
theorem completionIntersectionCount_map_parity
    {d : ℕ}
    (f : BananaMatrixEmbedding (perfectBanana d) A)
    (x y : Fin d → F2) :
    (A.completionIntersectionCount (f.left x) (f.right y) : F2) =
      x ⬝ᵥ y := by
  rw [A.completionIntersectionCount_parity]
  rw [f.pairing_apply]
  exact perfectBanana_eval x y

/-- Full arbitrary-copy form of the persistent BANANA colouring.

The ambient completion, and hence the colouring, is fixed before `f` is
chosen.  Every embedding of the standard perfect target of dimension
`2^(k+1)` contains a line-pair copy whose fixed ambient intersection
colour is any prescribed residue of the appropriate parity. -/
theorem exists_completionIntersectionColour
    (k : ℕ)
    (f :
      BananaMatrixEmbedding
        (perfectBanana ((2 ^ (k + 1) - 1) + 1)) A)
    (z : ZMod (2 ^ (k + 1))) :
    ∃ P :
        LinePairCopy
          ((2 ^ (k + 1) - 1) + 1)
          (residueParityHom k z),
      (A.completionIntersectionCount
          (f.left P.left) (f.right P.right) :
        ZMod (2 ^ (k + 1))) = z := by
  let g :
      BananaMatrixEmbedding
        (perfectBanana ((2 ^ (k + 1) - 1) + 1))
        (perfectBanana (l + r)) :=
    BananaMatrixEmbedding.comp A.completionEmbedding f
  let E : PerfectPairEmbedding
      ((2 ^ (k + 1) - 1) + 1) (l + r) :=
    g.toPerfectPairEmbedding
  obtain ⟨P, hP⟩ := E.exists_linePair_intersectionColour k z
  refine ⟨P, ?_⟩
  simpa [completionIntersectionCount, E, g,
    BananaMatrixEmbedding.comp,
    BananaMatrixEmbedding.toPerfectPairEmbedding,
    BananaMatrixStructure.completionEmbedding] using hP

/-- Fixed-source form of the persistent-colouring theorem.

For a fixed pairing value `b`, every residue of parity `b` occurs on a
line-pair copy inside the same target embedding.  This packages the
one-residue-at-a-time theorem in the quantifier order used in the
manuscript: the ambient completion and target copy are fixed before the
colour is chosen. -/
theorem completionIntersectionColours_cover_parity
    (k : ℕ) (b : F2)
    (f :
      BananaMatrixEmbedding
        (perfectBanana ((2 ^ (k + 1) - 1) + 1)) A) :
    ∀ z : ZMod (2 ^ (k + 1)),
      residueParityHom k z = b →
      ∃ P :
          LinePairCopy
            ((2 ^ (k + 1) - 1) + 1) b,
        (A.completionIntersectionCount
            (f.left P.left) (f.right P.right) :
          ZMod (2 ^ (k + 1))) = z := by
  intro z hz
  obtain ⟨P, hP⟩ := A.exists_completionIntersectionColour k f z
  let P' :
      LinePairCopy ((2 ^ (k + 1) - 1) + 1) b := {
    left := P.left
    right := P.right
    left_ne_zero := P.left_ne_zero
    right_ne_zero := P.right_ne_zero
    pairing := P.pairing.trans hz
  }
  refine ⟨P', ?_⟩
  simpa [P'] using hP

/-- Sharper pairing-one form: dimension `2^(k+1)-1` already forces
every odd residue. -/
theorem exists_pairingOne_completionIntersectionColour
    (k : ℕ)
    (f :
      BananaMatrixEmbedding
        (perfectBanana (2 ^ (k + 1) - 1)) A)
    (m : ℕ) (hm : Odd m) :
    ∃ P : LinePairCopy (2 ^ (k + 1) - 1) 1,
      (A.completionIntersectionCount
          (f.left P.left) (f.right P.right) :
        ZMod (2 ^ (k + 1))) =
          (m : ZMod (2 ^ (k + 1))) := by
  let g :
      BananaMatrixEmbedding
        (perfectBanana (2 ^ (k + 1) - 1))
        (perfectBanana (l + r)) :=
    BananaMatrixEmbedding.comp A.completionEmbedding f
  let E : PerfectPairEmbedding
      (2 ^ (k + 1) - 1) (l + r) :=
    g.toPerfectPairEmbedding
  obtain ⟨P, hP⟩ :=
    E.exists_pairingOne_intersectionColour k m hm
  refine ⟨P, ?_⟩
  simpa [completionIntersectionCount, E, g,
    BananaMatrixEmbedding.comp,
    BananaMatrixEmbedding.toPerfectPairEmbedding,
    BananaMatrixStructure.completionEmbedding] using hP

end BananaMatrixStructure

end SuccessorTree.NonPrecompact

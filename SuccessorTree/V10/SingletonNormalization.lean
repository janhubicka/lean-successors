import SuccessorTree.V10.BinaryUnaryAgeAdapter
import Mathlib.Tactic

/-!
# V10 Theorem 6.26: normalize an allowed unary/diagonal singleton

The paper permits arbitrary finite unary/binary languages. The
numerical H construction uses the neutral singleton (all unary
and diagonal bits false) at fake vertices. If that particular
singleton is forbidden, first choose any permitted singleton
template and toggle its unary and diagonal atoms uniformly.

The operation is an involutive Boolean mask, leaving all
directed OFF-DIAGONAL binary atoms unchanged. Apply precisely
the SAME mask to each forbidden finite pattern and to the
ambient structure. Then induced ordered embeddings correspond
in both directions, with every present and absent tuple
preserved. In particular, forbidden-age avoidance is invariant
and an allowed chosen singleton becomes neutral.

This is the missing normalization step from the original finite
unary/binary language to the normalized H construction. It
does not allow higher arity, alter Kpt axioms, or attach E to
an arbitrary finite forbidden L-witness.
-/

namespace SuccessorTree.V10

/-- Boolean masking by a fixed bit is injective and reflective,
including negative atoms. -/
theorem bool_xor_mask_eq_iff (x y m : Bool) :
    Bool.xor x m = Bool.xor y m ↔ x = y := by
  cases x <;> cases y <;> cases m <;> decide

/-- An allowed singleton template, stored as one unary/diagonal
bit vector independently of any off-diagonal binary relations. -/
structure SingletonLMask (du dd : Nat) where
  unary : Fin du → Bool
  diagonal : Fin dd → Bool

/-- Toggle the singleton part of an ordinary age-test structure.
Every off-diagonal directed relation is left unchanged. -/
def AgeTestModel.maskSingleton
    {db du dd : Nat}
    (A : AgeTestModel db du dd)
    (mask : SingletonLMask du dd) :
    AgeTestModel db du dd :=
  { carrier := A.carrier
    binary := A.binary
    unary := fun x t => Bool.xor (A.unary x t) (mask.unary t)
    diagonal := fun x t => Bool.xor (A.diagonal x t) (mask.diagonal t) }

/-- Apply the SAME unary/diagonal toggle to a finite forbidden
pattern; all directions and absent off-diagonal tuples stay put. -/
def ForbiddenAtomicPattern.maskSingleton
    {r db du dd : Nat}
    (F : ForbiddenAtomicPattern r db du dd)
    (mask : SingletonLMask du dd) :
    ForbiddenAtomicPattern r db du dd :=
  { binary := F.binary
    unary := fun x t => Bool.xor (F.unary x t) (mask.unary t)
    diagonal := fun x t => Bool.xor (F.diagonal x t) (mask.diagonal t) }

/-- Exact preservation AND reflection of ordered induced copies
under the same singleton normalization mask. -/
theorem realizes_maskSingleton_iff
    {r db du dd : Nat}
    (A : AgeTestModel db du dd)
    (F : ForbiddenAtomicPattern r db du dd)
    (mask : SingletonLMask du dd)
    (f : Fin r → Nat) :
    (A.maskSingleton mask).Realizes (F.maskSingleton mask) f ↔
      A.Realizes F f := by
  constructor
  · rintro ⟨hMono,hCarrier,hBinary,hUnary,hDiagonal⟩
    refine ⟨hMono,hCarrier,hBinary,?_,?_⟩
    · intro x a
      exact (bool_xor_mask_eq_iff
        (A.unary (f x) a) (F.unary x a) (mask.unary a)).1
        (hUnary x a)
    · intro x a
      exact (bool_xor_mask_eq_iff
        (A.diagonal (f x) a) (F.diagonal x a)
        (mask.diagonal a)).1 (hDiagonal x a)
  · rintro ⟨hMono,hCarrier,hBinary,hUnary,hDiagonal⟩
    refine ⟨hMono,hCarrier,hBinary,?_,?_⟩
    · intro x a
      exact (bool_xor_mask_eq_iff
        (A.unary (f x) a) (F.unary x a) (mask.unary a)).2
        (hUnary x a)
    · intro x a
      exact (bool_xor_mask_eq_iff
        (A.diagonal (f x) a) (F.diagonal x a)
        (mask.diagonal a)).2 (hDiagonal x a)

/-- Forbidden-copy avoidance for any fixed finite pattern is
preserved exactly, including present and absent unary/diagonal
bits and both directed off-diagonal relation orientations. -/
theorem avoids_maskSingleton_iff
    {r db du dd : Nat}
    (A : AgeTestModel db du dd)
    (F : ForbiddenAtomicPattern r db du dd)
    (mask : SingletonLMask du dd) :
    (¬ ∃ f : Fin r → Nat,
      (A.maskSingleton mask).Realizes (F.maskSingleton mask) f) ↔
    (¬ ∃ f : Fin r → Nat, A.Realizes F f) := by
  constructor
  · intro h f
    obtain ⟨e,he⟩ := f
    exact h ⟨e,(realizes_maskSingleton_iff A F mask e).2 he⟩
  · intro h f
    obtain ⟨e,he⟩ := f
    exact h ⟨e,(realizes_maskSingleton_iff A F mask e).1 he⟩

/-- The chosen permitted singleton becomes the literal all-false
neutral singleton in the normalized presentation. -/
theorem maskSingleton_chosen_template_neutral
    {du dd : Nat}
    (mask : SingletonLMask du dd) :
    (∀ t : Fin du, Bool.xor (mask.unary t) (mask.unary t) = false) ∧
    (∀ t : Fin dd,
      Bool.xor (mask.diagonal t) (mask.diagonal t) = false) := by
  constructor
  · intro t
    cases h : mask.unary t <;> simp [h]
  · intro t
    cases h : mask.diagonal t <;> simp [h]

/-- The mask does not change the two-vertex off-diagonal
relation pattern; irreducibility tests depending only on
these atoms therefore have the identical input data. -/
@[simp] theorem maskSingleton_binary_unchanged
    {r db du dd : Nat}
    (F : ForbiddenAtomicPattern r db du dd)
    (mask : SingletonLMask du dd) :
    (F.maskSingleton mask).binary = F.binary := rfl

end SuccessorTree.V10
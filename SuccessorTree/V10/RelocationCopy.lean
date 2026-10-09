import SuccessorTree.V10.HRelocation

/-!
# Relocating an entire forbidden configuration in the H age model

The v10 signature proof replaces the lower vertices of a forbidden
configuration by canonical generations 0, ..., r-1, while leaving the
upper vertices unchanged. Upper--upper relations need NOT arise from
the H-construction: they come from the hypothetical one-level age witness.

This file records upper--upper relations independently and proves equality
of EVERY directed binary tuple before and after lower relocation,
including nonedges and both orientations. Unary and diagonal data on
the lower vertices do not depend on their generations.

The theorem requires every lower--lower and lower--upper pair to be
linked in H, as is appropriate for an irreducible forbidden structure.
It makes no claim about the actual partial-type realization of the
upper witness vertices, or about its auxiliary E-relation.
-/

namespace SuccessorTree.V10

/-- An age witness with r lower and s upper vertices: lower--lower
and lower--upper tuples are controlled by the H types, while the
upper--upper tuples are those of the hypothetical witness itself. -/
def mixedBinary {n d r s : Nat}
    (B : Fin n → Fin n → Fin d → Bool)
    (upperBinary : Fin s → Fin s → Fin d → Bool)
    (k : Nat)
    (lowerFirst : Fin r → Fin n) (lowerGeneration : Fin r → Nat)
    (upperFirst : Fin s → Fin n) (upperGeneration : Fin s → Nat) :
    Sum (Fin r) (Fin s) → Sum (Fin r) (Fin s) → Fin d → Bool
  | .inl a, .inl b, t =>
      HBinary B k (.real (lowerFirst a) (lowerGeneration a))
        (.real (lowerFirst b) (lowerGeneration b)) t
  | .inl a, .inr b, t =>
      HBinary B k (.real (lowerFirst a) (lowerGeneration a))
        (.real (upperFirst b) (upperGeneration b)) t
  | .inr a, .inl b, t =>
      HBinary B k (.real (upperFirst a) (upperGeneration a))
        (.real (lowerFirst b) (lowerGeneration b)) t
  | .inr a, .inr b, t => upperBinary a b t

/-- The proposed relocation of all lower vertices preserves every
directed binary atomic tuple of the whole forbidden configuration.
The upper--upper relations are arbitrary and simply left unchanged. -/
theorem mixedBinary_eq_after_lower_relocation
    {n d r s : Nat}
    (B : Fin n → Fin n → Fin d → Bool)
    (upperBinary : Fin s → Fin s → Fin d → Bool)
    (k : Nat) (hr : r ≤ k)
    (lowerFirst : Fin r → Fin n) (lowerGeneration : Fin r → Nat)
    (upperFirst : Fin s → Fin n) (upperGeneration : Fin s → Nat)
    (hFirst : StrictMono lowerFirst)
    (hLowerLinked : ∀ a b : Fin r, a < b →
      HLinked B k
        (.real (lowerFirst a) (lowerGeneration a))
        (.real (lowerFirst b) (lowerGeneration b)))
    (hUpperAfter : ∀ a : Fin r, ∀ b : Fin s,
      lowerFirst a < upperFirst b)
    (hCrossLinked : ∀ a : Fin r, ∀ b : Fin s,
      HLinked B k
        (.real (lowerFirst a) (lowerGeneration a))
        (.real (upperFirst b) (upperGeneration b)))
    (x y : Sum (Fin r) (Fin s)) (t : Fin d) :
    mixedBinary B upperBinary k lowerFirst lowerGeneration
        upperFirst upperGeneration x y t =
      mixedBinary B upperBinary k lowerFirst (fun a => a.val)
        upperFirst upperGeneration x y t := by
  have hRank : ∀ a : Fin r, a.val ≤ lowerGeneration a :=
    ordered_linked_generation_rank B k r (by omega)
      lowerFirst lowerGeneration hFirst hLowerLinked
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          change HBinary B k
              (.real (lowerFirst a) (lowerGeneration a))
              (.real (lowerFirst b) (lowerGeneration b)) t =
            HBinary B k (.real (lowerFirst a) a.val)
              (.real (lowerFirst b) b.val) t
          rcases lt_trichotomy a b with hab | heq | hba
          · exact (relocated_lower_pairs B k r hr lowerFirst
                lowerGeneration hFirst hLowerLinked a b hab t).1
          · subst b
            simp
          · exact (relocated_lower_pairs B k r hr lowerFirst
                lowerGeneration hFirst hLowerLinked b a hba t).2
      | inr b =>
          change HBinary B k
              (.real (lowerFirst a) (lowerGeneration a))
              (.real (upperFirst b) (upperGeneration b)) t =
            HBinary B k (.real (lowerFirst a) a.val)
              (.real (upperFirst b) (upperGeneration b)) t
          exact (relocated_lower_upper_pair B k hr a
            (lowerFirst a) (upperFirst b)
            (lowerGeneration a) (upperGeneration b)
            (hUpperAfter a b) (hRank a) (hCrossLinked a b) t).1
  | inr a =>
      cases y with
      | inl b =>
          change HBinary B k
              (.real (upperFirst a) (upperGeneration a))
              (.real (lowerFirst b) (lowerGeneration b)) t =
            HBinary B k (.real (upperFirst a) (upperGeneration a))
              (.real (lowerFirst b) b.val) t
          exact (relocated_lower_upper_pair B k hr b
            (lowerFirst b) (upperFirst a)
            (lowerGeneration b) (upperGeneration a)
            (hUpperAfter b a) (hRank b) (hCrossLinked b a) t).2
      | inr b => rfl

/-- Unary and diagonal atomic data are preserved because the lower
vertex keeps its first index and upper vertices remain unchanged.
This statement is independent of the number of forbidden vertices. -/
def mixedSingleton {n d r s : Nat}
    (base : Fin n → Fin d → Bool) (upper : Fin s → Fin d → Bool)
    (lowerFirst : Fin r → Fin n) :
    Sum (Fin r) (Fin s) → Fin d → Bool
  | .inl a, t => base (lowerFirst a) t
  | .inr b, t => upper b t

theorem mixedSingleton_unchanged {n d r s : Nat}
    (base : Fin n → Fin d → Bool) (upper : Fin s → Fin d → Bool)
    (lowerFirst : Fin r → Fin n) (x : Sum (Fin r) (Fin s))
    (t : Fin d) :
    mixedSingleton base upper lowerFirst x t =
      mixedSingleton base upper lowerFirst x t := rfl

end SuccessorTree.V10

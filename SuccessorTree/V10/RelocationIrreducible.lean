import SuccessorTree.V10.RelocationCopy
import SuccessorTree.V10.BlockOrder

/-!
# Whole-configuration relocation from irreducibility and source order

The preceding module requires each lower--lower and lower--upper pair
to be linked in H and requires the lower first indices to increase.
For an irreducible forbidden witness, those assumptions follow from
pairwise binary irreducibility and strict order of the original H
positions. We derive them here before applying the all-tuples theorem.

Upper--upper tuples remain arbitrary data of the hypothetical witness;
they are not required to arise from a common H structure.
-/

namespace SuccessorTree.V10

/-- The ordering of two linked real H vertices forces the corresponding
base first indices to have the same strict order. -/
theorem linked_firstIndex_lt_of_position_lt
    {n d : Nat} (B : Fin n → Fin n → Fin d → Bool)
    (k : Nat) (i j : Fin n) (q m : Nat)
    (hLink : HLinked B k (.real i q) (.real j m))
    (hPos : hPosition k i.val q < hPosition k j.val m) :
    i < j := by
  rcases HLinked_gate B k i j q m hLink with
    ⟨hij, _, _, _⟩ | ⟨hji, hmle, _, _⟩
  · exact hij
  · have hrev : hPosition k j.val m < hPosition k i.val q :=
      hPosition_lt_of_block_lt k j.val i.val m q hmle
        (Fin.lt_def.mp hji)
    omega

/-- The complete hypothetical forbidden configuration is binary
irreducible. Upper--upper relations may be arbitrary, but for every
distinct pair at least one directed binary relation is present. -/
def MixedIrreducible {n d r s : Nat}
    (B : Fin n → Fin n → Fin d → Bool)
    (upperBinary : Fin s → Fin s → Fin d → Bool)
    (k : Nat)
    (lowerFirst : Fin r → Fin n) (lowerGeneration : Fin r → Nat)
    (upperFirst : Fin s → Fin n) (upperGeneration : Fin s → Nat) : Prop :=
  ∀ x y : Sum (Fin r) (Fin s), x ≠ y →
    ∃ t : Fin d,
      mixedBinary B upperBinary k lowerFirst lowerGeneration
        upperFirst upperGeneration x y t = true ∨
      mixedBinary B upperBinary k lowerFirst lowerGeneration
        upperFirst upperGeneration y x t = true

/-- The irreducibility and numerical source order of the entire
hypothetical forbidden copy imply that canonical relocation preserves
every binary fact. No separate lower--upper linkage assumption remains. -/
theorem irreducible_mixedBinary_eq_after_relocation
    {n d r s : Nat}
    (B : Fin n → Fin n → Fin d → Bool)
    (upperBinary : Fin s → Fin s → Fin d → Bool)
    (k : Nat) (hr : r ≤ k)
    (lowerFirst : Fin r → Fin n) (lowerGeneration : Fin r → Nat)
    (upperFirst : Fin s → Fin n) (upperGeneration : Fin s → Nat)
    (hIrreducible : MixedIrreducible B upperBinary k
      lowerFirst lowerGeneration upperFirst upperGeneration)
    (hLowerOrder : ∀ a b : Fin r, a < b →
      hPosition k (lowerFirst a).val (lowerGeneration a) <
        hPosition k (lowerFirst b).val (lowerGeneration b))
    (hCrossOrder : ∀ a : Fin r, ∀ b : Fin s,
      hPosition k (lowerFirst a).val (lowerGeneration a) <
        hPosition k (upperFirst b).val (upperGeneration b))
    (x y : Sum (Fin r) (Fin s)) (t : Fin d) :
    mixedBinary B upperBinary k lowerFirst lowerGeneration
      upperFirst upperGeneration x y t =
    mixedBinary B upperBinary k lowerFirst (fun a => a.val)
      upperFirst upperGeneration x y t := by
  have hLL : ∀ a b : Fin r, a < b →
      HLinked B k (.real (lowerFirst a) (lowerGeneration a))
        (.real (lowerFirst b) (lowerGeneration b)) := by
    intro a b hab
    have hne : (Sum.inl a : Sum (Fin r) (Fin s)) ≠ .inl b := by
      intro h
      have habne : a ≠ b := ne_of_lt hab
      exact habne (Sum.inl.inj h)
    obtain ⟨t, ht⟩ := hIrreducible (.inl a) (.inl b) hne
    exact ⟨t, by simpa only [mixedBinary] using ht⟩
  have hCU : ∀ a : Fin r, ∀ b : Fin s,
      HLinked B k (.real (lowerFirst a) (lowerGeneration a))
        (.real (upperFirst b) (upperGeneration b)) := by
    intro a b
    obtain ⟨t, ht⟩ := hIrreducible (.inl a) (.inr b) (by simp)
    exact ⟨t, by simpa only [mixedBinary] using ht⟩
  have hFirst : StrictMono lowerFirst := by
    intro a b hab
    exact linked_firstIndex_lt_of_position_lt B k
      (lowerFirst a) (lowerFirst b)
      (lowerGeneration a) (lowerGeneration b)
      (hLL a b hab) (hLowerOrder a b hab)
  have hUpperAfter : ∀ a : Fin r, ∀ b : Fin s,
      lowerFirst a < upperFirst b := by
    intro a b
    exact linked_firstIndex_lt_of_position_lt B k
      (lowerFirst a) (upperFirst b)
      (lowerGeneration a) (upperGeneration b)
      (hCU a b) (hCrossOrder a b)
  exact mixedBinary_eq_after_lower_relocation B upperBinary k hr
    lowerFirst lowerGeneration upperFirst upperGeneration
    hFirst hLL hUpperAfter hCU x y t

end SuccessorTree.V10

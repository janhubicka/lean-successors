import Mathlib.Tactic

/-!
# Finite counting interfaces for the v10 manuscript repairs

This module proves the finite combinatorial *consequences* used in the
reconstructed big-Ramsey argument, without assuming any particular model of
partial types. It deliberately does not claim the hard geometric input:

* Lemma \`lem:meets\` must construct the charge to higher-generation originals.
* Lemma \`lem:signatures\` must construct an injective finite signature code.

Those inputs are hypotheses below. The theorems isolate the precise
conclusions required by the induction and allow their hypotheses to be
discharged independently when the H-construction is formalised.
-/

namespace SuccessorTree
namespace V10

/-- Positive-generation meet levels can be counted once the geometric
argument assigns each such level to the image of a higher original.
No injectivity of the original-to-meet map is needed. -/
theorem meetLevels_card_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (meetLevels : Finset α) (higherOriginals : Finset β)
    (charge : β → α)
    (hcharge : ∀ x ∈ meetLevels,
      ∃ y ∈ higherOriginals, charge y = x) :
    meetLevels.card ≤ higherOriginals.card := by
  classical
  have hsub : meetLevels ⊆ higherOriginals.image charge := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcharge x hx
    exact Finset.mem_image.mpr ⟨y, hy, hxy⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- Each forbidden configuration of size n has at most \`(M+1)^n\`
vertex-valued signatures, where the extra value is the bottom symbol.
This is a counting statement, *conditional* on uniqueness of the
signature among selected levels. -/
theorem ageLevels_card_le_pow
    {n M : Nat} (ageLevels : Finset Nat)
    (signature : Nat → (Fin n → Fin (M + 1)))
    (hunique : ∀ a ∈ ageLevels, ∀ b ∈ ageLevels,
      signature a = signature b → a = b) :
    ageLevels.card ≤ (M + 1) ^ n := by
  classical
  have hinj : Set.InjOn signature (ageLevels : Set Nat) := by
    intro a ha b hb hab
    exact hunique a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab
  have heq : (ageLevels.image signature).card = ageLevels.card :=
    Finset.card_image_iff.mpr hinj
  have hbound :
      (ageLevels.image signature).card ≤
        (Finset.univ : Finset (Fin n → Fin (M + 1))).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [heq] at hbound
  simpa [Fintype.card_fun] using hbound

/-- The signature code may first name a forbidden family member and then
assign one of M original vertices or bottom to each of its positions.
This is the counting term \`R(M)\` in the proposed v10 proof. -/
theorem ageLevels_card_le_family
    {k M : Nat} (sizes : Fin k → Nat)
    (ageLevels : Finset Nat)
    (signature : Nat →
      (Σ i : Fin k, Fin (sizes i) → Fin (M + 1)))
    (hunique : ∀ a ∈ ageLevels, ∀ b ∈ ageLevels,
      signature a = signature b → a = b) :
    ageLevels.card ≤ ∑ i : Fin k, (M + 1) ^ (sizes i) := by
  classical
  have hinj : Set.InjOn signature (ageLevels : Set Nat) := by
    intro a ha b hb hab
    exact hunique a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab
  have heq : (ageLevels.image signature).card = ageLevels.card :=
    Finset.card_image_iff.mpr hinj
  have hbound :
      (ageLevels.image signature).card ≤
        (Finset.univ : Finset
          (Σ i : Fin k, Fin (sizes i) → Fin (M + 1))).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [heq] at hbound
  simpa [Fintype.card_sigma, Fintype.card_fun] using hbound

/-- Combining the charged meet levels with the coded age obstructions.
No false strict-generation descent or duplicate-counting assumption is used. -/
theorem newlySelected_card_le
    {α : Type*} [DecidableEq α]
    {k M : Nat} (sizes : Fin k → Nat)
    (meetLevels ageLevels higherOriginals : Finset α)
    (charge : α → α)
    (hcharge : ∀ x ∈ meetLevels,
      ∃ y ∈ higherOriginals, charge y = x)
    (signature : α →
      (Σ i : Fin k, Fin (sizes i) → Fin (M + 1)))
    (hunique : ∀ a ∈ ageLevels, ∀ b ∈ ageLevels,
      signature a = signature b → a = b) :
    (meetLevels ∪ ageLevels).card ≤
      higherOriginals.card + ∑ i : Fin k, (M + 1) ^ (sizes i) := by
  classical
  have hmeet := meetLevels_card_le meetLevels higherOriginals charge hcharge
  have hage : ageLevels.card ≤ ∑ i : Fin k, (M + 1) ^ (sizes i) := by
    have hinj : Set.InjOn signature (ageLevels : Set α) := by
      intro a ha b hb hab
      exact hunique a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab
    have heq : (ageLevels.image signature).card = ageLevels.card :=
      Finset.card_image_iff.mpr hinj
    have hbound :
        (ageLevels.image signature).card ≤
          (Finset.univ : Finset
            (Σ i : Fin k, Fin (sizes i) → Fin (M + 1))).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [heq] at hbound
    simpa [Fintype.card_sigma, Fintype.card_fun] using hbound
  exact (Finset.card_union_le meetLevels ageLevels).trans
    (Nat.add_le_add hmeet hage)

end V10
end SuccessorTree

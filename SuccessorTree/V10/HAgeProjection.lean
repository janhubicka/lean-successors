import SuccessorTree.V10.HAge
import Mathlib.Tactic

/-!
# Whole forbidden-copy projection from H back to the base structure

For a finite binary/unary language, suppose an ordered forbidden copy of
size at least two is embedded in the explicit H age model and is
irreducible. Every distinct pair of its vertices participates in some
directed binary relation. The H-copying gate then forces all image
vertices to be real with DISTINCT first indices. All directed binary,
unary and diagonal atomic facts are copied exactly from the base
structure on those first indices.

Thus a forbidden copy in the exact H model would induce a forbidden
copy in its base K. This is a concrete age-preservation statement about
HVertex / HBinary / HUnary / HDiagonal, not yet a proof that the printed
partial-structure H has precisely those interpretations.
-/

namespace SuccessorTree.V10

/-- Any pairwise-linked family of at least two H vertices is real at
every address. No orientation or generation choice is made here. -/
theorem every_irreducible_H_vertex_is_real
    {n d r : Nat}
    (B : Fin n → Fin n → Fin d → Bool) (k : Nat)
    (vertex : Fin r → HVertex n) (hr : 1 < r)
    (hLinked : ∀ a b : Fin r, a ≠ b →
      HLinked B k (vertex a) (vertex b)) :
    ∀ a : Fin r, ∃ i : Fin n, ∃ g : Nat,
      vertex a = .real i g := by
  let zero : Fin r := ⟨0, by omega⟩
  let one : Fin r := ⟨1, hr⟩
  intro a
  obtain ⟨b, hab⟩ : ∃ b : Fin r, a ≠ b := by
    by_cases ha : a = zero
    · refine ⟨one, ?_⟩
      intro heq
      have hzo : zero = one := ha.symm.trans heq
      have hv := congrArg Fin.val hzo
      norm_num [zero, one] at hv
    · exact ⟨zero, ha⟩
  obtain ⟨i, j, g, h, hva, _, _⟩ :=
    HLinked_real B k (hLinked a b hab)
  exact ⟨i, g, hva⟩

/-- Every irreducible finite H configuration with at least two vertices
has a simultaneous induced embedding into the base structure on its
first indices. Crucially, this includes ALL atomic values, not just
the positive relations used to obtain the gate. -/
theorem irreducible_H_copy_projects_to_base
    {n db du dd r : Nat}
    (B : Fin n → Fin n → Fin db → Bool)
    (U : Fin n → Fin du → Bool)
    (D : Fin n → Fin dd → Bool)
    (k : Nat)
    (vertex : Fin r → HVertex n) (hr : 1 < r)
    (hLinked : ∀ a b : Fin r, a ≠ b →
      HLinked B k (vertex a) (vertex b)) :
    ∃ f : Fin r → Fin n,
      Function.Injective f ∧
      (∀ a b : Fin r, a ≠ b → ∀ t : Fin db,
        HBinary B k (vertex a) (vertex b) t =
          B (f a) (f b) t) ∧
      (∀ a : Fin r, ∀ t : Fin du,
        HUnary U (vertex a) t = U (f a) t) ∧
      (∀ a : Fin r, ∀ t : Fin dd,
        HDiagonal D (vertex a) t = D (f a) t) := by
  classical
  have hReal := every_irreducible_H_vertex_is_real B k vertex hr hLinked
  let f : Fin r → Fin n := fun a => Classical.choose (hReal a)
  let g : Fin r → Nat := fun a =>
    Classical.choose (Classical.choose_spec (hReal a))
  have hrepr (a : Fin r) : vertex a = .real (f a) (g a) :=
    Classical.choose_spec (Classical.choose_spec (hReal a))
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    by_contra hne
    have hlink : HLinked B k (.real (f a) (g a))
        (.real (f b) (g b)) := by
      rw [← hrepr a, ← hrepr b]
      exact hLinked a b hne
    have hgate := HLinked_gate B k (f a) (f b)
      (g a) (g b) hlink
    rcases hgate with ⟨hlt, _, _, _⟩ | ⟨hlt, _, _, _⟩
    · exact (ne_of_lt hlt) hab
    · exact (Ne.symm (ne_of_lt hlt)) hab
  · intro a b hab t
    have hlink := hLinked a b hab
    rw [hrepr a, hrepr b] at hlink ⊢
    exact (HBinary_eq_base_of_link B k (f a) (f b)
      (g a) (g b) hlink t).1
  · intro a t
    rw [hrepr a]
    rfl
  · intro a t
    rw [hrepr a]
    rfl

end SuccessorTree.V10

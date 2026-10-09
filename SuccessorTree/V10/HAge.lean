import SuccessorTree.V10.HRelations
import Mathlib.Tactic

/-!
# The binary age of the explicit H-construction

This module models real vertices of the H-construction by their original
index and generation, and fake vertices by an address. A finite tuple of
directed binary bits encodes the ordered cross-pair relations of a finite
binary signature; unary and diagonal data are copied from the base
structure on real vertices. Fake vertices have the neutral singleton.

The main structural statement is that every irreducible subset with at
least two vertices projects injectively to first indices, and all binary
relations on that subset are precisely those of the base structure.

This checks the *proposed exact-copying interpretation* of H. It is not
an equivalence theorem for the one-way containment currently printed in
the manuscript. The auxiliary E-relation is handled in SocleE.
-/

namespace SuccessorTree.V10

/-- Abstract real and fake vertices with the same first-index convention
as the manuscript's enumerated H construction. -/
inductive HVertex (n : Nat) where
  | fake (address : Nat)
  | real (first : Fin n) (generation : Nat)
  deriving DecidableEq

/-- The admissible generation gate, with the lower base index taking
the lower generation. The second disjunct handles reversed pair order. -/
def HCrossAllowed {n : Nat}
    (k : Nat) (i j : Fin n) (q m : Nat) : Prop :=
  (i < j ∧ q ≤ k ∧ m ≤ k ∧
      (q < m ∨ (q = m ∧ m = k))) ∨
  (j < i ∧ m ≤ k ∧ q ≤ k ∧
      (m < q ∨ (m = q ∧ q = k)))

/-- Explicit decidability of the arithmetic cross-generation gate. -/
instance HCrossAllowed.decidable {n : Nat}
    (k : Nat) (i j : Fin n) (q m : Nat) :
    Decidable (HCrossAllowed k i j q m) := by
  unfold HCrossAllowed
  infer_instance

theorem HCrossAllowed_swap {n : Nat}
    (k : Nat) (i j : Fin n) (q m : Nat) :
    HCrossAllowed k i j q m ↔
      HCrossAllowed k j i m q := by
  constructor
  · rintro (⟨hij, hq, hm, hg⟩ | ⟨hji, hm, hq, hg⟩)
    · exact Or.inr ⟨hij, hq, hm, hg⟩
    · exact Or.inl ⟨hji, hm, hq, hg⟩
  · rintro (⟨hji, hm, hq, hg⟩ | ⟨hij, hq, hm, hg⟩)
    · exact Or.inr ⟨hji, hm, hq, hg⟩
    · exact Or.inl ⟨hij, hq, hm, hg⟩

/-- A directed binary relation bit between two H vertices. Each bit
is an ordered atomic tuple; the base function need not be symmetric. -/
def HBinary {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool) (k : Nat)
    (a b : HVertex n) (r : Fin d) : Bool :=
  match a, b with
  | .real i q, .real j m =>
      if HCrossAllowed k i j q m then B i j r else false
  | _, _ => false

/-- Unary atomic bits; the fake singleton is neutral. -/
def HUnary {n d : Nat}
    (U : Fin n → Fin d → Bool) (a : HVertex n) (r : Fin d) : Bool :=
  match a with
  | .real i _ => U i r
  | .fake _ => false

/-- Diagonal binary atomic bits are singleton data; they too are copied
from the base structure and absent at fake vertices. -/
def HDiagonal {n d : Nat}
    (D : Fin n → Fin d → Bool) (a : HVertex n) (r : Fin d) : Bool :=
  match a with
  | .real i _ => D i r
  | .fake _ => false

@[simp] theorem HBinary_fake_left {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool) (k addr : Nat)
    (v : HVertex n) (r : Fin d) :
    HBinary B k (.fake addr) v r = false := by
  cases v <;> rfl

@[simp] theorem HBinary_fake_right {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool) (k addr : Nat)
    (v : HVertex n) (r : Fin d) :
    HBinary B k v (.fake addr) r = false := by
  cases v <;> rfl

@[simp] theorem HBinary_same_first {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool)
    (k : Nat) (i : Fin n) (q m : Nat) (r : Fin d) :
    HBinary B k (.real i q) (.real i m) r = false := by
  simp [HBinary, HCrossAllowed]

/-- A pair is linked when at least one directed binary relation holds. -/
def HLinked {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool) (k : Nat)
    (a b : HVertex n) : Prop :=
  ∃ r : Fin d, HBinary B k a b r = true ∨
    HBinary B k b a r = true

theorem HLinked_real {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool) (k : Nat)
    {a b : HVertex n} (h : HLinked B k a b) :
    ∃ (i j : Fin n) (q m : Nat),
      a = .real i q ∧ b = .real j m ∧ i ≠ j := by
  cases a with
  | fake addr =>
      rcases h with ⟨r, h⟩
      simp [HLinked, HBinary] at h
  | real i q =>
      cases b with
      | fake addr =>
          rcases h with ⟨r, h⟩
          simp [HLinked, HBinary] at h
      | real j m =>
          have hij : i ≠ j := by
            intro heq
            subst j
            rcases h with ⟨r, h⟩
            simp at h
          exact ⟨i, j, q, m, rfl, rfl, hij⟩

/-- A link requires the exact generation gate, in either directed order. -/
theorem HLinked_gate {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool) (k : Nat)
    (i j : Fin n) (q m : Nat)
    (h : HLinked B k (.real i q) (.real j m)) :
    HCrossAllowed k i j q m := by
  by_contra hgate
  have hreverse : ¬ HCrossAllowed k j i m q := by
    intro h
    exact hgate ((HCrossAllowed_swap k i j q m).mpr h)
  rcases h with ⟨r, h | h⟩
  · simp [HBinary, hgate] at h
  · simp [HBinary, hreverse] at h

/-- Every linked pair has *exactly* the corresponding base binary
relations, in both directions. -/
theorem HBinary_eq_base_of_link {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool)
    (k : Nat) (i j : Fin n) (q m : Nat)
    (h : HLinked B k (.real i q) (.real j m)) :
    ∀ r : Fin d,
      HBinary B k (.real i q) (.real j m) r = B i j r ∧
      HBinary B k (.real j m) (.real i q) r = B j i r := by
  intro r
  have hg := HLinked_gate B k i j q m h
  have hs := (HCrossAllowed_swap k i j q m).mp hg
  simp [HBinary, hg, hs]

/-- Irreducibility in a binary language: every two distinct vertices
participate in some directed binary relation. -/
def HIrreducible {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool) (k : Nat)
    (X : Set (HVertex n)) : Prop :=
  ∀ ⦃a b : HVertex n⦄,
    a ∈ X → b ∈ X → a ≠ b → HLinked B k a b

/-- Every distinct pair of a nontrivial irreducible set consists of
real vertices with different first indices. All directed binary
relations are inherited from the base structure. -/
theorem irreducible_pair_projects_to_base {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool) (k : Nat)
    (X : Set (HVertex n)) (hX : HIrreducible B k X)
    {a b : HVertex n}
    (ha : a ∈ X) (hb : b ∈ X) (hne : a ≠ b) :
    ∃ (i j : Fin n) (q m : Nat),
      a = .real i q ∧ b = .real j m ∧ i ≠ j ∧
      (∀ r : Fin d,
        HBinary B k a b r = B i j r ∧
        HBinary B k b a r = B j i r) := by
  have hlink : HLinked B k a b := hX ha hb hne
  obtain ⟨i, j, q, m, h1, h2, hij⟩ := HLinked_real B k hlink
  subst a
  subst b
  exact ⟨i, j, q, m, rfl, rfl, hij,
    HBinary_eq_base_of_link B k i j q m hlink⟩

/-- The entire top-generation layer copies each *off-diagonal*
directed binary relation, with no symmetry assumption on the base data. -/
theorem HBinary_top_copy {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool)
    (k : Nat) (i j : Fin n) (hneq : i ≠ j) (r : Fin d) :
    HBinary B k (.real i k) (.real j k) r = B i j r := by
  have hgate : HCrossAllowed k i j k k := by
    rcases lt_trichotomy i j with hij | heq | hji
    · exact Or.inl ⟨hij, le_rfl, le_rfl, Or.inr ⟨rfl, rfl⟩⟩
    · exact False.elim (hneq heq)
    · exact Or.inr ⟨hji, le_rfl, le_rfl, Or.inr ⟨rfl, rfl⟩⟩
  simp [HBinary, hgate]

/-- Unary and diagonal tuples in the top-generation copy are inherited
from the corresponding base singleton. -/
@[simp] theorem HUnary_top_copy {n d : Nat}
    (U : Fin n → Fin d → Bool) (i : Fin n) (k : Nat) (r : Fin d) :
    HUnary U (.real i k) r = U i r := rfl

@[simp] theorem HDiagonal_top_copy {n d : Nat}
    (D : Fin n → Fin d → Bool) (i : Fin n) (k : Nat) (r : Fin d) :
    HDiagonal D (.real i k) r = D i r := rfl

/-- The numeric original-first-index order is preserved by the
enumeration iota used in the manuscript. -/
theorem hPosition_top_order
    (k : Nat) (i j : Nat) (hij : i < j) :
    hPosition k i k < hPosition k j k :=
  hPosition_lt_of_block_lt k i j k k (Nat.le_refl k) hij

end SuccessorTree.V10

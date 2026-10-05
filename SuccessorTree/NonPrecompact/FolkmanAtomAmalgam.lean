import Mathlib

/-!
# Atom geometry for the Folkman--BANANA strong amalgam

For a Boolean-ring embedding, source atoms split into nonempty blocks over
the common base atoms, but target atoms may also lie outside the greatest
element of the source.  At atom level the strong amalgam therefore consists
of:

* compatible pairs of atoms lying over one common base atom;
* a private tagged point for each left outside atom;
* a private tagged point for each right outside atom.

This file proves the strong-intersection statement for that construction.
It is the set-theoretic core of the Folkman--BANANA amalgam proof.
-/

namespace SuccessorTree.NonPrecompact

/-- Compatible inside atom pairs for partial atom maps to a common base. -/
abbrev FolkmanCompatiblePair
    {A B C : Type*}
    (f : B → Option A) (g : C → Option A) :=
  {p : B × C // ∃ a : A, f p.1 = some a ∧ g p.2 = some a}

/-- Left atoms outside the common base support. -/
abbrev FolkmanLeftOutside
    {A B : Type*} (f : B → Option A) :=
  {b : B // f b = none}

/-- Right atoms outside the common base support. -/
abbrev FolkmanRightOutside
    {A C : Type*} (g : C → Option A) :=
  {c : C // g c = none}

/-- Atom set of the Folkman fibre-grid amalgam. -/
abbrev FolkmanAtomAmalgam
    {A B C : Type*}
    (f : B → Option A) (g : C → Option A) :=
  Sum (FolkmanCompatiblePair f g)
    (Sum (FolkmanLeftOutside f) (FolkmanRightOutside g))

/-- Membership in the image of a selected set of left atoms. -/
def folkmanLeftImage
    {A B C : Type*}
    {f : B → Option A} {g : C → Option A}
    (SB : Set B) :
    FolkmanAtomAmalgam f g → Prop
  | .inl p => p.1.1 ∈ SB
  | .inr (.inl b) => b.1 ∈ SB
  | .inr (.inr _) => False

/-- Membership in the image of a selected set of right atoms. -/
def folkmanRightImage
    {A B C : Type*}
    {f : B → Option A} {g : C → Option A}
    (SC : Set C) :
    FolkmanAtomAmalgam f g → Prop
  | .inl p => p.1.2 ∈ SC
  | .inr (.inl _) => False
  | .inr (.inr c) => c.1 ∈ SC

/-- Left membership is constant on every nonempty fibre over a base atom,
provided the left and right amalgam images agree. -/
theorem folkman_mem_constant_left
    {A B C : Type*}
    (f : B → Option A) (g : C → Option A)
    (hg : ∀ a : A, ∃ c : C, g c = some a)
    (SB : Set B) (SC : Set C)
    (himage :
      ∀ p : FolkmanAtomAmalgam f g,
        folkmanLeftImage SB p ↔ folkmanRightImage SC p)
    {b₁ b₂ : B} {a : A}
    (hb₁ : f b₁ = some a) (hb₂ : f b₂ = some a) :
    b₁ ∈ SB ↔ b₂ ∈ SB := by
  obtain ⟨c, hc⟩ := hg a
  let p₁ : FolkmanCompatiblePair f g :=
    ⟨(b₁, c), ⟨a, hb₁, hc⟩⟩
  let p₂ : FolkmanCompatiblePair f g :=
    ⟨(b₂, c), ⟨a, hb₂, hc⟩⟩
  have h₁ := himage (Sum.inl p₁)
  have h₂ := himage (Sum.inl p₂)
  exact h₁.trans h₂.symm

/-- Right membership is constant on every nonempty fibre over a base atom. -/
theorem folkman_mem_constant_right
    {A B C : Type*}
    (f : B → Option A) (g : C → Option A)
    (hf : ∀ a : A, ∃ b : B, f b = some a)
    (SB : Set B) (SC : Set C)
    (himage :
      ∀ p : FolkmanAtomAmalgam f g,
        folkmanLeftImage SB p ↔ folkmanRightImage SC p)
    {c₁ c₂ : C} {a : A}
    (hc₁ : g c₁ = some a) (hc₂ : g c₂ = some a) :
    c₁ ∈ SC ↔ c₂ ∈ SC := by
  obtain ⟨b, hb⟩ := hf a
  let p₁ : FolkmanCompatiblePair f g :=
    ⟨(b, c₁), ⟨a, hb, hc₁⟩⟩
  let p₂ : FolkmanCompatiblePair f g :=
    ⟨(b, c₂), ⟨a, hb, hc₂⟩⟩
  have h₁ := himage (Sum.inl p₁)
  have h₂ := himage (Sum.inl p₂)
  exact h₁.symm.trans h₂

/-- A selected outside left atom cannot occur in an image which is also a
right image, because its private tagged amalgam atom is absent on the right. -/
theorem folkman_left_outside_not_mem
    {A B C : Type*}
    {f : B → Option A} {g : C → Option A}
    (SB : Set B) (SC : Set C)
    (himage :
      ∀ p : FolkmanAtomAmalgam f g,
        folkmanLeftImage SB p ↔ folkmanRightImage SC p)
    {b : B} (hb : f b = none) :
    b ∉ SB := by
  let bo : FolkmanLeftOutside f := ⟨b, hb⟩
  have h := himage (Sum.inr (Sum.inl bo))
  simpa [folkmanLeftImage, folkmanRightImage] using h

/-- Symmetric statement for an outside right atom. -/
theorem folkman_right_outside_not_mem
    {A B C : Type*}
    {f : B → Option A} {g : C → Option A}
    (SB : Set B) (SC : Set C)
    (himage :
      ∀ p : FolkmanAtomAmalgam f g,
        folkmanLeftImage SB p ↔ folkmanRightImage SC p)
    {c : C} (hc : g c = none) :
    c ∉ SC := by
  let co : FolkmanRightOutside g := ⟨c, hc⟩
  have h := himage (Sum.inr (Sum.inr co))
  simpa [folkmanLeftImage, folkmanRightImage] using h

/-- Strong intersection for the Folkman atom amalgam.

If a union of left atom blocks equals a union of right atom blocks in the
fibre-grid-plus-private-points amalgam, then no outside atom is selected and
the inside selections on both sides are exactly the inverse images of one
common subset of base atoms. -/
theorem exists_common_subset_of_folkmanAtomAmalgam
    {A B C : Type*}
    (f : B → Option A) (g : C → Option A)
    (hf : ∀ a : A, ∃ b : B, f b = some a)
    (hg : ∀ a : A, ∃ c : C, g c = some a)
    (SB : Set B) (SC : Set C)
    (himage :
      ∀ p : FolkmanAtomAmalgam f g,
        folkmanLeftImage SB p ↔ folkmanRightImage SC p) :
    ∃ SA : Set A,
      (∀ b a, f b = some a → (b ∈ SB ↔ a ∈ SA)) ∧
      (∀ b, f b = none → b ∉ SB) ∧
      (∀ c a, g c = some a → (c ∈ SC ↔ a ∈ SA)) ∧
      (∀ c, g c = none → c ∉ SC) := by
  let SA : Set A := {a | ∃ b : B, f b = some a ∧ b ∈ SB}
  refine ⟨SA, ?_, ?_, ?_, ?_⟩
  · intro b a hb
    constructor
    · intro hSB
      exact ⟨b, hb, hSB⟩
    · rintro ⟨b', hb', hb'S⟩
      exact
        (folkman_mem_constant_left
          f g hg SB SC himage hb hb').2 hb'S
  · intro b hb
    exact folkman_left_outside_not_mem SB SC himage hb
  · intro c a hc
    constructor
    · intro hSC
      obtain ⟨b, hb⟩ := hf a
      refine ⟨b, hb, ?_⟩
      let p : FolkmanCompatiblePair f g :=
        ⟨(b, c), ⟨a, hb, hc⟩⟩
      exact (himage (Sum.inl p)).2 hSC
    · rintro ⟨b, hb, hbS⟩
      obtain ⟨c', hc'⟩ := hg a
      let p : FolkmanCompatiblePair f g :=
        ⟨(b, c'), ⟨a, hb, hc'⟩⟩
      have hc'S : c' ∈ SC := (himage (Sum.inl p)).1 hbS
      exact
        (folkman_mem_constant_right
          f g hf SB SC himage hc' hc).1 hc'S
  · intro c hc
    exact folkman_right_outside_not_mem SB SC himage hc

end SuccessorTree.NonPrecompact

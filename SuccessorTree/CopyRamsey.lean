import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Abstract copy Ramsey interface

This file isolates the finite-structure Ramsey infrastructure needed by the
circulation lemmas comparing copy Ramsey degrees with precompact Ramsey
expansions.

A FiniteCopySystem records objects, embeddings, copy-ranges, composition,
and the functorial action of embeddings on copies. It deliberately does not
assume rigidity: several embeddings may have the same range.

A RamseyExpansion records finitely many expansion types, hereditary
restriction of an expansion along a reduct embedding, existence of expansion
types, and the embedding Ramsey property for expanded objects.

The main theorem is the manuscript's expansion-degree bound.
-/

namespace SuccessorTree

universe u v w x

structure FiniteCopySystem where
  Obj : Type u
  Emb : Obj → Obj → Type v
  Copy : Obj → Obj → Type w
  idEmb : ∀ A, Emb A A
  compEmb : ∀ {A B C}, Emb A B → Emb B C → Emb A C
  comp_id_left :
    ∀ {A B} (f : Emb A B), compEmb (idEmb A) f = f
  comp_id_right :
    ∀ {A B} (f : Emb A B), compEmb f (idEmb B) = f
  comp_assoc :
    ∀ {A B C D} (f : Emb A B) (g : Emb B C) (h : Emb C D),
      compEmb (compEmb f g) h = compEmb f (compEmb g h)
  range : ∀ {A B}, Emb A B → Copy A B
  mapCopy : ∀ {A B C}, Emb B C → Copy A B → Copy A C
  mapCopy_id :
    ∀ {A B} (p : Copy A B),
      mapCopy (idEmb B) p = p
  mapCopy_comp :
    ∀ {A B C D} (f : Emb B C) (g : Emb C D) (p : Copy A B),
      mapCopy (compEmb f g) p = mapCopy g (mapCopy f p)
  range_comp :
    ∀ {A B C} (f : Emb A B) (g : Emb B C),
      range (compEmb f g) = mapCopy g (range f)
  range_surjective :
    ∀ {A B}, Function.Surjective (@range A B)
  /-- Intrinsic containment of a smaller copy in a larger copy in the same ambient object. -/
  Subcopy : ∀ {P A C}, Copy P C → Copy A C → Prop
  /-- The P-subcopies of the range of an embedding A → C are exactly
  the transported P-copies of A. -/
  subcopy_range_iff :
    ∀ {P A C} (f : Emb A C) (p : Copy P C),
      Subcopy p (range f) ↔
        ∃ q : Copy P A, mapCopy f q = p
  copyFintype : ∀ A B, Fintype (Copy A B)
  copyDecidableEq : ∀ A B, DecidableEq (Copy A B)

namespace FiniteCopySystem

variable (S : FiniteCopySystem)

attribute [local instance] FiniteCopySystem.copyFintype
attribute [local instance] FiniteCopySystem.copyDecidableEq

def coloursInside
    {A B C : S.Obj} {r : ℕ}
    (colouring : S.Copy A C → Fin r)
    (f : S.Emb B C) : Finset (Fin r) :=
  Finset.univ.image fun p : S.Copy A B => colouring (S.mapCopy f p)

def CopyArrow
    (A B C : S.Obj) (r t : ℕ) : Prop :=
  ∀ colouring : S.Copy A C → Fin r,
    ∃ f : S.Emb B C,
      (S.coloursInside colouring f).card ≤ t

def CopyRamseyDegreeLE
    (A : S.Obj) (t : ℕ) : Prop :=
  ∀ (B : S.Obj) (r : ℕ), 0 < r →
    ∃ C : S.Obj, S.CopyArrow A B C r t

end FiniteCopySystem

/-- An abstract amalgamation class on a finite copy system.  This is the
one amalgamation-square operation needed by the degree-propagation lemma. -/
structure AmalgamationSystem (S : FiniteCopySystem) where
  amalgamate :
    ∀ {P B A : S.Obj} (p : S.Emb P B) (a : S.Emb P A),
      ∃ (D : S.Obj) (i : S.Emb B D) (j : S.Emb A D),
        S.compEmb p i = S.compEmb a j

namespace AmalgamationSystem

variable {S : FiniteCopySystem}

attribute [local instance] FiniteCopySystem.copyFintype
attribute [local instance] FiniteCopySystem.copyDecidableEq

/-- Intrinsic subcopy containment is preserved by further embeddings. -/
theorem subcopy_map
    {P A B C : S.Obj}
    (g : S.Emb B C)
    {p : S.Copy P B} {a : S.Copy A B}
    (h : S.Subcopy p a) :
    S.Subcopy (S.mapCopy g p) (S.mapCopy g a) := by
  obtain ⟨fa, hfa⟩ := S.range_surjective a
  rw [← hfa] at h
  obtain ⟨q, hq⟩ := (S.subcopy_range_iff fa p).mp h
  have hrange :
      S.mapCopy g a = S.range (S.compEmb fa g) := by
    rw [S.range_comp, hfa]
  rw [hrange]
  apply (S.subcopy_range_iff (S.compEmb fa g) (S.mapCopy g p)).mpr
  refine ⟨q, ?_⟩
  rw [S.mapCopy_comp, hq]

/-- A finite list of original P-copies of B can simultaneously be made
extendible to A-copies after embedding B into a further amalgam.  Repetitions
are harmless; this list form is the direct recursion behind the finite-set
version below. -/
theorem extend_list_copies
    (M : AmalgamationSystem S)
    {P A B : S.Obj}
    (pA : S.Emb P A)
    (copies : List (S.Copy P B)) :
    ∃ (D : S.Obj) (base : S.Emb B D),
      ∀ pcopy ∈ copies,
        ∃ a : S.Copy A D,
          S.Subcopy (S.mapCopy base pcopy) a := by
  classical
  exact List.rec
    (by
      refine ⟨B, S.idEmb B, ?_⟩
      intro q hq
      simp at hq)
    (fun headCopy tail ih => by
      obtain ⟨D, base, hbase⟩ := ih
      obtain ⟨ep, hep⟩ := S.range_surjective headCopy
      obtain ⟨D', i, j, hij⟩ :=
        M.amalgamate (S.compEmb ep base) pA
      refine ⟨D', S.compEmb base i, ?_⟩
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · let a : S.Copy A D' := S.range j
        refine ⟨a, ?_⟩
        have hpbase :
            S.mapCopy base headCopy =
              S.range (S.compEmb ep base) := by
          calc
            S.mapCopy base headCopy =
                S.mapCopy base (S.range ep) := by rw [hep]
            _ = S.range (S.compEmb ep base) :=
              (S.range_comp ep base).symm
        have hpmap :
            S.mapCopy (S.compEmb base i) headCopy =
              S.range (S.compEmb (S.compEmb ep base) i) := by
          calc
            S.mapCopy (S.compEmb base i) headCopy =
                S.mapCopy i (S.mapCopy base headCopy) :=
              S.mapCopy_comp base i headCopy
            _ = S.mapCopy i (S.range (S.compEmb ep base)) := by
              rw [hpbase]
            _ = S.range (S.compEmb (S.compEmb ep base) i) :=
              (S.range_comp (S.compEmb ep base) i).symm
        rw [hpmap, hij]
        exact (S.subcopy_range_iff j
          (S.range (S.compEmb pA j))).mpr
            ⟨S.range pA, by rw [S.range_comp]⟩
      · obtain ⟨a, ha⟩ := hbase q hq
        refine ⟨S.mapCopy i a, ?_⟩
        rw [S.mapCopy_comp]
        exact subcopy_map (S := S) i ha)
    copies

/-- A finite family of original P-copies of B can simultaneously be made
extendible to A-copies after embedding B into a further amalgam. -/
theorem extend_finite_copies
    (M : AmalgamationSystem S)
    {P A B : S.Obj}
    (pA : S.Emb P A)
    (copies : Finset (S.Copy P B)) :
    ∃ (D : S.Obj) (base : S.Emb B D),
      ∀ p ∈ copies,
        ∃ a : S.Copy A D,
          S.Subcopy (S.mapCopy base p) a := by
  classical
  obtain ⟨D, base, h⟩ :=
    extend_list_copies M pA copies.toList
  refine ⟨D, base, ?_⟩
  intro p hp
  exact h p (by simpa using hp)

/-- Attach an A-copy over every P-copy of B. -/
theorem extend_all_copies
    (M : AmalgamationSystem S)
    {P A B : S.Obj}
    (pA : S.Emb P A) :
    ∃ (D : S.Obj) (base : S.Emb B D),
      ∀ p : S.Copy P B,
        ∃ a : S.Copy A D,
          S.Subcopy (S.mapCopy base p) a := by
  classical
  obtain ⟨D, base, h⟩ :=
    extend_finite_copies M pA (Finset.univ : Finset (S.Copy P B))
  exact ⟨D, base, fun p => h p (Finset.mem_univ p)⟩

/-- The set of colours appearing on P-subcopies of one A-copy. -/
noncomputable def subcopyColourSet
    {P A C : S.Obj} {r : ℕ}
    (colouring : S.Copy P C → Fin r)
    (a : S.Copy A C) : Finset (Fin r) := by
  classical
  exact
    (Finset.univ.filter fun p : S.Copy P C => S.Subcopy p a).image colouring

/-- An A-copy contains at most as many P-colours as there are P-copies in A. -/
theorem subcopyColourSet_card_le
    {P A C : S.Obj} {r : ℕ}
    (colouring : S.Copy P C → Fin r)
    (a : S.Copy A C) :
    (subcopyColourSet (S := S) colouring a).card ≤
      Fintype.card (S.Copy P A) := by
  classical
  obtain ⟨f, hf⟩ := S.range_surjective a
  let transported : Finset (S.Copy P C) :=
    Finset.univ.image (S.mapCopy f)
  have hcopies :
      (Finset.univ.filter fun p : S.Copy P C => S.Subcopy p a) ⊆
        transported := by
    intro p hp
    have hsub : S.Subcopy p a := (Finset.mem_filter.mp hp).2
    rw [← hf] at hsub
    obtain ⟨q, hq⟩ := (S.subcopy_range_iff f p).mp hsub
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, hq⟩
  calc
    (subcopyColourSet (S := S) colouring a).card ≤
        (Finset.univ.filter fun p : S.Copy P C => S.Subcopy p a).card :=
      Finset.card_image_le
    _ ≤ transported.card := Finset.card_le_card hcopies
    _ ≤ (Finset.univ : Finset (S.Copy P A)).card :=
      Finset.card_image_le
    _ = Fintype.card (S.Copy P A) := Finset.card_univ

/-- Copy Ramsey degree propagates from a structure A to any substructure P.

If P embeds into A, A has copy Ramsey degree at most d, and there are s
P-copies in A, then P has copy Ramsey degree at most s*d.  This is the
abstract form of the circulation manuscript's degree-propagation lemma. -/
theorem copyRamseyDegreeLE_of_embedding
    (M : AmalgamationSystem S)
    {P A : S.Obj}
    (pA : S.Emb P A)
    {d : ℕ}
    (hA : S.CopyRamseyDegreeLE A d) :
    S.CopyRamseyDegreeLE P
      (Fintype.card (S.Copy P A) * d) := by
  classical
  intro B r hr

  obtain ⟨Bplus, base, hext⟩ :=
    extend_all_copies M pA

  let Palette := Finset (Fin r)
  let nPal := Fintype.card Palette
  have hnPal : 0 < nPal :=
    Fintype.card_pos_iff.mpr ⟨∅⟩

  obtain ⟨C, hC⟩ := hA Bplus nPal hnPal
  refine ⟨C, ?_⟩
  intro colouringP

  let paletteEquiv : Palette ≃ Fin nPal :=
    Fintype.equivFin Palette

  let colouringA : S.Copy A C → Fin nPal :=
    fun a => paletteEquiv (subcopyColourSet (S := S) colouringP a)

  obtain ⟨g, hg⟩ := hC colouringA

  let palettes : Finset Palette :=
    (S.coloursInside colouringA g).image paletteEquiv.symm

  have hpalettes_card : palettes.card ≤ d := by
    calc
      palettes.card ≤ (S.coloursInside colouringA g).card :=
        Finset.card_image_le
      _ ≤ d := hg

  have hpalette_size :
      ∀ T ∈ palettes, T.card ≤ Fintype.card (S.Copy P A) := by
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨z, hz, hTz⟩
    rcases Finset.mem_image.mp hz with ⟨a, ha, hza⟩
    have hT_eq :
        T = subcopyColourSet (S := S) colouringP (S.mapCopy g a) := by
      rw [← hTz, ← hza]
      simp [colouringA, paletteEquiv]
    rw [hT_eq]
    exact subcopyColourSet_card_le (S := S) colouringP (S.mapCopy g a)

  let allColours : Finset (Fin r) :=
    palettes.biUnion id

  have hallColours_card :
      allColours.card ≤ Fintype.card (S.Copy P A) * d := by
    calc
      allColours.card ≤ ∑ T ∈ palettes, T.card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _T ∈ palettes, Fintype.card (S.Copy P A) := by
        exact Finset.sum_le_sum hpalette_size
      _ = palettes.card * Fintype.card (S.Copy P A) := by
        rw [Finset.sum_const_nat]
        simp
      _ ≤ d * Fintype.card (S.Copy P A) :=
        Nat.mul_le_mul_right _ hpalettes_card
      _ = Fintype.card (S.Copy P A) * d := Nat.mul_comm _ _

  refine ⟨S.compEmb base g, ?_⟩
  unfold FiniteCopySystem.coloursInside
  apply le_trans (Finset.card_le_card ?_) hallColours_card
  intro colour hcolour
  rcases Finset.mem_image.mp hcolour with ⟨p, hp, rfl⟩

  obtain ⟨a, ha⟩ := hext p
  have hsub :
      S.Subcopy
        (S.mapCopy g (S.mapCopy base p))
        (S.mapCopy g a) :=
    subcopy_map (S := S) g ha

  have hcolour_mem_set :
      colouringP (S.mapCopy g (S.mapCopy base p)) ∈
        subcopyColourSet (S := S) colouringP (S.mapCopy g a) := by
    unfold subcopyColourSet
    apply Finset.mem_image.mpr
    refine ⟨S.mapCopy g (S.mapCopy base p), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub⟩

  have hpalette_mem :
      subcopyColourSet (S := S) colouringP (S.mapCopy g a) ∈ palettes := by
    apply Finset.mem_image.mpr
    refine ⟨colouringA (S.mapCopy g a), ?_, ?_⟩
    · unfold FiniteCopySystem.coloursInside
      apply Finset.mem_image.mpr
      exact ⟨a, Finset.mem_univ _, rfl⟩
    · simp [colouringA, paletteEquiv]

  have hcolour_union :
      colouringP (S.mapCopy g (S.mapCopy base p)) ∈ allColours := by
    exact Finset.mem_biUnion.mpr
      ⟨subcopyColourSet (S := S) colouringP (S.mapCopy g a),
        hpalette_mem, hcolour_mem_set⟩

  simpa only [S.mapCopy_comp] using hcolour_union


end AmalgamationSystem

structure RamseyExpansion (S : FiniteCopySystem) where
  Exp : S.Obj → Type x
  expFintype : ∀ A, Fintype (Exp A)
  expDecidableEq : ∀ A, DecidableEq (Exp A)
  expNonempty : ∀ A, Nonempty (Exp A)
  restrict : ∀ {A B}, S.Emb A B → Exp B → Exp A
  restrict_id :
    ∀ {A} (a : Exp A),
      restrict (S.idEmb A) a = a
  restrict_comp :
    ∀ {A B C} (f : S.Emb A B) (g : S.Emb B C) (c : Exp C),
      restrict (S.compEmb f g) c =
        restrict f (restrict g c)
  ramsey :
    ∀ {A B : S.Obj}
      (a : Exp A) (b : Exp B)
      (r : ℕ), 0 < r →
      ∃ (C : S.Obj) (c : Exp C),
        ∀ colouring :
            { f : S.Emb A C // restrict f c = a } → Fin r,
          ∃ g : { g : S.Emb B C // restrict g c = b },
            ∀ e₁ e₂ :
                { e : S.Emb A B // restrict e b = a },
              colouring
                  ⟨S.compEmb e₁.1 g.1, by
                    rw [restrict_comp, g.2, e₁.2]⟩ =
                colouring
                  ⟨S.compEmb e₂.1 g.1, by
                    rw [restrict_comp, g.2, e₂.2]⟩

namespace RamseyExpansion

variable {S : FiniteCopySystem} (E : RamseyExpansion S)

attribute [local instance] FiniteCopySystem.copyFintype
attribute [local instance] FiniteCopySystem.copyDecidableEq

local instance instExpansionFintype (A : S.Obj) : Fintype (E.Exp A) :=
  E.expFintype A

local instance instExpansionDecidableEq (A : S.Obj) : DecidableEq (E.Exp A) :=
  E.expDecidableEq A

abbrev ExpEmb
    {A B : S.Obj} (a : E.Exp A) (b : E.Exp B) :=
  { f : S.Emb A B // E.restrict f b = a }

def idExp
    {A : S.Obj} (a : E.Exp A) :
    E.ExpEmb a a :=
  ⟨S.idEmb A, E.restrict_id a⟩

def compExp
    {A B C : S.Obj}
    {a : E.Exp A} {b : E.Exp B} {c : E.Exp C}
    (f : E.ExpEmb a b) (g : E.ExpEmb b c) :
    E.ExpEmb a c :=
  ⟨S.compEmb f.1 g.1, by
    rw [E.restrict_comp, g.2, f.2]⟩

@[simp] theorem compExp_val
    {A B C : S.Obj}
    {a : E.Exp A} {b : E.Exp B} {c : E.Exp C}
    (f : E.ExpEmb a b) (g : E.ExpEmb b c) :
    (E.compExp f g).1 = S.compEmb f.1 g.1 := rfl

theorem simultaneous_ramsey
    {A B : S.Obj}
    (types : Finset (E.Exp A))
    (b : E.Exp B)
    (r : ℕ) (hr : 0 < r) :
    ∃ (C : S.Obj) (c : E.Exp C),
      ∀ colour :
          ∀ a : E.Exp A, E.ExpEmb a c → Fin r,
        ∃ g : E.ExpEmb b c,
          ∀ a ∈ types,
            ∀ e₁ e₂ : E.ExpEmb a b,
              colour a (E.compExp e₁ g) =
                colour a (E.compExp e₂ g) := by
  classical
  induction types using Finset.induction_on with
  | empty =>
      refine ⟨B, b, ?_⟩
      intro colour
      refine ⟨E.idExp b, ?_⟩
      simp
  | @insert a types ha ih =>
      obtain ⟨D, d, hD⟩ := ih
      obtain ⟨C, c, hC⟩ := E.ramsey a d r hr
      refine ⟨C, c, ?_⟩
      intro colour
      obtain ⟨h, hh⟩ := hC (colour a)
      let pulled :
          ∀ x : E.Exp A, E.ExpEmb x d → Fin r :=
        fun x e => colour x (E.compExp e h)
      obtain ⟨g, hg⟩ := hD pulled
      refine ⟨E.compExp g h, ?_⟩
      intro x hx e₁ e₂
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · have hmono := hh (E.compExp e₁ g) (E.compExp e₂ g)
        simpa [pulled, compExp, S.comp_assoc] using hmono
      · have hmono := hg x hx e₁ e₂
        simpa [pulled, compExp, S.comp_assoc] using hmono

theorem copyRamseyDegreeLE_card_expansionTypes
    (A : S.Obj) :
    S.CopyRamseyDegreeLE A (Fintype.card (E.Exp A)) := by
  classical
  intro B r hr
  let b : E.Exp B := Classical.choice (E.expNonempty B)
  obtain ⟨C, c, hsim⟩ :=
    E.simultaneous_ramsey (Finset.univ : Finset (E.Exp A)) b r hr
  refine ⟨C, ?_⟩
  intro colouring

  let expandedColour :
      ∀ a : E.Exp A, E.ExpEmb a c → Fin r :=
    fun _ e => colouring (S.range e.1)

  obtain ⟨g, hg⟩ := hsim expandedColour

  let rep : S.Copy A B → S.Emb A B :=
    fun p => Classical.choose (S.range_surjective p)
  have hrep (p : S.Copy A B) :
      S.range (rep p) = p :=
    Classical.choose_spec (S.range_surjective p)

  let copyType : S.Copy A B → E.Exp A :=
    fun p => E.restrict (rep p) b

  let colourOn : S.Copy A B → Fin r :=
    fun p => colouring (S.mapCopy g.1 p)

  have hsame
      (p q : S.Copy A B)
      (hpq : copyType p = copyType q) :
      colourOn p = colourOn q := by
    let ep : E.ExpEmb (copyType p) b :=
      ⟨rep p, rfl⟩
    let eq' : E.ExpEmb (copyType p) b :=
      ⟨rep q, hpq.symm⟩
    have hhom :=
      hg (copyType p) (Finset.mem_univ _) ep eq'
    change
      colouring (S.mapCopy g.1 p) =
        colouring (S.mapCopy g.1 q)
    simpa [expandedColour, ep, eq', S.range_comp, hrep] using hhom

  let colourByType : E.Exp A → Fin r :=
    fun a =>
      if h : ∃ p : S.Copy A B, copyType p = a then
        colourOn (Classical.choose h)
      else
        ⟨0, hr⟩

  have hfactor (p : S.Copy A B) :
      colourOn p = colourByType (copyType p) := by
    have hex : ∃ q : S.Copy A B, copyType q = copyType p :=
      ⟨p, rfl⟩
    rw [show colourByType (copyType p) =
        colourOn (Classical.choose hex) by
          simp [colourByType, hex]]
    exact hsame p (Classical.choose hex)
      (Classical.choose_spec hex).symm

  refine ⟨g.1, ?_⟩
  unfold FiniteCopySystem.coloursInside
  have hsubset :
      Finset.univ.image colourOn ⊆
        Finset.univ.image colourByType := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨copyType p, Finset.mem_univ _, ?_⟩
    exact (hfactor p).symm
  calc
    (Finset.univ.image
        (fun p : S.Copy A B =>
          colouring (S.mapCopy g.1 p))).card =
        (Finset.univ.image colourOn).card := rfl
    _ ≤ (Finset.univ.image colourByType).card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.univ : Finset (E.Exp A)).card :=
      Finset.card_image_le
    _ = Fintype.card (E.Exp A) := Finset.card_univ

end RamseyExpansion

end SuccessorTree

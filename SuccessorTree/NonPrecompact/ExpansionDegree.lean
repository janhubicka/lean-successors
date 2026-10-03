/-!
# Finite expansion types bound copy Ramsey degrees

This file formalises the abstract combinatorial argument of
`lem:expansion-degree-bound` in the BANANA circulation manuscript.

The intended interpretation is:

* `Obj` is the class of finite expanded structures;
* `Ty` is the finite set of expansion isomorphism types of one fixed
  reduct source `A`;
* `ExpEmb τ X` is the type of embeddings of a representative of expansion
  type `τ` into the expanded structure `X`;
* `Copy X` is the type of reduct copies of `A` in the reduct of `X`.

The axioms below isolate exactly what the manuscript proof uses.  The
expanded class has the embedding Ramsey property for each source expansion
type.  Heredity says every reduct copy in an expanded structure inherits
some expansion type, expressed by `liftCopy`.  Forgetting an expanded
embedding commutes with composition.

The main theorem first proves the finite-family version of the Ramsey
property by successive applications of the one-source property.  It then
colours each expanded embedding by the colour of its reduct range.  On the
resulting target copy the colour depends only on the expansion type, hence
at most `|Ty|` colours occur.

No rigidity assumption on the reduct source is used.
-/

namespace SuccessorTree.NonPrecompact

/-- Abstract embedding/action data needed to iterate Ramsey witnesses for a
finite family of source expansion types. -/
structure ExpansionEmbeddingSystem (Obj Ty : Type*) where
  Emb : Obj → Obj → Type*
  ExpEmb : Ty → Obj → Type*
  id : ∀ X, Emb X X
  comp : ∀ {X Y Z}, Emb X Y → Emb Y Z → Emb X Z
  act : ∀ {τ X Y}, Emb X Y → ExpEmb τ X → ExpEmb τ Y
  act_comp :
    ∀ {τ X Y Z} (f : Emb X Y) (g : Emb Y Z) (e : ExpEmb τ X),
      act (comp f g) e = act g (act f e)

/-- The ordinary embedding Ramsey property for one fixed expanded source
type `τ`. -/
def ExpansionEmbeddingSystem.RamseyFor
    {Obj Ty : Type*}
    (S : ExpansionEmbeddingSystem Obj Ty)
    (τ : Ty) : Prop :=
  ∀ (B : Obj) (numColours : ℕ), 0 < numColours →
    ∃ C : Obj,
      ∀ colouring : S.ExpEmb τ C → Fin numColours,
        ∃ f : S.Emb B C,
          ∃ colour : Fin numColours,
            ∀ e : S.ExpEmb τ B,
              colouring (S.act f e) = colour

namespace ExpansionEmbeddingSystem

variable {Obj Ty : Type*}
variable (S : ExpansionEmbeddingSystem Obj Ty)

/-- Successively applying the one-source Ramsey property homogenises any
finite list of expanded source types simultaneously. -/
theorem ramseyForList
    (hRamsey : ∀ τ, S.RamseyFor τ)
    (types : List Ty)
    (B : Obj) (numColours : ℕ) (hColours : 0 < numColours) :
    ∃ C : Obj,
      ∀ colouring : ∀ τ, S.ExpEmb τ C → Fin numColours,
        ∃ f : S.Emb B C,
          ∀ τ ∈ types,
            ∃ colour : Fin numColours,
              ∀ e : S.ExpEmb τ B,
                colouring τ (S.act f e) = colour := by
  induction types generalizing B with
  | nil =>
      refine ⟨B, ?_⟩
      intro colouring
      refine ⟨S.id B, ?_⟩
      intro τ hτ
      simp at hτ
  | cons τ types ih =>
      obtain ⟨D, hD⟩ := ih B
      obtain ⟨C, hC⟩ :=
        hRamsey τ D numColours hColours
      refine ⟨C, ?_⟩
      intro colouring
      obtain ⟨h, colourτ, hmonoτ⟩ :=
        hC (colouring τ)
      let pulled :
          ∀ σ, S.ExpEmb σ D → Fin numColours :=
        fun σ e => colouring σ (S.act h e)
      obtain ⟨g, hmonoTypes⟩ := hD pulled
      refine ⟨S.comp g h, ?_⟩
      intro σ hσ
      rcases List.mem_cons.mp hσ with hστ | hσtypes
      · subst σ
        refine ⟨colourτ, ?_⟩
        intro e
        rw [S.act_comp]
        exact hmonoτ (S.act g e)
      · obtain ⟨colourσ, hmonoσ⟩ :=
          hmonoTypes σ hσtypes
        refine ⟨colourσ, ?_⟩
        intro e
        rw [S.act_comp]
        exact hmonoσ e

/-- Finite-family Ramsey homogenisation for all source expansion types. -/
theorem ramseyForAll
    [Fintype Ty] [DecidableEq Ty]
    (hRamsey : ∀ τ, S.RamseyFor τ)
    (B : Obj) (numColours : ℕ) (hColours : 0 < numColours) :
    ∃ C : Obj,
      ∀ colouring : ∀ τ, S.ExpEmb τ C → Fin numColours,
        ∃ f : S.Emb B C,
          ∀ τ,
            ∃ colour : Fin numColours,
              ∀ e : S.ExpEmb τ B,
                colouring τ (S.act f e) = colour := by
  obtain ⟨C, hC⟩ :=
    S.ramseyForList hRamsey Finset.univ.toList
      B numColours hColours
  refine ⟨C, ?_⟩
  intro colouring
  obtain ⟨f, hf⟩ := hC colouring
  refine ⟨f, ?_⟩
  intro τ
  exact hf τ (by simp)

end ExpansionEmbeddingSystem

/-- Add reduct-copy data to the expanded embedding system.

The two compatibility fields formalise the hereditary induced-expansion
argument: every reduct copy has at least one expanded lift, and forgetting
the range of an expanded embedding commutes with postcomposition. -/
structure ExpansionCopySystem (Obj Ty : Type*)
    extends ExpansionEmbeddingSystem Obj Ty where
  Copy : Obj → Type*
  copyAct : ∀ {X Y}, Emb X Y → Copy X → Copy Y
  forgetRange : ∀ {τ X}, ExpEmb τ X → Copy X
  forget_act :
    ∀ {τ X Y} (f : Emb X Y) (e : ExpEmb τ X),
      forgetRange (act f e) = copyAct f (forgetRange e)
  liftCopy :
    ∀ (X : Obj) (copy : Copy X),
      ∃ τ : Ty, ∃ e : ExpEmb τ X,
        forgetRange e = copy

namespace ExpansionCopySystem

variable {Obj Ty : Type*}
variable (S : ExpansionCopySystem Obj Ty)

/-- Copy-Ramsey-degree bound in the expanded-object presentation.

For every expanded target `B` and every finite colouring of reduct source
copies, some expanded `B`-copy sees at most `t` colours.  Since every
reduct target has an expansion in an expansion class, this is the finite
combinatorial content of the usual reduct copy-degree statement. -/
def CopyDegreeLE (t : ℕ) : Prop :=
  ∀ (B : Obj) (numColours : ℕ), 0 < numColours →
    ∃ C : Obj,
      ∀ colouring : S.Copy C → Fin numColours,
        ∃ f : S.Emb B C,
          ∃ colours : Finset (Fin numColours),
            colours.card ≤ t ∧
            ∀ copy : S.Copy B,
              colouring (S.copyAct f copy) ∈ colours

/-- A finite Ramsey expansion with `|Ty|` source expansion types bounds the
copy Ramsey degree by `|Ty|`.

This is the formal counterpart of manuscript
`lem:expansion-degree-bound`. -/
theorem copyDegreeLE_card_expansionTypes
    [Fintype Ty] [DecidableEq Ty]
    (hRamsey : ∀ τ, S.toExpansionEmbeddingSystem.RamseyFor τ) :
    S.CopyDegreeLE (Fintype.card Ty) := by
  intro B numColours hColours
  obtain ⟨C, hC⟩ :=
    S.toExpansionEmbeddingSystem.ramseyForAll
      hRamsey B numColours hColours
  refine ⟨C, ?_⟩
  intro colouring

  let expandedColour :
      ∀ τ, S.ExpEmb τ C → Fin numColours :=
    fun τ e => colouring (S.forgetRange e)

  obtain ⟨f, hmono⟩ := hC expandedColour

  have hconst :
      ∀ τ : Ty,
        ∃ colour : Fin numColours,
          ∀ e : S.ExpEmb τ B,
            expandedColour τ (S.act f e) = colour :=
    hmono

  choose chosen hchosen using hconst

  let colours : Finset (Fin numColours) :=
    Finset.univ.image chosen

  have hcard :
      colours.card ≤ Fintype.card Ty := by
    calc
      colours.card ≤ (Finset.univ : Finset Ty).card := by
        exact Finset.card_image_le
      _ = Fintype.card Ty := Finset.card_univ

  refine ⟨f, colours, hcard, ?_⟩
  intro copy
  obtain ⟨τ, e, he⟩ := S.liftCopy B copy
  have hm := hchosen τ e
  change
    colouring (S.forgetRange (S.act f e)) =
      chosen τ at hm
  rw [S.forget_act, he] at hm
  exact Finset.mem_image.mpr
    ⟨τ, Finset.mem_univ τ, hm.symm⟩

/-- Version with a named numerical bound `t`. -/
theorem copyDegreeLE_of_card_expansionTypes_eq
    [Fintype Ty] [DecidableEq Ty]
    (hRamsey : ∀ τ, S.toExpansionEmbeddingSystem.RamseyFor τ)
    {t : ℕ} (ht : Fintype.card Ty = t) :
    S.CopyDegreeLE t := by
  simpa [ht] using S.copyDegreeLE_card_expansionTypes hRamsey

end ExpansionCopySystem

end SuccessorTree.NonPrecompact

import SuccessorTree.Pigeonhole

/-!
# Ramsey-first validation of the weak block axioms

The only tree-dependent input to this module is the colour-free seeded
realisation equation of manuscript M4. In an actual successor monoid,
`wordApprox` is the product of canonical completions of the designated
letters, and `apply` is restriction/composition with a two-level block.

No SMTree, M2', M3', decomposition, fusion, envelope, or abstract Ramsey
space instance is imported or assumed. In particular, the covered-front
result below does NOT assert that the manuscript's local axioms supply
its separate coverage and common-base hypotheses.
-/

namespace SuccessorTree.Block

universe u v w x y z

variable {Γ : Type u} {Approx : Type v} {Block : Type w}
  {κ : Type x} {ι : Type y} {Point : Type z}

/-- Literal existential M4 data. The seed precedes the choice of a line;
one admissible block works for its base and all letter substitutions. -/
def HasSeededRealisation
    (wordApprox : List Γ → Approx)
    (apply : Block → LineInput Γ → Approx) : Prop :=
  ∃ seed : List Γ, ∀ L : StarLine Γ, ∃ b : Block,
    apply b .base = wordApprox (seed ++ L.star) ∧
    ∀ e : Γ, apply b (.letter e) = wordApprox (seed ++ L.eval e)

/-- The local block pigeonhole theorem with Hales--Jewett discharged.
The input is a realization property, not a Ramsey hypothesis. -/
theorem seededPigeonhole
    [Fintype Γ] [Fintype κ]
    (wordApprox : List Γ → Approx)
    (apply : Block → LineInput Γ → Approx)
    (hRealise : HasSeededRealisation wordApprox apply)
    (colour : Approx → κ) :
    ∃ b : Block, ∀ a : LineInput Γ,
      colour (apply b a) = colour (apply b .base) := by
  obtain ⟨seed, hSeed⟩ := hRealise
  obtain ⟨L, hL⟩ :=
    (HalesJewett.starHJ_finite (α := Γ) (κ := κ))
      (fun w => colour (wordApprox (seed ++ w)))
  obtain ⟨b, hBase, hLetter⟩ := hSeed L
  refine ⟨b, ?_⟩
  intro a
  cases a with
  | base => rfl
  | letter e =>
      rw [hLetter e, hBase]
      exact hL e

/-- Pairwise form, including the starred member of the line. -/
theorem seededPigeonhole_pairwise
    [Fintype Γ] [Fintype κ]
    (wordApprox : List Γ → Approx)
    (apply : Block → LineInput Γ → Approx)
    (hRealise : HasSeededRealisation wordApprox apply)
    (colour : Approx → κ) :
    ∃ b : Block, ∀ a a' : LineInput Γ,
      colour (apply b a) = colour (apply b a') := by
  obtain ⟨b, hb⟩ := seededPigeonhole wordApprox apply hRealise colour
  exact ⟨b, fun a a' => (hb a).trans (hb a').symm⟩

/-- One block works for an entire finite batch of profile colourings.
Separate blocks for separate profiles would not suffice. -/
theorem finiteProfilePigeonhole
    [Fintype Γ] [Fintype κ] [Fintype ι]
    (wordApprox : List Γ → Approx)
    (apply : Block → LineInput Γ → Approx)
    (hRealise : HasSeededRealisation wordApprox apply)
    (profile : ι → Approx → Point)
    (colour : Point → κ) :
    ∃ b : Block, ∀ i : ι, ∀ a : LineInput Γ,
      colour (profile i (apply b a)) =
        colour (profile i (apply b .base)) := by
  classical
  obtain ⟨b, hb⟩ := seededPigeonhole
    (κ := ι → κ) wordApprox apply hRealise
    (fun t i => colour (profile i t))
  refine ⟨b, ?_⟩
  intro i a
  exact congrFun (hb a) i

/-- A conditional all-front bridge. Coverage concerns EVERY member of
`front b`, and all profiles must share one base. These are explicit,
colour-free hypotheses, not consequences of local M4.

This is a sufficient local bridge only. No persistence under refinement
or global fat-tree A4 is asserted here. -/
theorem coveredFrontPigeonhole
    [Fintype Γ] [Fintype κ] [Fintype ι]
    (wordApprox : List Γ → Approx)
    (apply : Block → LineInput Γ → Approx)
    (hRealise : HasSeededRealisation wordApprox apply)
    (profile : ι → Approx → Point)
    (front : Block → Set Point) (anchor : Block → Point)
    (hCover : ∀ b t, t ∈ front b →
      ∃ i : ι, ∃ a : LineInput Γ, profile i (apply b a) = t)
    (hBase : ∀ b i, profile i (apply b .base) = anchor b)
    (colour : Point → κ) :
    ∃ b : Block, ∀ t ∈ front b, colour t = colour (anchor b) := by
  obtain ⟨b, hb⟩ := finiteProfilePigeonhole
    wordApprox apply hRealise profile colour
  refine ⟨b, ?_⟩
  intro t ht
  obtain ⟨i, a, heq⟩ := hCover b t ht
  rw [← heq, hb i a, hBase b i]

/-- The previously proved supported-replay interface implies the new
seeded interface. This adapter uses a supported prefix, not unseeded
realisation, and does not rebuild the strong tree construction. -/
theorem hasSeededRealisation_of_replay
    [Fintype Γ] (sys : ReplaySystem Γ Approx Block) :
    HasSeededRealisation sys.wordApprox sys.apply := by
  classical
  let seed := fullSupport Γ
  refine ⟨seed, ?_⟩
  intro L
  have hSupport : Supports (L.prepend seed).star := by
    intro e
    exact support_mem_star_prepend seed L (supports_fullSupport Γ) e
  refine ⟨sys.replay (L.prepend seed) hSupport, ?_, ?_⟩
  · simpa using sys.replay_base (L.prepend seed) hSupport
  · intro e
    simpa using sys.replay_letter (L.prepend seed) hSupport e

/-!
## Regression: a nonempty alphabet is not an all-front coverage proof

This finite example is a counterexample only to dropping coverage from
this abstract interface. It is NOT advertised as a successor monoid.
The manuscript's parity monoid supplies the separate monoid obstruction.
-/

/-- A nonempty singleton alphabet can realise every line while seeing
only the point `false`. -/
theorem singletonRealisation :
    HasSeededRealisation
      (fun _ : List Unit => false)
      (fun _ : Unit => fun _ : LineInput Unit => false) := by
  refine ⟨[], ?_⟩
  intro L
  exact ⟨(), rfl, fun _ => rfl⟩

/-- Enlarging that represented front to all Boolean points destroys
homogeneity for the identity colouring. -/
theorem fullFront_not_homogeneous :
    ¬ ∃ _b : Unit, ∃ c : Bool,
      ∀ t ∈ (Set.univ : Set Bool), t = c := by
  rintro ⟨b, c, hc⟩
  have h : (false : Bool) = true :=
    (hc false (Set.mem_univ false)).trans
      (hc true (Set.mem_univ true)).symm
  cases h

end SuccessorTree.Block

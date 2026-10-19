import SuccessorTree.ShapeFiniteRamsey

/-!
# Ramsey theorem for restrictions to a bounded source configuration

The finite-dimensional shape Ramsey theorem also colours the restrictions
of monoid maps to any fixed configuration whose source levels are bounded.
The restriction is the actual function, with no chosen total extension as
part of the coloured data. This is the reusable pullback used in the binary
type-respecting application.

The identification of an intrinsic class of partial maps with these
restrictions is a separate mathematical theorem of each application.
-/

namespace SuccessorTree.SMTree

universe u v w z

variable {T : Type u} {Label : Type v} {P : Type w}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

/-- Actual functions induced on a fixed source configuration by monoid maps.
Different total extensions give the same object when their restrictions agree. -/
def Restriction (H : SMTree S) (source : P → T) :=
  {f : P → T // ∃ F : MMap H, f = fun x => F (source x)}

namespace Restriction

/-- Restrict a total monoid map to the given configuration. -/
def ofMap (H : SMTree S) (source : P → T) (F : MMap H) :
    Restriction H source :=
  ⟨fun x => F (source x), F, rfl⟩

@[simp] theorem ofMap_apply (H : SMTree S) (source : P → T)
    (F : MMap H) (x : P) :
    (ofMap H source F).1 x = F (source x) := rfl

/-- Postcompose the actual partial function; no representative is chosen. -/
def act (H : SMTree S) (source : P → T)
    (F : MMap H) (f : Restriction H source) : Restriction H source := by
  refine ⟨fun x => F (f.1 x), ?_⟩
  obtain ⟨G, hG⟩ := f.2
  exact ⟨MMap.comp H F G, by rw [hG]; rfl⟩

@[simp] theorem act_apply (H : SMTree S) (source : P → T)
    (F : MMap H) (f : Restriction H source) (x : P) :
    (act H source F f).1 x = F (f.1 x) := rfl

@[simp] theorem act_ofMap (H : SMTree S) (source : P → T)
    (F G : MMap H) :
    act H source F (ofMap H source G) =
      ofMap H source (MMap.comp H F G) := by
  apply Subtype.ext
  rfl

@[simp] theorem act_id (H : SMTree S) (source : P → T)
    (f : Restriction H source) :
    act H source (MMap.id H) f = f := by
  apply Subtype.ext
  rfl

theorem act_comp (H : SMTree S) (source : P → T)
    (F G : MMap H) (f : Restriction H source) :
    act H source (MMap.comp H F G) f =
      act H source F (act H source G f) := by
  apply Subtype.ext
  rfl

/-- Restrict the representative of a finite approximation. The bound below
is used to prove that this restriction is independent of the representative. -/
noncomputable def ofApprox (H : SMTree S) (source : P → T)
    {n k : Nat} (g : AM H n k) : Restriction H source :=
  ofMap H source (g.representative H)

theorem ofApprox_toAM (H : SMTree S) (source : P → T)
    (n k : Nat) (bounded : ∀ x, LevelTree.lev (source x) < n + k)
    (F : MMap H) (fixes : F.FixesBelow H n) :
    ofApprox H source (F.toAM H n k fixes) = ofMap H source F := by
  apply Subtype.ext
  funext x
  exact MMap.toAM_representative_agrees H F n k fixes (source x) (bounded x)

theorem ofApprox_shapeActK (H : SMTree S) (source : P → T)
    (n k : Nat) (bounded : ∀ x, LevelTree.lev (source x) < n + k)
    (F : ShapeSubspace H n) (g : AM H n k) :
    ofApprox H source (H.shapeActK n k F g) =
      act H source F.1 (ofApprox H source g) := by
  apply Subtype.ext
  funext x
  exact H.shapeActK_representative_agrees n k F g (source x) (bounded x)

end Restriction

/-- A fixed bounded configuration has Ramsey degree one for its restrictions
of monoid maps. This includes an empty source and arbitrary finite colour types. -/
theorem boundedRestrictionRamsey
    {κ : Type z} [Fintype κ]
    (H : SMTree S) (source : P → T)
    (k : Nat) (bounded : ∀ x, LevelTree.lev (source x) < k)
    (colour : Restriction H source → κ) :
    ∃ F : MMap H, ∀ f g : Restriction H source,
      colour (Restriction.act H source F f) =
        colour (Restriction.act H source F g) := by
  classical
  obtain ⟨F, hF⟩ := H.shapePreservingRamsey 0 k
    (fun a => colour (Restriction.ofApprox H source a))
  refine ⟨F.1, ?_⟩
  intro f g
  obtain ⟨G, hG⟩ := f.2
  obtain ⟨K, hK⟩ := g.2
  have hf : f = Restriction.ofMap H source G := Subtype.ext hG
  have hg : g = Restriction.ofMap H source K := Subtype.ext hK
  subst f
  subst g
  have Gfix : G.FixesBelow H 0 := by intro x hx; omega
  have Kfix : K.FixesBelow H 0 := by intro x hx; omega
  have bound : ∀ x, LevelTree.lev (source x) < 0 + k := by
    simpa using bounded
  have homogeneous := hF (G.toAM H 0 k Gfix) (K.toAM H 0 k Kfix)
  rw [Restriction.ofApprox_shapeActK H source 0 k bound,
    Restriction.ofApprox_shapeActK H source 0 k bound,
    Restriction.ofApprox_toAM H source 0 k bound,
    Restriction.ofApprox_toAM H source 0 k bound] at homogeneous
  exact homogeneous

end SuccessorTree.SMTree

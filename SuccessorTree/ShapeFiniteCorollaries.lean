import SuccessorTree.ShapeFiniteBounds

/-!
# Finite corollaries of the shape-preserving Ramsey theorem

The first corollary is the compactness consequence used in the manuscript.
The exact-terminal version is proved afterwards by a common M3 padding.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Composition of a bounded witness with a coordinate ending before the
witness source segment stays below the same ambient bound. -/
noncomputable def boundedComp
    (H : SMTree S) {n m k N : Nat}
    (hm : 0 < m) (hk : 0 < k)
    (f : AM.AtMost H n m N)
    (g : AM.Below H n k (n + m)) :
    AM.AtMost H n k N :=
  ⟨finiteShapeComp H f.1 g.1,
    (finiteShapeComp_terminalLevel_le H hm hk f.1 g.1 g.2).trans f.2⟩

/-- If a total subspace is truncated after m moving levels, composing the
truncation with a coordinate ending before n+m gives the same finite map as
the total shape action. -/
theorem finiteShapeComp_toAM_eq_shapeActK
    (H : SMTree S) {n m k : Nat}
    (hm : 0 < m) (hk : 0 < k)
    (W : ShapeSubspace H n)
    (g : AM H n k)
    (hg : g.terminalLevel H < n + m) :
    finiteShapeComp H (W.1.toAM H n m W.2) g =
      H.shapeActK n k W g := by
  apply Subtype.ext
  unfold finiteShapeComp shapeActK
  apply Subtype.ext
  apply ramseyApprox_eq_of_apply H
  intro x hx
  change
    (W.1.toAM H n m W.2).representative H
        (g.representative H x) =
      W.1 (g.representative H x)
  apply MMap.toAM_representative_agrees H W.1 n m W.2
  exact lt_of_le_of_lt
    (g.level_le_terminalLevel H hx) hg

/-- The bounded finite Ramsey conclusion at a fixed ambient level. -/
def BoundedRamseyAt
    (H : SMTree S) (κ : Type w) (n k m N : Nat)
    (hm : 0 < m) (hk : 0 < k) : Prop :=
  ∀ colour : AM.AtMost H n k N → κ,
    ∃ f : AM.AtMost H n m N,
      ∀ g h : AM.Below H n k (n + m),
        colour (boundedComp H hm hk f g) =
          colour (boundedComp H hm hk f h)

/-- Corollary 1.7: for every finite number of colours there is a finite
ambient terminal bound which already witnesses the finite-dimensional Ramsey
theorem. -/
theorem shapeRamsey_bounded
    {κ : Type w} [Fintype κ] [Nonempty κ]
    (H : SMTree S) (n k m : Nat)
    (hk : 0 < k) (hm : 0 < m) :
    ∃ N : Nat, BoundedRamseyAt H κ n k m N hm hk := by
  classical
  by_contra hno
  push_neg at hno

  let BadColour : Nat → Type max u w :=
    fun N =>
      {c : AM.AtMost H n k N → κ //
        ∀ f : AM.AtMost H n m N,
          ∃ g h : AM.Below H n k (n + m),
            c (boundedComp H hm hk f g) ≠
              c (boundedComp H hm hk f h)}

  have hbad (N : Nat) :
      ∃ c : AM.AtMost H n k N → κ,
        ∀ f : AM.AtMost H n m N,
          ∃ g h : AM.Below H n k (n + m),
            c (boundedComp H hm hk f g) ≠
              c (boundedComp H hm hk f h) := by
    by_contra h
    push_neg at h
    exact hno N h

  letI : ∀ N : Nat, Nonempty (BadColour N) :=
    fun N => ⟨⟨Classical.choose (hbad N), Classical.choose_spec (hbad N)⟩⟩

  letI : ∀ N : Nat, Finite (AM.AtMost H n k N) :=
    fun N => AM.atMost_finite (T := T) H (by omega)

  letI : ∀ N : Nat, Finite (AM.AtMost H n m N) :=
    fun N => AM.atMost_finite (T := T) H (by omega)

  letI : ∀ N : Nat, Finite (BadColour N) :=
    fun N =>
      Finite.of_injective
        (fun c : BadColour N => c.1)
        (by
          intro a b hab
          exact Subtype.ext hab)

  let proj : {i j : Nat} → i ≤ j → BadColour j → BadColour i :=
    fun {i j} hij c =>
      ⟨fun a => c.1 ⟨a.1, a.2.trans hij⟩, by
        intro f
        let fj : AM.AtMost H n m j := ⟨f.1, f.2.trans hij⟩
        obtain ⟨g, h, hne⟩ := c.2 fj
        refine ⟨g, h, ?_⟩
        simpa [boundedComp, fj] using hne⟩

  have hproj_refl :
      ∀ ⦃i⦄ (a : BadColour i), proj (le_refl i) a = a := by
    intro i a
    apply Subtype.ext
    funext x
    rfl

  have hproj_trans :
      ∀ ⦃i j l⦄ (hij : i ≤ j) (hjl : j ≤ l) (a : BadColour l),
        proj hij (proj hjl a) = proj (hij.trans hjl) a := by
    intro i j l hij hjl a
    apply Subtype.ext
    funext x
    rfl

  have hfin :
      ∀ i a, {b : BadColour (i + 1) |
        proj (Nat.le_add_right i 1) b = a}.Finite := by
    intro i a
    exact Set.toFinite _

  obtain ⟨seq, hseq⟩ :=
    exists_seq_forall_proj_of_forall_finite
      (α := BadColour) proj hproj_refl hproj_trans hfin

  have hcoh {i j : Nat} (hij : i ≤ j)
      (a : AM.AtMost H n k i) :
      (seq j).1 ⟨a.1, a.2.trans hij⟩ = (seq i).1 a := by
    have h := congrArg
      (fun c : BadColour i => c.1 a)
      (hseq hij)
    exact h

  let globalColour : AM H n k → κ :=
    fun a => (seq (a.terminalLevel H)).1 ⟨a, le_rfl⟩

  obtain ⟨W, hW⟩ :=
    H.shapePreservingRamsey n k globalColour

  let f0 : AM H n m := W.1.toAM H n m W.2
  let N : Nat := f0.terminalLevel H
  let f : AM.AtMost H n m N := ⟨f0, le_rfl⟩

  obtain ⟨g, h, hbadN⟩ := (seq N).2 f

  have hfinite (q : AM.Below H n k (n + m)) :
      finiteShapeComp H f0 q.1 =
        H.shapeActK n k W q.1 :=
    finiteShapeComp_toAM_eq_shapeActK H hm hk W q.1 q.2

  have hbound (q : AM.Below H n k (n + m)) :
      (finiteShapeComp H f0 q.1).terminalLevel H ≤ N :=
    finiteShapeComp_terminalLevel_le H hm hk f0 q.1 q.2

  have hglobal (q : AM.Below H n k (n + m)) :
      globalColour (finiteShapeComp H f0 q.1) =
        (seq N).1 (boundedComp H hm hk f q) := by
    let a : AM.AtMost H n k
        ((finiteShapeComp H f0 q.1).terminalLevel H) :=
      ⟨finiteShapeComp H f0 q.1, le_rfl⟩
    have hc := hcoh (hbound q) a
    exact hc.symm

  apply hbadN
  calc
    (seq N).1 (boundedComp H hm hk f g) =
        globalColour (finiteShapeComp H f0 g.1) := (hglobal g).symm
    _ = globalColour (H.shapeActK n k W g.1) := by rw [hfinite g]
    _ = globalColour (H.shapeActK n k W h.1) := hW g.1 h.1
    _ = globalColour (finiteShapeComp H f0 h.1) := by rw [hfinite h]
    _ = (seq N).1 (boundedComp H hm hk f h) := hglobal h

end SMTree
end SuccessorTree

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
  apply AM.ramseyApprox_eq_of_apply H
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
  push Not at hno

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
    push Not at h
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


/-! ## Exact terminal padding -/

private theorem padding_levelMap_comp
    (H : SMTree S) (F G : MMap H) (q : Nat) :
    H.levelMap (MMap.comp H F G).map q =
      H.levelMap F.map (H.levelMap G.map q) := by
  obtain ⟨x, hx⟩ := H.level_nonempty q
  calc
    H.levelMap (MMap.comp H F G).map q =
        LevelTree.lev (F (G x)) := by
      simpa [hx] using
        H.levelMap_eq (MMap.comp H F G).map (a := x)
    _ = H.levelMap F.map (LevelTree.lev (G x)) :=
      (H.levelMap_eq F.map (a := G x)).symm
    _ = H.levelMap F.map (H.levelMap G.map q) := by
      have hG := H.levelMap_eq G.map (a := x)
      rw [hx] at hG
      rw [hG]

private theorem padding_levelMap_id
    (H : SMTree S) (q : Nat) :
    H.levelMap (MMap.id H).map q = q := by
  obtain ⟨x, hx⟩ := H.level_nonempty q
  calc
    H.levelMap (MMap.id H).map q =
        LevelTree.lev ((MMap.id H) x) := by
      simpa [hx] using H.levelMap_eq (MMap.id H).map (a := x)
    _ = LevelTree.lev x := rfl
    _ = q := hx

/-- The M3 factor which inserts one target level at t. -/
noncomputable def paddingLetter
    (H : SMTree S) (t : Nat) (ht : 0 < t) :
    OneLevelLetter H t := by
  obtain ⟨D, hD, hskip, _⟩ := H.m3 0 t ht
  exact ⟨⟨D, hD⟩, hskip⟩

/-- Product of the consecutive M3 insertions at t,...,t+s-1. -/
noncomputable def paddingMap
    (H : SMTree S) (t : Nat) (ht : 0 < t) :
    Nat → MMap H
  | 0 => MMap.id H
  | s + 1 =>
      MMap.comp H
        (paddingLetter H (t + s) (by omega)).toMMap
        (paddingMap H t ht s)

theorem paddingMap_fixesBelow
    (H : SMTree S) (t : Nat) (ht : 0 < t) :
    ∀ s : Nat, (paddingMap H t ht s).FixesBelow H t := by
  intro s
  induction s with
  | zero =>
      exact MMap.id_fixesBelow H t
  | succ s ih =>
      intro x hx
      rw [paddingMap, MMap.comp_apply, ih x hx]
      exact
        (paddingLetter H (t + s) (by omega)).eq_id_below H
          (by omega)

theorem paddingMap_level_start
    (H : SMTree S) (t : Nat) (ht : 0 < t) :
    ∀ s : Nat,
      H.levelMap (paddingMap H t ht s).map t = t + s := by
  intro s
  induction s with
  | zero =>
      simpa [paddingMap] using padding_levelMap_id H t
  | succ s ih =>
      rw [paddingMap, padding_levelMap_comp, ih]
      have hlev :=
        H.levelMap_of_skipsOnly
          (paddingLetter H (t + s) (by omega)).toMMap.map
          (t + s)
          (paddingLetter H (t + s) (by omega)).skips
          (t + s)
      simp at hlev
      omega

theorem AM.sourceLast_le_terminalLevel
    (H : SMTree S) {n k : Nat} (hk : 0 < k)
    (a : AM H n k) :
    n + k - 1 ≤ a.terminalLevel H := by
  unfold AM.terminalLevel
  exact H.levelMap_id_le (a.representative H).map (n + k - 1)

/-- Composition with a coordinate ending at the last source level of f has
the same terminal target level as f. -/
theorem finiteShapeComp_terminalLevel_eq_left
    (H : SMTree S) {n m k : Nat}
    (hm : 0 < m) (hk : 0 < k)
    (f : AM H n m)
    (g : AM.At H n k (n + m - 1)) :
    (finiteShapeComp H f g.1).terminalLevel H =
      f.terminalLevel H := by
  let F := f.representative H
  let G := g.1.representative H
  have hfix :
      (MMap.comp H F G).FixesBelow H n :=
    MMap.comp_fixesBelow H F G n
      (f.representative_fixesBelow H)
      (g.1.representative_fixesBelow H)
  unfold finiteShapeComp
  rw [MMap.toAM_terminalLevel H (MMap.comp H F G) n k hfix (by omega)]
  rw [padding_levelMap_comp]
  change H.levelMap F.map (g.1.terminalLevel H) = f.terminalLevel H
  rw [g.2]
  rfl

/-- Exact-terminal finite composition. -/
noncomputable def exactComp
    (H : SMTree S) {n m k N : Nat}
    (hm : 0 < m) (hk : 0 < k)
    (f : AM.At H n m N)
    (g : AM.At H n k (n + m - 1)) :
    AM.At H n k N :=
  ⟨finiteShapeComp H f.1 g.1,
    (finiteShapeComp_terminalLevel_eq_left H hm hk f.1 g).trans f.2⟩

/-- Total map used to pad a bounded approximation from its terminal level to
a prescribed ambient level N. -/
noncomputable def paddingComposite
    (H : SMTree S) {n k N : Nat}
    (hk : 0 < k)
    (a : AM.AtMost H n k N)
    (ht : 0 < a.1.terminalLevel H) : MMap H :=
  let t := a.1.terminalLevel H
  MMap.comp H
    (paddingMap H t ht (N - t))
    (a.1.representative H)

theorem paddingComposite_fixesBelow
    (H : SMTree S) {n k N : Nat}
    (hk : 0 < k)
    (a : AM.AtMost H n k N)
    (ht : 0 < a.1.terminalLevel H) :
    (paddingComposite H hk a ht).FixesBelow H n := by
  let t := a.1.terminalLevel H
  have hlast : n + k - 1 ≤ t :=
    a.1.sourceLast_le_terminalLevel H hk
  have hnt : n ≤ t := by omega
  have hpad :
      (paddingMap H t ht (N - t)).FixesBelow H n := by
    intro x hx
    exact paddingMap_fixesBelow H t ht (N - t) x
      (lt_of_lt_of_le hx hnt)
  exact MMap.comp_fixesBelow H
    (paddingMap H t ht (N - t))
    (a.1.representative H) n
    hpad (a.1.representative_fixesBelow H)

/-- Pad a bounded nonempty approximation to the exact ambient terminal level. -/
noncomputable def padApproxTo
    (H : SMTree S) {n k N : Nat}
    (hk : 0 < k)
    (a : AM.AtMost H n k N)
    (ht : 0 < a.1.terminalLevel H) :
    AM.At H n k N := by
  let C := paddingComposite H hk a ht
  have hCfix : C.FixesBelow H n :=
    paddingComposite_fixesBelow H hk a ht
  let out : AM H n k := C.toAM H n k hCfix
  refine ⟨out, ?_⟩
  rw [MMap.toAM_terminalLevel H C n k hCfix (by omega)]
  unfold C paddingComposite
  rw [padding_levelMap_comp]
  change
    H.levelMap
        (paddingMap H (a.1.terminalLevel H) ht
          (N - a.1.terminalLevel H)).map
        (a.1.terminalLevel H) = N
  rw [paddingMap_level_start]
  omega

theorem padApproxTo_representative_agrees
    (H : SMTree S) {n k N : Nat}
    (hk : 0 < k)
    (a : AM.AtMost H n k N)
    (ht : 0 < a.1.terminalLevel H)
    (x : T) (hx : LevelTree.lev x < n + k) :
    (padApproxTo H hk a ht).1.representative H x =
      paddingComposite H hk a ht x := by
  unfold padApproxTo
  exact MMap.toAM_representative_agrees H
    (paddingComposite H hk a ht) n k
    (paddingComposite_fixesBelow H hk a ht) x hx


end SMTree
end SuccessorTree

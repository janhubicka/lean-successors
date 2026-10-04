import SuccessorTree.FatTree.Reduction
import SuccessorTree.FatTree.FiniteReduction
import Mathlib.Data.Fintype.Pi

/-!
# Finitization of the fat-tree order

This file starts the A.2 layer for the fat-tree Ramsey space.  The manuscript
defines x ≤fin y by finite fat-tree reduction together with equality of the
terminal cuts.  We isolate exactly that relation here before proving the
finiteness and approximation clauses of A.2.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FiniteFatTree

variable (H : SMTree S)

/-- Finite code for a one-row approximation whose last image level is
strictly below a fixed ambient cut. -/
noncomputable def boundedRowCode (n d : Nat)
    (a : {a : AM H n 1 // a.rowEndLevel H < d}) :
    InitialNode T n → InitialNode T d := by
  intro x
  let F : MMap H := a.1.representative H
  have htop := a.1.representative_top H
  have hval := congrArg Subtype.val htop
  change F.restrictLe H n = a.1.1.1 at hval
  have hx : a.1.1.1 x = F x.1 := by
    exact (congrFun hval x).symm
  refine ⟨a.1.1.1 x, ?_⟩
  have hlev :
      LevelTree.lev (F x.1) ≤ H.levelMap F.map n := by
    calc
      LevelTree.lev (F x.1) =
          H.levelMap F.map (LevelTree.lev x.1) :=
        (H.levelMap_eq F.map (a := x.1)).symm
      _ ≤ H.levelMap F.map n :=
        (H.levelMap_strictMono F.map).monotone x.2
  have hend : H.levelMap F.map n = a.1.rowEndLevel H := rfl
  apply Nat.le_of_lt
  calc
    LevelTree.lev (a.1.1.1 x) = LevelTree.lev (F x.1) := by rw [hx]
    _ ≤ H.levelMap F.map n := hlev
    _ = a.1.rowEndLevel H := hend
    _ < d := a.2

@[simp] theorem boundedRowCode_val (n d : Nat)
    (a : {a : AM H n 1 // a.rowEndLevel H < d})
    (x : InitialNode T n) :
    (boundedRowCode H n d a x).1 = a.1.1.1 x := by
  rfl

/-- The bounded row code is injective: a realized finite row is determined
by its values on the finite source initial segment. -/
theorem boundedRowCode_injective (n d : Nat) :
    Function.Injective (boundedRowCode H n d) := by
  classical
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hx := congrFun hab x
  have hxv := congrArg Subtype.val hx
  simpa only [boundedRowCode_val] using hxv

/-- For fixed source cut and ambient terminal bound there are only finitely
many possible one-row approximations. -/
theorem boundedRows_finite (n d : Nat) :
    Set.Finite {a : AM H n 1 | a.rowEndLevel H < d} := by
  classical
  rw [← Set.finite_coe_iff]
  exact Finite.of_injective
    (boundedRowCode H n d)
    (boundedRowCode_injective H n d)

/-- Uniform finite code for a bounded row.  We pad a row outside its
source initial segment by `none`, so all rows below terminal cut `d` live
in the same finite function space. -/
noncomputable def uniformRowCode (n d : Nat)
    (a : {a : AM H n 1 // a.rowEndLevel H < d}) :
    InitialNode T d → Option (InitialNode T d) := by
  intro x
  by_cases hx : LevelTree.lev x.1 ≤ n
  · exact some (boundedRowCode H n d a ⟨x.1, hx⟩)
  · exact none

/-- Padding does not lose information about a row with fixed source cut. -/
theorem uniformRowCode_injective (n d : Nat) :
    Function.Injective (uniformRowCode H n d) := by
  classical
  intro a b hab
  apply boundedRowCode_injective H n d
  funext x
  have hnd : n ≤ d := by
    have hle :
        n ≤ a.1.rowEndLevel H := by
      exact H.levelMap_id_le (a.1.representative H).map n
    omega
  let xd : InitialNode T d :=
    ⟨x.1, x.2.trans hnd⟩
  have hxcode := congrFun hab xd
  have hs :
      some (boundedRowCode H n d a x) =
        some (boundedRowCode H n d b x) := by
    simpa [uniformRowCode, xd, x.2] using hxcode
  exact Option.some.inj hs

/-- A fixed finite ambient code space for fat trees whose terminal cut is
`d`.  The first coordinate records the height, the second the selected cuts,
and the third the uniformly padded row maps. -/
def FixedTerminalCode (d : Nat) :=
  Fin (d + 1) ×
    (Fin (d + 1) → Option (Fin (d + 1))) ×
    (Fin d → Option (InitialNode T d → Option (InitialNode T d)))

noncomputable instance fixedTerminalCodeFintype (d : Nat) :
    Fintype (FixedTerminalCode (T := T) d) := by
  classical
  letI node : Fintype (InitialNode T d) := initialNodeFintype T d
  letI nodeOpt : Fintype (Option (InitialNode T d)) := inferInstance
  letI rowMap :
      Fintype (InitialNode T d → Option (InitialNode T d)) := inferInstance
  letI rowOpt :
      Fintype (Option (InitialNode T d → Option (InitialNode T d))) :=
    inferInstance
  letI cutOpt : Fintype (Option (Fin (d + 1))) := inferInstance
  letI cutMap :
      Fintype (Fin (d + 1) → Option (Fin (d + 1))) := inferInstance
  letI rows :
      Fintype
        (Fin d → Option (InitialNode T d → Option (InitialNode T d))) :=
    inferInstance
  unfold FixedTerminalCode
  infer_instance

/-- Finite fat trees with a prescribed terminal cut. -/
def FixedTerminal (d : Nat) :=
  {U : FiniteFatTree H // U.terminalCut = d}

/-- Encode a finite fat tree ending at cut `d` in a fixed finite
ambient code space.  Positions beyond the actual height are padded by
`none`. -/
noncomputable def fixedTerminalCode (d : Nat)
    (U : FixedTerminal H d) :
    FixedTerminalCode (T := T) d := by
  have hheight : U.1.height ≤ d := by
    have h := U.1.height_le_terminalCut H
    simpa [U.2] using h
  let h : Fin (d + 1) :=
    ⟨U.1.height, Nat.lt_succ_of_le hheight⟩
  refine ⟨h, ?_, ?_⟩
  · intro j
    by_cases hj : j.1 ≤ U.1.height
    · let i : Fin (U.1.height + 1) :=
        ⟨j.1, Nat.lt_succ_of_le hj⟩
      have hcut : U.1.cut i ≤ d := by
        have hle := U.1.cut_le_terminalCut H i
        simpa [U.2] using hle
      exact some ⟨U.1.cut i, Nat.lt_succ_of_le hcut⟩
    · exact none
  · intro j
    by_cases hj : j.1 < U.1.height
    · let i : Fin U.1.height := ⟨j.1, hj⟩
      have hnext : U.1.cut i.succ ≤ d := by
        have hle := U.1.cut_le_terminalCut H i.succ
        simpa [U.2] using hle
      have hend : (U.1.row i).rowEndLevel H < d := by
        have hrow := U.1.row_cut i
        omega
      exact some
        (uniformRowCode H (U.1.cut i.castSucc) d
          ⟨U.1.row i, hend⟩)
    · exact none

@[simp] theorem fixedTerminalCode_height (d : Nat)
    (U : FixedTerminal H d) :
    (fixedTerminalCode H d U).1.1 = U.1.height := by
  simp [fixedTerminalCode]

/-- The fixed-terminal code loses no finite fat-tree information. -/
theorem fixedTerminalCode_injective (d : Nat) :
    Function.Injective (fixedTerminalCode H d) := by
  classical
  rintro ⟨U, hUt⟩ ⟨V, hVt⟩ hcode
  apply Subtype.ext
  rcases U with ⟨uh, uc, uz, ur, urc⟩
  rcases V with ⟨vh, vc, vz, vr, vrc⟩
  dsimp at hUt hVt hcode ⊢
  have hheight : uh = vh := by
    have h := congrArg
      (fun c : FixedTerminalCode (T := T) d => c.1.1) hcode
    simpa [fixedTerminalCode] using h
  subst vh
  have hcuts := congrArg
    (fun c : FixedTerminalCode (T := T) d => c.2.1) hcode
  have hrows := congrArg
    (fun c : FixedTerminalCode (T := T) d => c.2.2) hcode
  have hUd : uh ≤ d := by
    have h :=
      (FiniteFatTree.mk uh uc uz ur urc).height_le_terminalCut H
    calc
      uh ≤ uc ⟨uh, Nat.lt_succ_self uh⟩ := by
        simpa [FiniteFatTree.terminalCut] using h
      _ = d := hUt
  have hVd : uh ≤ d := by
    have h :=
      (FiniteFatTree.mk uh vc vz vr vrc).height_le_terminalCut H
    calc
      uh ≤ vc ⟨uh, Nat.lt_succ_self uh⟩ := by
        simpa [FiniteFatTree.terminalCut] using h
      _ = d := hVt
  have hcut : uc = vc := by
    funext i
    have hi : i.1 ≤ uh := Nat.le_of_lt_succ i.2
    have hid : i.1 ≤ d := hi.trans hUd
    let j : Fin (d + 1) :=
      ⟨i.1, Nat.lt_succ_of_le hid⟩
    have hc := congrFun hcuts j
    have hUc : uc i ≤ d := by
      have h :=
        (FiniteFatTree.mk uh uc uz ur urc).cut_le_terminalCut H i
      calc
        uc i ≤ uc ⟨uh, Nat.lt_succ_self uh⟩ := by
          simpa [FiniteFatTree.terminalCut] using h
        _ = d := hUt
    have hVc : vc i ≤ d := by
      have h :=
        (FiniteFatTree.mk uh vc vz vr vrc).cut_le_terminalCut H i
      calc
        vc i ≤ vc ⟨uh, Nat.lt_succ_self uh⟩ := by
          simpa [FiniteFatTree.terminalCut] using h
        _ = d := hVt
    have hs :
        some (⟨uc i, Nat.lt_succ_of_le hUc⟩ : Fin (d + 1)) =
          some (⟨vc i, Nat.lt_succ_of_le hVc⟩ : Fin (d + 1)) := by
      simpa [fixedTerminalCode, j, hi] using hc
    exact congrArg Fin.val (Option.some.inj hs)
  subst vc
  have hrow : ur = vr := by
    funext i
    have hjd : i.1 < d := lt_of_lt_of_le i.2 hUd
    let j : Fin d := ⟨i.1, hjd⟩
    have hr := congrFun hrows j
    have hUend : (ur i).rowEndLevel H < d := by
      have hrc := urc i
      have hterminal : uc i.succ ≤ d := by
        have h :=
          (FiniteFatTree.mk uh uc uz ur urc).cut_le_terminalCut H i.succ
        calc
          uc i.succ ≤ uc ⟨uh, Nat.lt_succ_self uh⟩ := by
            simpa [FiniteFatTree.terminalCut] using h
          _ = d := hUt
      omega
    have hVend : (vr i).rowEndLevel H < d := by
      have hrc := vrc i
      have hterminal : uc i.succ ≤ d := by
        have h :=
          (FiniteFatTree.mk uh uc vz vr vrc).cut_le_terminalCut H i.succ
        calc
          uc i.succ ≤ uc ⟨uh, Nat.lt_succ_self uh⟩ := by
            simpa [FiniteFatTree.terminalCut] using h
          _ = d := hVt
      omega
    have hr' := Option.some.inj (by
      simpa [fixedTerminalCode, j, i.2] using hr)
    have hb := uniformRowCode_injective H _ d hr'
    have hbv := congrArg Subtype.val hb
    simpa using hbv
  subst vr
  rfl

/-- There are only finitely many finite fat trees ending at a prescribed
terminal ambient cut. -/
theorem fixedTerminal_finite (d : Nat) :
    Set.Finite {U : FiniteFatTree H | U.terminalCut = d} := by
  classical
  rw [← Set.finite_coe_iff]
  exact Finite.of_injective
    (fixedTerminalCode H d)
    (fixedTerminalCode_injective H d)

/-- The manuscript's finitary order on finite fat trees: reduction with the
same terminal ambient cut. -/
def LeFin (X Y : FiniteFatTree H) : Prop :=
  Reduces H X Y ∧ X.terminalCut = Y.terminalCut

/-- The finitary fat-tree order is reflexive. -/
theorem leFin_refl (X : FiniteFatTree H) : LeFin H X X := by
  exact ⟨reduces_refl H X, rfl⟩

/-- The finitary fat-tree order is transitive. -/
theorem leFin_trans {X Y Z : FiniteFatTree H}
    (hXY : LeFin H X Y) (hYZ : LeFin H Y Z) :
    LeFin H X Z := by
  exact ⟨reduces_trans H hXY.1 hYZ.1, hXY.2.trans hYZ.2⟩

/-- Forgetting the terminal-cut equality leaves an ordinary finite
fat-subtree reduction. -/
theorem reduces_of_leFin {X Y : FiniteFatTree H}
    (h : LeFin H X Y) : Reduces H X Y :=
  h.1

/-- A finitary reduction has exactly the same terminal ambient cut. -/
theorem terminalCut_eq_of_leFin {X Y : FiniteFatTree H}
    (h : LeFin H X Y) : X.terminalCut = Y.terminalCut :=
  h.2


/-- Todorčević A.2(1) for the manuscript's finite order: a fixed finite
fat tree has only finitely many `≤fin` predecessors. -/
theorem leFin_lower_finite (Y : FiniteFatTree H) :
    Set.Finite {X : FiniteFatTree H | LeFin H X Y} := by
  apply (fixedTerminal_finite H Y.terminalCut).subset
  intro X hX
  exact hX.2


/-- Forward half of A2(2): an infinite fat-tree reduction induces
finite `≤fin` reductions on every initial segment. -/
theorem exists_initialSegment_leFin_of_reduces
    {V U : FatTree H}
    (hVU : FatTree.Reduces H V U) (n : Nat) :
    ∃ m : Nat,
      LeFin H (V.initialSegment H n) (U.initialSegment H m) := by
  rcases hVU with ⟨w⟩
  refine ⟨w.index n, ?_⟩
  constructor
  · exact ⟨w.initialSegment H n⟩
  · simpa using w.cut_eq n

/-- Converse half of A2(2): coherent finite `≤fin` reductions of
all initial segments determine one infinite fat-tree reduction.  Coherence of
the target indices is forced by equality of terminal cuts and injectivity of
the ambient cut function. -/
theorem reduces_of_initialSegment_leFin
    {V U : FatTree H}
    (hlocal :
      ∀ n : Nat, ∃ m : Nat,
        LeFin H (V.initialSegment H n) (U.initialSegment H m)) :
    FatTree.Reduces H V U := by
  classical
  let φ : Nat → Nat := fun n => Classical.choose (hlocal n)
  have hφ :
      ∀ n : Nat,
        LeFin H (V.initialSegment H n)
          (U.initialSegment H (φ n)) := by
    intro n
    exact Classical.choose_spec (hlocal n)
  have hcut : ∀ n : Nat, V.cut n = U.cut (φ n) := by
    intro n
    simpa [φ] using (hφ n).2
  have hstrict : StrictMono φ := by
    intro i j hij
    by_contra hnot
    have hji : φ j ≤ φ i := Nat.le_of_not_gt hnot
    have hUle := (U.cut_strictMono H).monotone hji
    have hVlt := V.cut_strictMono H hij
    rw [hcut i, hcut j] at hVlt
    exact (not_lt_of_ge hUle) hVlt
  refine ⟨{
    index := φ
    index_strict := hstrict
    cut_eq := hcut
    lift_subset := ?_
  }⟩
  intro i
  let ri : Fin (i + 1) := ⟨i, by omega⟩
  rcases (hφ (i + 1)).1 with ⟨fw⟩
  have hsCut := fw.cut_eq ri.castSucc
  have heCut := fw.cut_eq ri.succ
  change
    V.cut i =
      U.cut (fw.index ri.castSucc).1 at hsCut
  change
    V.cut (i + 1) =
      U.cut (fw.index ri.succ).1 at heCut
  have hstart : (fw.index ri.castSucc).1 = φ i := by
    apply U.cut_injective H
    calc
      U.cut (fw.index ri.castSucc).1 = V.cut i := hsCut.symm
      _ = U.cut (φ i) := hcut i
  have hend : (fw.index ri.succ).1 = φ (i + 1) := by
    apply U.cut_injective H
    calc
      U.cut (fw.index ri.succ).1 = V.cut (i + 1) := heCut.symm
      _ = U.cut (φ (i + 1)) := hcut (i + 1)
  have hfin := fw.lift_subset ri
  rw [V.initialSegment_oneLift H (i + 1) ri] at hfin
  rw [U.initialSegment_liftTo H (φ (i + 1))] at hfin
  simpa [ri, hstart, hend] using hfin

/-- A2(2) for infinite fat trees, expressed using the manuscript's finite
initial segments and `≤fin`. -/
theorem reduces_iff_initialSegment_leFin
    (V U : FatTree H) :
    FatTree.Reduces H V U ↔
      ∀ n : Nat, ∃ m : Nat,
        LeFin H (V.initialSegment H n) (U.initialSegment H m) := by
  constructor
  · intro h n
    exact exists_initialSegment_leFin_of_reduces H h n
  · exact reduces_of_initialSegment_leFin H

/-- A2(3), in prefix form: a finite reduction restricts to every source
prefix, and the corresponding target prefix ends at the image of that
terminal cut. -/
theorem leFin_prefix
    {Y Z : FiniteFatTree H}
    (hYZ : LeFin H Y Z)
    (n : Nat) (hn : n ≤ Y.height) :
    ∃ (m : Nat) (hm : m ≤ Z.height),
      LeFin H (Y.initialSegment H n hn) (Z.initialSegment H m hm) := by
  rcases hYZ.1 with ⟨w⟩
  let yn : Fin (Y.height + 1) := ⟨n, by omega⟩
  let zn : Fin (Z.height + 1) := w.index yn
  let m : Nat := zn.1
  have hm : m ≤ Z.height := Nat.le_of_lt_succ zn.2
  refine ⟨m, hm, ?_⟩
  constructor
  · exact ⟨w.initialSegment H n hn⟩
  · have hc := w.cut_eq yn
    simpa [FiniteFatTree.initialSegment_terminalCut, yn, zn, m] using hc

end FiniteFatTree

end SMTree
end SuccessorTree

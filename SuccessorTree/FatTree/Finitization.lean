import SuccessorTree.FatTree.FiniteReduction

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
  letI : Fintype (InitialNode T d) := initialNodeFintype T d
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
    simpa [FiniteFatTree.terminalCut, hUt] using h
  have hVd : uh ≤ d := by
    have h :=
      (FiniteFatTree.mk uh vc vz vr vrc).height_le_terminalCut H
    simpa [FiniteFatTree.terminalCut, hVt] using h
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
      simpa [FiniteFatTree.terminalCut, hUt] using h
    have hVc : vc i ≤ d := by
      have h :=
        (FiniteFatTree.mk uh vc vz vr vrc).cut_le_terminalCut H i
      simpa [FiniteFatTree.terminalCut, hVt] using h
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
      have hterminal :
          uc i.succ ≤ d := by
        have h :=
          (FiniteFatTree.mk uh uc uz ur urc).cut_le_terminalCut H i.succ
        simpa [FiniteFatTree.terminalCut, hUt] using h
      omega
    have hVend : (vr i).rowEndLevel H < d := by
      have hrc := vrc i
      have hterminal :
          uc i.succ ≤ d := by
        have h :=
          (FiniteFatTree.mk uh uc vz vr vrc).cut_le_terminalCut H i.succ
        simpa [FiniteFatTree.terminalCut, hVt] using h
      omega
    have hs :
        some
            (uniformRowCode H (uc i.castSucc) d
              ⟨ur i, hUend⟩) =
          some
            (uniformRowCode H (uc i.castSucc) d
              ⟨vr i, hVend⟩) := by
      simpa [fixedTerminalCode, j, i.2] using hr
    have hb :=
      uniformRowCode_injective H (uc i.castSucc) d
        (Option.some.inj hs)
    exact congrArg Subtype.val hb
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

end FiniteFatTree

end SMTree
end SuccessorTree

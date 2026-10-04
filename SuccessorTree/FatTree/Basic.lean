import SuccessorTree.Canonical
import SuccessorTree.ShapePigeonhole

/-!
# Fat subtrees: structural data

This file formalizes the data in the manuscript's definition of a fat
subtree, before any topological-Ramsey-space axioms are imposed.

The key point is that a row `u : AM H n 1` is a *finite* approximation.
Whenever the manuscript writes `u⁺`, we therefore use the canonical total
extension supplied by `canonicalExtension`; an arbitrary total representative
of `u` is not sufficient for the lift construction.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- The last target level used by a one-row approximation.  This is determined
by the finite approximation; the chosen representative is only a convenient
way to read it. -/
noncomputable def AM.rowEndLevel
    (H : SMTree S) {n : Nat} (a : AM H n 1) : Nat :=
  H.levelMap (a.representative H).map n

/-- An infinite fat subtree.  The equation is written without natural-number
subtraction: the row ending at target level `m` has next cut `m + 1`.
This is equivalent to the paper's `u_i ∈ AM^{c(i)}_1(c(i+1)-1)`, while
making positivity and strict growth of the cut explicit. -/
structure FatTree (H : SMTree S) where
  cut : Nat → Nat
  cut_zero : cut 0 = 0
  row : (i : Nat) → AM H (cut i) 1
  row_cut : ∀ i : Nat, (row i).rowEndLevel H + 1 = cut (i + 1)

/-- A finite fat subtree, including its terminal cut. -/
structure FiniteFatTree (H : SMTree S) where
  height : Nat
  cut : Fin (height + 1) → Nat
  cut_zero : cut 0 = 0
  row : (i : Fin height) → AM H (cut i.castSucc) 1
  row_cut : ∀ i : Fin height,
    (row i).rowEndLevel H + 1 = cut i.succ

/-- The final cut of a finite fat tree.  Keeping it as named data is
useful for A.2: the finitary order remembers this cut explicitly. -/
def FiniteFatTree.terminalCut {H : SMTree S}
    (U : FiniteFatTree H) : Nat :=
  U.cut ⟨U.height, Nat.lt_succ_self U.height⟩

namespace FatTree

variable (H : SMTree S)

/-- Every row forces the next cut to be strictly larger. -/
theorem cut_lt_succ (U : FatTree H) (i : Nat) :
    U.cut i < U.cut (i + 1) := by
  have hle : U.cut i ≤ (U.row i).rowEndLevel H := by
    exact H.levelMap_id_le (U.row i).representative.map (U.cut i)
  calc
    U.cut i < (U.row i).rowEndLevel H + 1 := Nat.lt_succ_of_le hle
    _ = U.cut (i + 1) := U.row_cut i

/-- Hence the cut of an infinite fat subtree is strictly increasing. -/
theorem cut_strictMono (U : FatTree H) : StrictMono U.cut := by
  exact strictMono_nat_of_lt_succ (fun i => by
    simpa [Nat.succ_eq_add_one] using U.cut_lt_succ H i)

/-- In particular the cut is injective, which justifies uniqueness in the
paper's definition of `depth_U(x)`. -/
theorem cut_injective (U : FatTree H) : Function.Injective U.cut :=
  (U.cut_strictMono H).injective

/-- The first `n` rows of an infinite fat tree, with the terminal cut kept. -/
def initialSegment (U : FatTree H) (n : Nat) : FiniteFatTree H where
  height := n
  cut := fun i => U.cut i.1
  cut_zero := U.cut_zero
  row := fun i => U.row i.1
  row_cut := by
    intro i
    simpa using U.row_cut i.1

@[simp] theorem initialSegment_terminalCut (U : FatTree H) (n : Nat) :
    (U.initialSegment H n).terminalCut = U.cut n := rfl

/-- Every cut of an infinite fat tree's finite initial segment is the
corresponding ambient cut. -/
theorem initialSegment_cut (U : FatTree H)
    (n : Nat) (i : Fin ((U.initialSegment H n).height + 1)) :
    (U.initialSegment H n).cut i = U.cut i.1 := by
  rfl

/-- The paper's `u_i⁺`: the canonical total extension of row `i`. -/
noncomputable def rowExtension (U : FatTree H) (i : Nat) : MMap H :=
  H.canonicalExtension ((U.row i).representative H) (U.cut i)

/-- The canonical row extension agrees with the row on the prescribed source
initial segment. -/
theorem rowExtension_agrees (U : FatTree H) (i : Nat)
    (x : T) (hx : LevelTree.lev x ≤ U.cut i) :
    U.rowExtension H i x = (U.row i).representative H x := by
  exact H.canonicalExtension_agrees _ _ _ hx

/-- The canonical extension has the same terminal image level as the row. -/
theorem rowExtension_level_at_cut (U : FatTree H) (i : Nat) :
    H.levelMap (U.rowExtension H i).map (U.cut i) =
      (U.row i).rowEndLevel H := by
  exact H.canonicalExtension_level_at_prefix _ _

/-- This is the level calculation used implicitly in the definition of
`Lift`: immediate successors of level `cut i`, after applying `u_i⁺`, lie
exactly on level `cut (i+1)`. -/
theorem rowExtension_level_succ (U : FatTree H) (i : Nat) :
    H.levelMap (U.rowExtension H i).map (U.cut i + 1) = U.cut (i + 1) := by
  calc
    H.levelMap (U.rowExtension H i).map (U.cut i + 1) =
        H.levelMap (U.rowExtension H i).map (U.cut i) + 1 :=
      H.canonicalExtension_level_succ
        ((U.row i).representative H) (U.cut i) (U.cut i) le_rfl
    _ = (U.row i).rowEndLevel H + 1 := by
      rw [U.rowExtension_level_at_cut H i]
    _ = U.cut (i + 1) := U.row_cut i

end FatTree

namespace FiniteFatTree

variable (H : SMTree S)

/-- Two finite fat trees are equal once their data fields agree; the
structural proof fields are irrelevant.  HEq is convenient because the cut
and row domains depend on the height. -/
theorem ext_data {U V : FiniteFatTree H}
    (hheight : U.height = V.height)
    (hcut : HEq U.cut V.cut)
    (hrow : HEq U.row V.row) :
    U = V := by
  cases U with
  | mk uh uc uz ur urc =>
      cases V with
      | mk vh vc vz vr vrc =>
          dsimp at hheight hcut hrow
          subst vh
          have hc : uc = vc := eq_of_heq hcut
          subst vc
          have hr : ur = vr := eq_of_heq hrow
          subst vr
          rfl

/-- The first `n` rows of a finite fat tree, retaining the cut after
the last retained row. -/
def initialSegment (U : FiniteFatTree H) (n : Nat) (hn : n ≤ U.height) :
    FiniteFatTree H where
  height := n
  cut := fun i =>
    U.cut ⟨i.1, by omega⟩
  cut_zero := by
    simpa using U.cut_zero
  row := fun i =>
    U.row ⟨i.1, by omega⟩
  row_cut := by
    intro i
    let j : Fin U.height := ⟨i.1, by omega⟩
    have hs :
        j.succ =
          (⟨i.1 + 1, by omega⟩ : Fin (U.height + 1)) :=
      Fin.ext rfl
    have h := U.row_cut j
    rw [hs] at h
    simpa [j] using h

@[simp] theorem initialSegment_height (U : FiniteFatTree H)
    (n : Nat) (hn : n ≤ U.height) :
    (U.initialSegment H n hn).height = n := rfl

@[simp] theorem initialSegment_cut (U : FiniteFatTree H)
    (n : Nat) (hn : n ≤ U.height)
    (i : Fin (n + 1)) :
    (U.initialSegment H n hn).cut i =
      U.cut ⟨i.1, by omega⟩ := rfl

/-- Cut projection with the dependent index type carried by the
initial-segment object itself. -/
theorem initialSegment_cut_dep (U : FiniteFatTree H)
    (n : Nat) (hn : n ≤ U.height)
    (i : Fin ((U.initialSegment H n hn).height + 1)) :
    (U.initialSegment H n hn).cut i =
      U.cut
        (⟨i.1, by
          have hi : i.1 ≤ n := by
            simpa using Nat.le_of_lt_succ i.2
          exact Nat.lt_succ_of_le (hi.trans hn)⟩ :
          Fin (U.height + 1)) := by
  rfl

@[simp] theorem initialSegment_terminalCut (U : FiniteFatTree H)
    (n : Nat) (hn : n ≤ U.height) :
    (U.initialSegment H n hn).terminalCut =
      U.cut ⟨n, by omega⟩ := rfl

/-- The canonical total extension of a finite fat-tree row. -/
noncomputable def rowExtension (U : FiniteFatTree H)
    (i : Fin U.height) : MMap H :=
  H.canonicalExtension ((U.row i).representative H) (U.cut i.castSucc)

/-- A finite row extension agrees with the row on its prescribed prefix. -/
theorem rowExtension_agrees (U : FiniteFatTree H)
    (i : Fin U.height) (x : T)
    (hx : LevelTree.lev x ≤ U.cut i.castSucc) :
    U.rowExtension H i x = (U.row i).representative H x := by
  exact H.canonicalExtension_agrees _ _ _ hx

/-- The finite row extension has the same final image level as the row. -/
theorem rowExtension_level_at_cut (U : FiniteFatTree H)
    (i : Fin U.height) :
    H.levelMap (U.rowExtension H i).map (U.cut i.castSucc) =
      (U.row i).rowEndLevel H := by
  exact H.canonicalExtension_level_at_prefix _ _

/-- Immediate successors at one finite cut are sent to the next cut. -/
theorem rowExtension_level_succ (U : FiniteFatTree H)
    (i : Fin U.height) :
    H.levelMap (U.rowExtension H i).map (U.cut i.castSucc + 1) =
      U.cut i.succ := by
  calc
    H.levelMap (U.rowExtension H i).map (U.cut i.castSucc + 1) =
        H.levelMap (U.rowExtension H i).map (U.cut i.castSucc) + 1 :=
      H.canonicalExtension_level_succ
        ((U.row i).representative H) (U.cut i.castSucc)
        (U.cut i.castSucc) le_rfl
    _ = (U.row i).rowEndLevel H + 1 := by
      rw [U.rowExtension_level_at_cut H i]
    _ = U.cut i.succ := U.row_cut i

/-- Adjacent cuts in a finite fat tree are strictly increasing as well. -/
theorem cut_lt_succ (U : FiniteFatTree H) (i : Fin U.height) :
    U.cut i.castSucc < U.cut i.succ := by
  have hle : U.cut i.castSucc ≤ (U.row i).rowEndLevel H := by
    exact H.levelMap_id_le (U.row i).representative.map (U.cut i.castSucc)
  calc
    U.cut i.castSucc < (U.row i).rowEndLevel H + 1 := Nat.lt_succ_of_le hle
    _ = U.cut i.succ := U.row_cut i

/-- The k-th cut is at least k.  Thus the terminal ambient cut bounds
the number of rows in a finite fat tree. -/
theorem index_le_cut (U : FiniteFatTree H) :
    ∀ k : Nat, (hk : k ≤ U.height) →
      k ≤ U.cut (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (U.height + 1)) := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [U.cut_zero]
  | succ k ih =>
      intro hk
      have hklt : k < U.height := by omega
      let i : Fin U.height := ⟨k, hklt⟩
      have hprev :
          k ≤ U.cut i.castSucc := by
        have := ih (Nat.le_of_lt hklt)
        simpa [i] using this
      have hprev' :
          k ≤ U.cut (⟨k, by omega⟩ : Fin (U.height + 1)) := by
        simpa [i] using hprev
      have hstep := U.cut_lt_succ H i
      change
        U.cut (⟨k, by omega⟩ : Fin (U.height + 1)) <
          U.cut (⟨k + 1, by omega⟩ : Fin (U.height + 1)) at hstep
      exact Nat.succ_le_of_lt (lt_of_le_of_lt hprev' hstep)

/-- Height is bounded by the terminal cut. -/
theorem height_le_terminalCut (U : FiniteFatTree H) :
    U.height ≤ U.terminalCut := by
  simpa [FiniteFatTree.terminalCut] using
    U.index_le_cut H U.height le_rfl

/-- Finite cuts are monotone with their cut index. -/
theorem cut_le_of_index_le (U : FiniteFatTree H)
    {i j : Nat} (hi : i ≤ U.height) (hj : j ≤ U.height)
    (hij : i ≤ j) :
    U.cut (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (U.height + 1)) ≤
      U.cut (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (U.height + 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  have aux :
      ∀ k : Nat, (hk : i + k ≤ U.height) →
        U.cut (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (U.height + 1)) ≤
          U.cut (⟨i + k, Nat.lt_succ_of_le hk⟩ :
            Fin (U.height + 1)) := by
    intro k
    induction k with
    | zero =>
        intro hk
        rfl
    | succ k ih =>
        intro hk
        have hkprev : i + k ≤ U.height := by omega
        have hklt : i + k < U.height := by omega
        have hprev := ih hkprev
        let q : Fin U.height := ⟨i + k, hklt⟩
        have hstep := U.cut_lt_succ H q
        have hstep' :
            U.cut
                (⟨i + k, Nat.lt_succ_of_le hkprev⟩ :
                  Fin (U.height + 1)) ≤
              U.cut
                (⟨i + (k + 1), Nat.lt_succ_of_le hk⟩ :
                  Fin (U.height + 1)) := by
          exact Nat.le_of_lt (by
            simpa [q, Nat.add_assoc] using hstep)
        exact hprev.trans hstep'
  exact aux k hj

/-- Every finite cut is at most the terminal cut. -/
theorem cut_le_terminalCut (U : FiniteFatTree H)
    (i : Fin (U.height + 1)) :
    U.cut i ≤ U.terminalCut := by
  have h :=
    U.cut_le_of_index_le H
      (i := i.1) (j := U.height)
      (Nat.le_of_lt_succ i.2) le_rfl
      (Nat.le_of_lt_succ i.2)
  simpa [FiniteFatTree.terminalCut] using h

end FiniteFatTree

end SMTree
end SuccessorTree

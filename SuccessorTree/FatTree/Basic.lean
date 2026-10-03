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

/-- Adjacent cuts in a finite fat tree are strictly increasing as well. -/
theorem cut_lt_succ (U : FiniteFatTree H) (i : Fin U.height) :
    U.cut i.castSucc < U.cut i.succ := by
  have hle : U.cut i.castSucc ≤ (U.row i).rowEndLevel H := by
    exact H.levelMap_id_le (U.row i).representative.map (U.cut i.castSucc)
  calc
    U.cut i.castSucc < (U.row i).rowEndLevel H + 1 := Nat.lt_succ_of_le hle
    _ = U.cut i.succ := U.row_cut i

end FiniteFatTree

end SMTree
end SuccessorTree

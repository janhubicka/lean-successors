import SuccessorTree.Successor
import Mathlib.Tactic

/-!
# Injectivity follows from weak successors and strict level order

For an S-tree, a function that preserves equal levels, strictly
preserves the order of levels, extends each root and weakly preserves
successors is automatically injective. The usual shape-map
injectivity field is not invoked in the proof.

The induction uses S2 on two mapped successor witnesses lying
below a common image and the already established injectivity
at lower source levels for their parameter lists.

This is intended as a reusable tool for constructing the future
M2 deletion map: after its level function, root property and weak
successor preservation have been proved, injectivity need not be
reconstructed separately from deleted relation columns.
It does NOT prove any of those other M2 obligations.
-/

namespace SuccessorTree

universe u v

private theorem list_map_injective_of_left_witnesses
    {α : Type u} {β : Type v} (f : α → β)
    {xs ys : List α}
    (hLeft : ∀ x ∈ xs, ∀ y, f x = f y → x = y)
    (hMap : xs.map f = ys.map f) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hMap
  | cons x xs ih =>
      cases ys with
      | nil => simp at hMap
      | cons y ys =>
          simp only [List.map_cons] at hMap
          have hPair := List.cons.inj hMap
          have hx : x = y := hLeft x (by simp) y hPair.1
          have hTail : ∀ z ∈ xs, ∀ w, f z = f w → z = w := by
            intro z hz w hzw
            exact hLeft z (by simp [hz]) w hzw
          have hxs : xs = ys := ih hTail hPair.2
          simp [hx,hxs]

/-- A function on an S-tree is injective if it preserves the order
of levels strictly and weakly preserves actual successors, extends
every root and preserves the equality of levels.

No assumed injectivity, M2, M3, or pruning is used. The mapped
successor witnesses only lie BELOW the images of their source
successors, as in the published weak shape-map definition. -/
theorem injective_of_level_order_and_weak_successors
    {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T]
    (S : STree T Label)
    (f : T → T)
    (hLevel : ∀ {x y : T}, LevelTree.lev x = LevelTree.lev y →
      LevelTree.lev (f x) = LevelTree.lev (f y))
    (hStrict : ∀ {x y : T}, LevelTree.lev x < LevelTree.lev y →
      LevelTree.lev (f x) < LevelTree.lev (f y))
    (hWeak : ∀ {a b : T} {p : List T} {c : Label},
      S.succ a p c = some b →
      ∃ d : T, S.succ (f a) (p.map f) c = some d ∧ d ≤ f b)
    (hRoot : ∀ {a : T}, LevelTree.lev a = 0 → a ≤ f a) :
    Function.Injective f := by
  have hSameLevel : ∀ {x y : T}, f x = f y →
      LevelTree.lev x = LevelTree.lev y := by
    intro x y heq
    rcases lt_trichotomy (LevelTree.lev x) (LevelTree.lev y) with
        hlt | he | hgt
    · have hh := hStrict hlt
      rw [heq] at hh
      exact False.elim ((Nat.lt_irrefl _) hh)
    · exact he
    · have hh := hStrict hgt
      rw [heq] at hh
      exact False.elim ((Nat.lt_irrefl _) hh)
  have hMain :
      ∀ n : Nat, ∀ a b : T,
        LevelTree.lev a = n → f a = f b → a = b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a b ha heq
        have hb : LevelTree.lev b = n :=
          (hSameLevel heq).symm.trans ha
        by_cases hn0 : n = 0
        · have hRootA : a ≤ f a := hRoot (ha.trans hn0)
          have hRootB : b ≤ f b := hRoot (hb.trans hn0)
          have hRootBSame : b ≤ f a := by
            rw [heq]
            exact hRootB
          have habLev : LevelTree.lev a = LevelTree.lev b :=
            ha.trans hb.symm
          rcases LevelTree.comparable_below hRootA hRootBSame with
              hAB | hBA
          · exact LevelTree.same_level_of_le hAB habLev
          · exact (LevelTree.same_level_of_le hBA habLev.symm).symm
        · let qa : T := LevelTree.ancestor a (n-1) (by omega)
          let qb : T := LevelTree.ancestor b (n-1) (by omega)
          have hqaLev : LevelTree.lev qa = n-1 :=
            LevelTree.level_ancestor a (n-1) (by omega)
          have hqbLev : LevelTree.lev qb = n-1 :=
            LevelTree.level_ancestor b (n-1) (by omega)
          have hqaLe : qa ≤ a :=
            LevelTree.ancestor_le a (n-1) (by omega)
          have hqbLe : qb ≤ b :=
            LevelTree.ancestor_le b (n-1) (by omega)
          have hqaCov : qa ⋖ a := by
            apply LevelTree.covBy_of_le_level_succ hqaLe
            omega
          have hqbCov : qb ⋖ b := by
            apply LevelTree.covBy_of_le_level_succ hqbLe
            omega
          obtain ⟨pa,ca,hAstep⟩ := S.s3 hqaCov
          obtain ⟨pb,cb,hBstep⟩ := S.s3 hqbCov
          obtain ⟨da,hMappedA,hdaLe⟩ := hWeak hAstep
          obtain ⟨db,hMappedB,hdbLe⟩ := hWeak hBstep
          have hGaLe : f qa ≤ f a :=
            (S.covBy_of_succ_eq_some hMappedA).le.trans hdaLe
          have hGbLe : f qb ≤ f b :=
            (S.covBy_of_succ_eq_some hMappedB).le.trans hdbLe
          have hGbSame : f qb ≤ f a := by
            rw [heq]
            exact hGbLe
          have hMapParentLev : LevelTree.lev (f qa) =
              LevelTree.lev (f qb) := hLevel (hqaLev.trans hqbLev.symm)
          have hMapParent : f qa = f qb := by
            rcases LevelTree.comparable_below hGaLe hGbSame with
                hAB | hBA
            · exact LevelTree.same_level_of_le hAB hMapParentLev
            · exact (LevelTree.same_level_of_le hBA
                hMapParentLev.symm).symm
          have hParent : qa = qb :=
            ih (n-1) (by omega) qa qb hqaLev hMapParent
          have hDaCov : f qa ⋖ da :=
            S.covBy_of_succ_eq_some hMappedA
          have hDbCov : f qb ⋖ db :=
            S.covBy_of_succ_eq_some hMappedB
          have hDlev : LevelTree.lev da = LevelTree.lev db := by
            have hda := LevelTree.covBy_level_eq hDaCov
            have hdb := LevelTree.covBy_level_eq hDbCov
            omega
          have hDbSame : db ≤ f a := by
            rw [heq]
            exact hdbLe
          have hDsame : da = db := by
            rcases LevelTree.comparable_below hdaLe hDbSame with
                hAB | hBA
            · exact LevelTree.same_level_of_le hAB hDlev
            · exact (LevelTree.same_level_of_le hBA hDlev.symm).symm
          have hMappedBSame :
              S.succ (f qa) (pb.map f) cb = some da := by
            rw [hMapParent,hDsame]
            exact hMappedB
          have hMappedInputs := S.s2 hMappedA hMappedBSame
          have hParamMap : pa.map f = pb.map f := hMappedInputs.2.1
          have hLetter : ca = cb := hMappedInputs.2.2
          have hParamLow : ∀ x ∈ pa, LevelTree.lev x < n := by
            intro x hx
            have hh := S.parameter_level_lt hAstep hx
            rw [hqaLev] at hh
            omega
          have hParamInject :
              ∀ x ∈ pa, ∀ y, f x = f y → x = y := by
            intro x hx y hxy
            exact ih (LevelTree.lev x) (hParamLow x hx)
              x y rfl hxy
          have hParams : pa = pb :=
            list_map_injective_of_left_witnesses f hParamInject hParamMap
          have hBstepSame : S.succ qa pa ca = some b := by
            rw [hParent,hParams,hLetter]
            exact hBstep
          exact Option.some.inj (hAstep.symm.trans hBstepSame)
  intro a b heq
  exact hMain (LevelTree.lev a) a b rfl heq

end SuccessorTree

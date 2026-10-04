import SuccessorTree.ShapeAction
import SuccessorTree.Canonical
import Mathlib.Tactic

/-!
# Splitting a one-row shape map at an intermediate target level

This is the Lean form of Proposition `prop:shape-split` needed by the
fat-tree A4 trace recursion.  Repeated M2 lowering moves only the last
source level while preserving the frozen prefix.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

private theorem split_list_map_eq_self_of_mem_eq
    {α : Type u} (p : List α) (f : α → α)
    (h : ∀ x ∈ p, f x = x) :
    p.map f = p := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
      have hx : f x = x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons]
      rw [hx, ih hxs]

private theorem mmap_le_apply_of_fixesBelow
    (H : SMTree S) (F : MMap H) {n : Nat}
    (hF : F.FixesBelow H n)
    {x : T} (hx : LevelTree.lev x = n) :
    x ≤ F x := by
  cases n with
  | zero =>
      exact F.map.root_le' hx
  | succ n =>
      have hnle : n ≤ LevelTree.lev x := by omega
      let p := LevelTree.ancestor x n hnle
      have hpx : p ≤ x := LevelTree.ancestor_le x n hnle
      have hpLevel : LevelTree.lev p = n :=
        LevelTree.level_ancestor x n hnle
      have hcov : p ⋖ x := by
        apply LevelTree.covBy_of_le_level_succ hpx
        omega
      obtain ⟨params, c, hsucc⟩ := S.s3 hcov
      have hpfix : F p = p := by
        apply hF p
        omega
      have hparams : params.map F = params := by
        apply split_list_map_eq_self_of_mem_eq
        intro y hy
        apply hF y
        have hylt := S.parameter_level_lt hsucc hy
        omega
      obtain ⟨d, hd, hdx⟩ := F.map.weak_succ' hsucc
      have hd' : S.succ p params c = some d := by
        simpa [hpfix, hparams] using hd
      have hdeq : d = x :=
        Option.some.inj (hd'.symm.trans hsucc)
      simpa [hdeq] using hdx

/-- One application of M2 lowers the image of the moving source level by
exactly one, keeps the frozen prefix fixed, and moves every top image only
downwards in the tree. -/
theorem exists_lower_moving_level_once
    (H : SMTree S) (F : MMap H) (c : Nat)
    (hfix : F.FixesBelow H c)
    (hlt : c < H.levelMap F.map c) :
    ∃ G : MMap H,
      G.FixesBelow H c ∧
      H.levelMap G.map c = H.levelMap F.map c - 1 ∧
      ∀ x : T, LevelTree.lev x = c → G x ≤ F x := by
  by_cases hc0 : c = 0
  · subst c
    let t : Nat := H.levelMap F.map 0
    obtain ⟨a, ha⟩ := H.level_nonempty 0
    have hFa : LevelTree.lev (F a) = t := by
      dsimp [t]
      simpa [ha] using (H.levelMap_eq F.map (a := a)).symm
    have hpos : 0 < LevelTree.lev (F a) := by
      rw [hFa]
      simpa [t] using hlt
    have htpos : 0 < t := by
      simpa [t] using hlt
    have hskip : F.map.Skips (t - 1) := by
      intro hmem
      rw [← H.range_levelMap F.map] at hmem
      rcases hmem with ⟨k, hk⟩
      have hmono :=
        (H.levelMap_strictMono F.map).monotone (Nat.zero_le k)
      rw [hk] at hmono
      dsimp [t] at hmono
      omega
    have hskipFa :
        F.map.Skips (LevelTree.lev (F a) - 1) := by
      simpa [hFa] using hskip
    obtain ⟨F1, F2, hF1, hF2, hF2skip0, hagree⟩ :=
      H.m2 0 F.map F.mem a ha hpos hskipFa
    let G : MMap H := ⟨F1, hF1⟩
    let D : MMap H := ⟨F2, hF2⟩
    have hDskip : D.map.SkipsOnly (t - 1) := by
      simpa [D, hFa] using hF2skip0
    have hcomp : D (G a) = F a := by
      exact hagree a (by omega)
    have htarget : LevelTree.lev (G a) = t - 1 := by
      have hlev :
          LevelTree.lev (D (G a)) =
            if LevelTree.lev (G a) < t - 1
            then LevelTree.lev (G a)
            else LevelTree.lev (G a) + 1 := by
        calc
          LevelTree.lev (D (G a)) =
              H.levelMap D.map (LevelTree.lev (G a)) :=
            (H.levelMap_eq D.map (a := G a)).symm
          _ = _ :=
            H.levelMap_of_skipsOnly D.map (t - 1) hDskip
              (LevelTree.lev (G a))
      rw [hcomp, hFa] at hlev
      split at hlev <;> omega
    have hGtop : H.levelMap G.map 0 = t - 1 := by
      calc
        H.levelMap G.map 0 = LevelTree.lev (G a) := by
          simpa [ha] using H.levelMap_eq G.map (a := a)
        _ = t - 1 := htarget
    have hDfix : D.FixesBelow H (t - 1) := by
      intro x hx
      exact H.eq_id_below_skip D.map (t - 1) hDskip hx
    refine ⟨G, ?_, ?_, ?_⟩
    · intro x hx
      omega
    · simpa [t] using hGtop
    · intro x hx
      have hGlev : LevelTree.lev (G x) = t - 1 := by
        calc
          LevelTree.lev (G x) =
              H.levelMap G.map (LevelTree.lev x) :=
            (H.levelMap_eq G.map (a := x)).symm
          _ = H.levelMap G.map 0 := by rw [hx]
          _ = t - 1 := hGtop
      have hle : G x ≤ D (G x) :=
        mmap_le_apply_of_fixesBelow H D hDfix hGlev
      have hcompX : D (G x) = F x :=
        hagree x (by omega)
      simpa [hcompX] using hle
  · obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := by
      exact ⟨c - 1, by omega⟩
    have hFm : H.levelMap F.map m = m := by
      obtain ⟨a, ha⟩ := H.level_nonempty m
      have hfixa : F a = a := hfix a (by omega)
      calc
        H.levelMap F.map m = LevelTree.lev (F a) := by
          simpa [ha] using H.levelMap_eq F.map (a := a)
        _ = LevelTree.lev a := by rw [hfixa]
        _ = m := ha
    have hgap :
        H.levelMap F.map m + 1 <
          H.levelMap F.map (m + 1) := by
      rw [hFm]
      exact hlt
    obtain ⟨G, D, hGagree, hDskip, hDG, hGtop⟩ :=
      H.exists_lower_gap_once_factor F m hgap
    have hGfix : G.FixesBelow H (m + 1) := by
      intro x hx
      have hxle : LevelTree.lev x ≤ m := by omega
      rw [hGagree x hxle]
      exact hfix x hx
    let t : Nat := H.levelMap F.map (m + 1)
    have hDfix : D.FixesBelow H (t - 1) := by
      intro x hx
      exact H.eq_id_below_skip D.map (t - 1)
        (by simpa [t] using hDskip) hx
    refine ⟨G, hGfix, hGtop, ?_⟩
    intro x hx
    have hGlev : LevelTree.lev (G x) = t - 1 := by
      calc
        LevelTree.lev (G x) =
            H.levelMap G.map (LevelTree.lev x) :=
          (H.levelMap_eq G.map (a := x)).symm
        _ = H.levelMap G.map (m + 1) := by rw [hx]
        _ = t - 1 := by simpa [t] using hGtop
    have hle : G x ≤ D (G x) :=
      mmap_le_apply_of_fixesBelow H D hDfix hGlev
    have hcompX : D (G x) = F x :=
      hDG x (by omega)
    simpa [hcompX] using hle

namespace MMap

/-- If an admissible map fixes all levels strictly below `n`, then a node
on level `n` lies below its image. -/
theorem le_apply_at_cut
    (H : SMTree S) (F : MMap H) (n : Nat)
    (hF : F.FixesBelow H n)
    {x : T} (hx : LevelTree.lev x = n) :
    x ≤ F x :=
  mmap_le_apply_of_fixesBelow H F hF hx

end MMap

/-- The admissible target cuts in Proposition `prop:shape-split`.

For source level zero every target between zero and the current top is
allowed.  Above zero the cut must lie strictly above the image of the
preceding source level. -/
def SplitCut (H : SMTree S) (F : MMap H) (n m : Nat) : Prop :=
  m ≤ H.levelMap F.map n ∧
    match n with
    | 0 => True
    | k + 1 => H.levelMap F.map k < m

private theorem exists_lower_root_once_factor
    (H : SMTree S) (F : MMap H)
    (hlt : 0 < H.levelMap F.map 0) :
    ∃ G D : MMap H,
      D.FixesBelow H (H.levelMap F.map 0 - 1) ∧
      (∀ x : T, LevelTree.lev x ≤ 0 → D (G x) = F x) ∧
      H.levelMap G.map 0 = H.levelMap F.map 0 - 1 := by
  let t : Nat := H.levelMap F.map 0
  obtain ⟨a, ha⟩ := H.level_nonempty 0
  have hFa : LevelTree.lev (F a) = t := by
    dsimp [t]
    simpa [ha] using (H.levelMap_eq F.map (a := a)).symm
  have hpos : 0 < LevelTree.lev (F a) := by
    rw [hFa]
    simpa [t] using hlt
  have hskip : F.map.Skips (t - 1) := by
    intro hmem
    rw [← H.range_levelMap F.map] at hmem
    rcases hmem with ⟨k, hk⟩
    have hmono :=
      (H.levelMap_strictMono F.map).monotone (Nat.zero_le k)
    rw [hk] at hmono
    dsimp [t] at hmono
    omega
  have hskipFa :
      F.map.Skips (LevelTree.lev (F a) - 1) := by
    simpa [hFa] using hskip
  obtain ⟨F1, F2, hF1, hF2, hF2skip0, hagree⟩ :=
    H.m2 0 F.map F.mem a ha hpos hskipFa
  let G : MMap H := ⟨F1, hF1⟩
  let D : MMap H := ⟨F2, hF2⟩
  have hDskip : D.map.SkipsOnly (t - 1) := by
    simpa [D, hFa] using hF2skip0
  have hcomp : D (G a) = F a :=
    hagree a (by omega)
  have htarget : LevelTree.lev (G a) = t - 1 := by
    have hlev :
        LevelTree.lev (D (G a)) =
          if LevelTree.lev (G a) < t - 1
          then LevelTree.lev (G a)
          else LevelTree.lev (G a) + 1 := by
      calc
        LevelTree.lev (D (G a)) =
            H.levelMap D.map (LevelTree.lev (G a)) :=
          (H.levelMap_eq D.map (a := G a)).symm
        _ = _ :=
          H.levelMap_of_skipsOnly D.map (t - 1) hDskip
            (LevelTree.lev (G a))
    rw [hcomp, hFa] at hlev
    split at hlev <;> omega
  have hGtop : H.levelMap G.map 0 = t - 1 := by
    calc
      H.levelMap G.map 0 = LevelTree.lev (G a) := by
        simpa [ha] using H.levelMap_eq G.map (a := a)
      _ = t - 1 := htarget
  have hDfix : D.FixesBelow H (t - 1) := by
    intro x hx
    exact H.eq_id_below_skip D.map (t - 1) hDskip hx
  exact ⟨G, D, by simpa [t] using hDfix, hagree, by simpa [t] using hGtop⟩

/-- Full factor form of Proposition `prop:shape-split`.

The prefix map `P` agrees with `F` strictly below the moving source
level and lands that level exactly on the chosen target cut `m`.
The outer factor `Q` fixes everything below `m` and satisfies
`Q (P x) = F x` through the moving source level. -/
theorem exists_shapeSplit_factor
    (H : SMTree S) (F : MMap H) (n m : Nat)
    (hcut : SplitCut H F n m) :
    ∃ P Q : MMap H,
      (∀ x : T, LevelTree.lev x < n → P x = F x) ∧
      H.levelMap P.map n = m ∧
      Q.FixesBelow H m ∧
      (∀ x : T, LevelTree.lev x ≤ n → Q (P x) = F x) := by
  have main :
      ∀ top : Nat, ∀ K : MMap H,
        H.levelMap K.map n = top →
        SplitCut H K n m →
        ∃ P Q : MMap H,
          (∀ x : T, LevelTree.lev x < n → P x = K x) ∧
          H.levelMap P.map n = m ∧
          Q.FixesBelow H m ∧
          (∀ x : T, LevelTree.lev x ≤ n → Q (P x) = K x) := by
    intro top
    induction top using Nat.strong_induction_on with
    | h top ih =>
        intro K hKtop hKcut
        have hmtop : m ≤ top := by
          exact hKcut.1.trans_eq hKtop
        by_cases hEq : m = top
        · refine ⟨K, MMap.id H, ?_, ?_, ?_, ?_⟩
          · intro x hx
            rfl
          · exact hKtop.trans hEq.symm
          · exact MMap.id_fixesBelow H m
          · intro x hx
            rfl
        · have hmlt : m < top := by omega
          cases n with
          | zero =>
              change m ≤ H.levelMap K.map 0 ∧ True at hKcut
              have htopPos : 0 < H.levelMap K.map 0 := by
                rw [hKtop]
                omega
              obtain ⟨G, D, hDfixTop, hDG, hGtop0⟩ :=
                exists_lower_root_once_factor H K htopPos
              have hGtop : H.levelMap G.map 0 = top - 1 := by
                rw [hGtop0, hKtop]
              have hsmall : top - 1 < top := by omega
              have hmG : m ≤ top - 1 := by omega
              have hGcut : SplitCut H G 0 m := by
                exact ⟨by simpa [hGtop] using hmG, trivial⟩
              obtain ⟨P, Q, hPagree, hPtop, hQfix, hQP⟩ :=
                ih (top - 1) hsmall G hGtop hGcut
              have hDfixTop' : D.FixesBelow H (top - 1) := by
                intro x hx
                apply hDfixTop x
                simpa [hKtop] using hx
              have hDfixm : D.FixesBelow H m := by
                intro x hx
                apply hDfixTop' x
                have hmTop : m ≤ top - 1 := by omega
                exact lt_of_lt_of_le hx hmTop
              let R : MMap H := MMap.comp H D Q
              refine ⟨P, R, ?_, hPtop, ?_, ?_⟩
              · intro x hx
                omega
              · exact MMap.comp_fixesBelow H D Q m hDfixm hQfix
              · intro x hx
                change D (Q (P x)) = K x
                rw [hQP x hx]
                exact hDG x hx
          | succ k =>
              change
                m ≤ H.levelMap K.map (k + 1) ∧
                  H.levelMap K.map k < m at hKcut
              have hgap :
                  H.levelMap K.map k + 1 <
                    H.levelMap K.map (k + 1) := by
                rw [hKtop]
                omega
              obtain ⟨G, D, hGagree, hDskip0, hDG, hGtop0⟩ :=
                H.exists_lower_gap_once_factor K k hgap
              have hGtop :
                  H.levelMap G.map (k + 1) = top - 1 := by
                rw [hGtop0, hKtop]
              have hGk :
                  H.levelMap G.map k = H.levelMap K.map k := by
                obtain ⟨a, ha⟩ := H.level_nonempty k
                calc
                  H.levelMap G.map k = LevelTree.lev (G a) := by
                    simpa [ha] using H.levelMap_eq G.map (a := a)
                  _ = LevelTree.lev (K a) := by
                    rw [hGagree a (by omega)]
                  _ = H.levelMap K.map k := by
                    simpa [ha] using (H.levelMap_eq K.map (a := a)).symm
              have hsmall : top - 1 < top := by omega
              have hmG : m ≤ top - 1 := by omega
              have hGcut : SplitCut H G (k + 1) m := by
                refine ⟨?_, ?_⟩
                · simpa [hGtop] using hmG
                · simpa [hGk] using hKcut.2
              obtain ⟨P, Q, hPagree, hPtop, hQfix, hQP⟩ :=
                ih (top - 1) hsmall G hGtop hGcut
              have hDskip :
                  D.map.SkipsOnly (top - 1) := by
                simpa [hKtop] using hDskip0
              have hDfixTop : D.FixesBelow H (top - 1) := by
                intro x hx
                exact H.eq_id_below_skip D.map (top - 1) hDskip hx
              have hDfixm : D.FixesBelow H m := by
                intro x hx
                apply hDfixTop x
                have hmTop : m ≤ top - 1 := by omega
                exact lt_of_lt_of_le hx hmTop
              let R : MMap H := MMap.comp H D Q
              refine ⟨P, R, ?_, hPtop, ?_, ?_⟩
              · intro x hx
                calc
                  P x = G x := hPagree x hx
                  _ = K x := hGagree x (by omega)
              · exact MMap.comp_fixesBelow H D Q m hDfixm hQfix
              · intro x hx
                change D (Q (P x)) = K x
                rw [hQP x hx]
                exact hDG x hx
  exact main (H.levelMap F.map n) F rfl hcut

/-- Top-level consequence of a shape split: the new top image lies below
the old top image, and its level is the chosen split cut. -/
theorem shapeSplit_top_le_level
    (H : SMTree S)
    (F P Q : MMap H) (n m : Nat)
    (hPtop : H.levelMap P.map n = m)
    (hQfix : Q.FixesBelow H m)
    (hQP : ∀ x : T, LevelTree.lev x ≤ n → Q (P x) = F x)
    {x : T} (hx : LevelTree.lev x = n) :
    P x ≤ F x ∧ LevelTree.lev (P x) = m := by
  have hPlev :
      LevelTree.lev (P x) = m := by
    calc
      LevelTree.lev (P x) =
          H.levelMap P.map n := by
        simpa [hx] using (H.levelMap_eq P.map (a := x)).symm
      _ = m := hPtop
  have hle0 :
      P x ≤ Q (P x) :=
    Q.le_apply_at_cut H m hQfix hPlev
  have hle : P x ≤ F x := by
    rw [hQP x (by omega)] at hle0
    exact hle0
  exact ⟨hle, hPlev⟩

/-- Lower the moving source level to an arbitrary admissible intermediate
target level. -/
theorem exists_truncate_moving_level
    (H : SMTree S) (F : MMap H)
    (c d : Nat)
    (hfix : F.FixesBelow H c)
    (hcd : c ≤ d)
    (hdt : d ≤ H.levelMap F.map c) :
    ∃ G : MMap H,
      G.FixesBelow H c ∧
      H.levelMap G.map c = d ∧
      ∀ x : T, LevelTree.lev x = c → G x ≤ F x := by
  have main :
      ∀ t : Nat, ∀ K : MMap H,
        K.FixesBelow H c →
        H.levelMap K.map c = t →
        d ≤ t →
        ∃ G : MMap H,
          G.FixesBelow H c ∧
          H.levelMap G.map c = d ∧
          ∀ x : T, LevelTree.lev x = c → G x ≤ K x := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        intro K hKfix hKt hdt'
        by_cases hEq : d = t
        · refine ⟨K, hKfix, ?_, ?_⟩
          · simpa [hEq] using hKt
          · intro x hx
            exact le_rfl
        · have hdl : d < t := by omega
          have hct : c < t := lt_of_le_of_lt hcd hdl
          have hltK : c < H.levelMap K.map c := by
            rw [hKt]
            exact hct
          obtain ⟨G, hGfix, hGtop, hGK⟩ :=
            exists_lower_moving_level_once H K c hKfix hltK
          have hGt : H.levelMap G.map c = t - 1 := by
            rw [hGtop, hKt]
          have hsmall : t - 1 < t := by omega
          have hdG : d ≤ t - 1 := by omega
          obtain ⟨P, hPfix, hPtop, hPG⟩ :=
            ih (t - 1) hsmall G hGfix hGt hdG
          refine ⟨P, hPfix, hPtop, ?_⟩
          intro x hx
          exact (hPG x hx).trans (hGK x hx)
  exact main (H.levelMap F.map c) F hfix rfl hdt

private theorem toAM_one_representative_agrees_split
    (H : SMTree S) (F : MMap H) (c : Nat)
    (hfix : F.FixesBelow H c)
    (x : T) (hx : LevelTree.lev x ≤ c) :
    ((F.toAM H c 1 hfix).representative H) x = F x := by
  let q : AM H c 1 := F.toAM H c 1 hfix
  have hrep := q.representative_top H
  have hval := congrArg Subtype.val hrep
  change (q.representative H).restrictLe H c =
    F.restrictLe H c at hval
  exact congrFun hval ⟨x, hx⟩

/-- One-row form of Proposition `prop:shape-split`.

A finite row can be truncated at every intermediate target level.  The
chosen representative of the truncated row maps every source-level point
below the corresponding point of the original row. -/
theorem exists_truncate_oneRow
    (H : SMTree S)
    {c : Nat} (theta : AM H c 1)
    (d : Nat)
    (hcd : c ≤ d)
    (hdt : d ≤ theta.topLevel H) :
    ∃ q : AM H c 1,
      q.topLevel H = d ∧
      ∀ x : T, LevelTree.lev x = c →
        q.representative H x ≤ theta.representative H x := by
  let F : MMap H := theta.representative H
  have hFfix : F.FixesBelow H c :=
    theta.representative_fixesBelow H
  obtain ⟨P, hPfix, hPtop, hPF⟩ :=
    exists_truncate_moving_level H F c d hFfix hcd hdt
  let q : AM H c 1 := P.toAM H c 1 hPfix
  have hqtop : q.topLevel H = d := by
    obtain ⟨a, ha⟩ := H.level_nonempty c
    have hqa : q.representative H a = P a :=
      toAM_one_representative_agrees_split H P c hPfix a (by omega)
    unfold AM.topLevel
    calc
      H.levelMap (q.representative H).map c =
          LevelTree.lev (q.representative H a) := by
        simpa [ha] using H.levelMap_eq (q.representative H).map (a := a)
      _ = LevelTree.lev (P a) := by rw [hqa]
      _ = H.levelMap P.map c := by
        simpa [ha] using (H.levelMap_eq P.map (a := a)).symm
      _ = d := hPtop
  refine ⟨q, hqtop, ?_⟩
  intro x hx
  have hqP : q.representative H x = P x :=
    toAM_one_representative_agrees_split H P c hPfix x (by omega)
  rw [hqP]
  exact hPF x hx

end SMTree
end SuccessorTree

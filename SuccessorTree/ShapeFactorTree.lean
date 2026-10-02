import SuccessorTree.ShapeTransportAlphabet
import SuccessorTree.ShapeAction
import Mathlib.Tactic

/-!
# The finite-factor tree of one-moving-level shape maps

Every nontrivial member of AM^n_1 can be peeled by M2 at its last target
level. The predecessor ends exactly one target level earlier and the outer
factor is a genuine one-level letter at that predecessor level.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Exact target-level slice of AM^n_1. -/
abbrev AMExact
    (H : SMTree S) (n m : Nat) :=
  {g : AM H n 1 // g.topLevel H = m}

/-- A one-level factor applied after a predecessor word. -/
noncomputable def factorEdgeApply
    (H : SMTree S)
    {n m : Nat}
    (p : AMExact H n m)
    (e : OneLevelLetter H m) :
    AM H n 1 :=
  (MMap.comp H e.toMMap (p.1.representative H)).toAM H n 1
    (MMap.comp_fixesBelow H e.toMMap (p.1.representative H) n
      (by
        intro x hx
        exact e.eq_id_below H
          (lt_trans hx (by
            have hnm : n ≤ m := by
              have hge := H.levelMap_id_le (p.1.representative H).map n
              rw [← p.2] at hge
              exact hge
            exact lt_of_lt_of_le hx hnm)))
      p.1.representative_fixesBelow)

/-- Applying one factor raises the exact terminal level by one. -/
theorem factorEdgeApply_topLevel
    (H : SMTree S)
    {n m : Nat}
    (p : AMExact H n m)
    (e : OneLevelLetter H m) :
    (H.factorEdgeApply p e).topLevel H = m + 1 := by
  unfold factorEdgeApply AM.topLevel
  rw [H.levelMap_comp e.toMMap (p.1.representative H) n]
  rw [p.2]
  rw [H.levelMap_of_skipsOnly e.toMMap.map m e.skips]
  simp

/-- Exact target slices are finite. -/
noncomputable instance amExactFintype
    (H : SMTree S) (n m : Nat) :
    Fintype (AMExact H n m) := by
  classical
  let B : Type u := AMBelow H n (m + 1)
  letI : Fintype B := amBelowFintype H n (m + 1)
  let S' : Finset B :=
    Finset.univ.filter (fun g => g.1.topLevel H = m)
  let e : AMExact H n m ≃ {g : B // g ∈ S'} where
    toFun g := by
      let b : B := ⟨g.1, by rw [g.2]; omega⟩
      refine ⟨b, ?_⟩
      simp [S', b, g.2]
    invFun g := ⟨g.1.1, by
      have hg := g.2
      simp [S'] at hg
      exact hg⟩
    left_inv g := by
      apply Subtype.ext
      rfl
    right_inv g := by
      apply Subtype.ext
      rfl
  exact Fintype.ofEquiv _ e.symm

/-- M2 predecessor factorisation for one-moving-level words.

If g ends at m>n, then on its whole finite source domain it is a one-level
letter at m-1 applied after a predecessor ending at m-1. -/
theorem exists_factor_predecessor
    (H : SMTree S)
    {n m : Nat}
    (g : AMExact H n m)
    (hnm : n < m) :
    ∃ p : AMExact H n (m - 1),
      ∃ e : OneLevelLetter H (m - 1),
        g.1 = H.factorEdgeApply p e := by
  let G : MMap H := g.1.representative H
  have hGtop : H.levelMap G.map n = m := g.2
  have hcut : SplitCut H G n (m - 1) := by
    constructor
    · rw [hGtop]
      omega
    · cases n with
      | zero => trivial
      | succ j =>
          have hfix := g.1.representative_fixesBelow H
          have hGj :
              H.levelMap G.map j = j := by
            exact H.levelMap_eq_of_fixesBelow G (j + 1) hfix
              (Nat.lt_succ_self j)
          rw [hGj]
          omega
  obtain ⟨P, Q, hPagree, hPtop, hQfix, hQP⟩ :=
    H.exists_shapeSplit_factor G n (m - 1) hcut
  have hPfix : P.FixesBelow H n := by
    intro x hx
    calc
      P x = G x := hPagree x hx
      _ = x := g.1.representative_fixesBelow H x hx
  let p0 : AM H n 1 := P.toAM H n 1 hPfix
  have hpTop : p0.topLevel H = m - 1 := by
    unfold AM.topLevel
    have hrep := AM.representative_top H p0
    have hval := congrArg Subtype.val hrep
    change (p0.representative H).restrictLe H n = P.restrictLe H n at hval
    obtain ⟨x, hx⟩ := H.level_nonempty n
    have hpoint := congrFun hval ⟨x, by simpa [hx]⟩
    calc
      H.levelMap (p0.representative H).map n =
          LevelTree.lev (p0.representative H x) := by
        simpa [hx] using H.levelMap_eq (p0.representative H).map (a := x)
      _ = LevelTree.lev (P x) := by rw [hpoint]
      _ = H.levelMap P.map n := by
        simpa [hx] using (H.levelMap_eq P.map (a := x)).symm
      _ = m - 1 := hPtop
  let p : AMExact H n (m - 1) := ⟨p0, hpTop⟩
  have hQtop :
      H.levelMap Q.map (m - 1) = m := by
    obtain ⟨x, hx⟩ := H.level_nonempty n
    have hPx : LevelTree.lev (P x) = m - 1 := by
      calc
        LevelTree.lev (P x) =
            H.levelMap P.map n := by
          simpa [hx] using (H.levelMap_eq P.map (a := x)).symm
        _ = m - 1 := hPtop
    calc
      H.levelMap Q.map (m - 1) =
          LevelTree.lev (Q (P x)) := by
        simpa [hPx] using H.levelMap_eq Q.map (a := P x)
      _ = LevelTree.lev (G x) := by
        rw [hQP x (by simpa [hx])]
      _ = H.levelMap G.map n := by
        simpa [hx] using (H.levelMap_eq G.map (a := x)).symm
      _ = m := hGtop
  let e : OneLevelLetter H (m - 1) := by
    refine ⟨H.canonicalExtension Q (m - 1), ?_⟩
    exact H.canonicalExtension_skipsOnly_of_oneStep
      Q (m - 1) hQfix (by
        have hmpos : 0 < m := lt_trans (Nat.zero_le n) hnm
        have hm : (m - 1) + 1 = m := by omega
        simpa [hm] using hQtop)
  refine ⟨p, e, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext y
  have hGfinite := g.1.representative_top H
  have hGval := congrArg Subtype.val hGfinite
  change G.restrictLe H n = g.1.1 at hGval
  have hgY := congrFun hGval y
  have hpfinite := p.1.representative_top H
  have hpval := congrArg Subtype.val hpfinite
  change (p.1.representative H).restrictLe H n = p.1.1 at hpval
  have hpY := congrFun hpval y
  have hPfinite : p.1.1 y = P y.1 := by
    change p0.1.1 y = P y.1
    rfl
  have hPyLev : LevelTree.lev (P y.1) ≤ m - 1 := by
    calc
      LevelTree.lev (P y.1) =
          H.levelMap P.map (LevelTree.lev y.1) :=
        (H.levelMap_eq P.map (a := y.1)).symm
      _ ≤ H.levelMap P.map n :=
        (H.levelMap_strictMono P.map).monotone y.2
      _ = m - 1 := hPtop
  change g.1.1 y =
    H.canonicalExtension Q (m - 1)
      (p.1.representative H y.1)
  rw [← hgY]
  have hpRepEq : p.1.representative H y.1 = P y.1 := by
    calc
      p.1.representative H y.1 = p.1.1 y := hpY
      _ = P y.1 := hPfinite
  rw [hpRepEq]
  rw [H.canonicalExtension_agrees Q (m - 1) (P y.1) hPyLev]
  exact (hQP y.1 y.2).symm

/-- The root of the factor tree is the identity word. -/
theorem amExact_base_unique
    (H : SMTree S) (n : Nat)
    (g : AMExact H n n) :
    g.1 = AM.id1 H n := by
  apply AM.eq_id1_of_topLevel_le H g.1
  rw [g.2]

end SMTree
end SuccessorTree

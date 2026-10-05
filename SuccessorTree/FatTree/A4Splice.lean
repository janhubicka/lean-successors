import SuccessorTree.FatTree.A4Trace

/-!
# A reusable one-block geometric splice

The criterion is the full successor-lift inclusion, not a factorisation
through a chosen representative. It is independent of pigeonhole and A4.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- A row whose whole successor lift follows an ambient interval can replace
that interval, preserving every earlier row and the terminal cut. -/
theorem appendRow_stemAt_of_oneLift
    (U : FatTree H) (a b : Nat) (hab : a < b)
    (h : AM H (U.cut a) 1)
    (hend : h.rowEndLevel H + 1 = U.cut b)
    (hlift :
      H.canonicalExtension (h.representative H) (U.cut a) ''
          ImmediateSuccessors (T := T) (TreeLevel (T := T) (U.cut a)) ⊆
        U.liftTo H a b (Nat.le_of_lt hab)
          (TreeLevel (T := T) (U.cut a))) :
    StemAt H (FiniteFatTree.appendRow H (U.initialSegment H a) h) U b := by
  let x := U.initialSegment H a
  let V := FiniteFatTree.appendRow H x h
  let Z := U.initialSegment H b
  let idx : Fin (V.height + 1) → Fin (Z.height + 1) := fun k =>
    if hk : k.1 ≤ a then ⟨k.1, by change k.1 < b + 1; omega⟩
    else ⟨b, by change b < b + 1; omega⟩
  have idx_old (k : Fin (V.height + 1)) (hk : k.1 ≤ a) :
      (idx k).1 = k.1 := by simp only [idx, dif_pos hk]
  have idx_last (k : Fin (V.height + 1)) (hk : ¬ k.1 ≤ a) :
      (idx k).1 = b := by simp only [idx, dif_neg hk]
  have hstrict : StrictMono idx := by
    intro p q hpq
    have hpq' : p.1 < q.1 := hpq
    change (idx p).1 < (idx q).1
    by_cases hq : q.1 ≤ a
    · rw [idx_old q hq, idx_old p (by omega)]
      exact hpq'
    · have hqb : q.1 < a + 2 := q.2
      rw [idx_last q hq, idx_old p (by omega)]
      omega
  have hcut (k : Fin (V.height + 1)) : V.cut k = U.cut (idx k).1 := by
    by_cases hk : k.1 ≤ a
    · let k0 : Fin (x.height + 1) := ⟨k.1, by change k.1 < a + 1; omega⟩
      have heq : k0.castSucc = k := Fin.ext rfl
      calc
        V.cut k = V.cut k0.castSucc := congrArg V.cut heq.symm
        _ = x.cut k0 := FiniteFatTree.appendRow_cut_old H x h k0
        _ = U.cut k.1 := rfl
        _ = U.cut (idx k).1 := congrArg U.cut (idx_old k hk).symm
    · have hkb : k.1 < a + 2 := k.2
      have heq : k = Fin.last V.height := Fin.ext (by change k.1 = a + 1; omega)
      calc
        V.cut k = V.terminalCut := by rw [heq]; rfl
        _ = h.rowEndLevel H + 1 := FiniteFatTree.appendRow_terminalCut H x h
        _ = U.cut b := hend
        _ = U.cut (idx k).1 := congrArg U.cut (idx_last k hk).symm
  have hstep (r : Fin V.height) :
      V.oneLift H r (TreeLevel (T := T) (V.cut r.castSucc)) ⊆
        Z.liftTo H (idx r.castSucc) (idx r.succ)
          (le_of_lt (hstrict (by change r.1 < r.1 + 1; omega)))
          (TreeLevel (T := T) (Z.cut (idx r.castSucc))) := by
    rw [U.initialSegment_liftTo H b]
    change V.oneLift H r (TreeLevel (T := T) (V.cut r.castSucc)) ⊆
      U.liftTo H (idx r.castSucc).1 (idx r.succ).1 _
        (TreeLevel (T := T) (U.cut (idx r.castSucc).1))
    have hrb : r.1 < a + 1 := r.2
    have hi0 : (idx r.castSucc).1 = r.1 := idx_old _ (by change r.1 ≤ a; omega)
    by_cases hr : r.1 < a
    · have hi1 : (idx r.succ).1 = r.1 + 1 := idx_old _ (by change r.1 + 1 ≤ a; omega)
      have hrow : V.rowExtension H r = U.rowExtension H r.1 := by
        let r0 : Fin x.height := ⟨r.1, hr⟩
        have heq : r0.castSucc = r := Fin.ext rfl
        have hc : V.cut r.castSucc = x.cut r0.castSucc := by
          rw [← heq]
          exact FiniteFatTree.appendRow_cut_old H x h r0.castSucc
        have he : HEq (V.row r) (x.row r0) := by
          rw [← heq]
          exact FiniteFatTree.appendRow_row_old H x h r0
        exact canonicalExtension_eq_of_row_heq H hc he
      have hs : V.oneLift H r (TreeLevel (T := T) (V.cut r.castSucc)) =
          U.oneLift H r.1 (TreeLevel (T := T) (U.cut r.1)) := by
        unfold FiniteFatTree.oneLift FatTree.oneLift
        rw [hrow, hcut r.castSucc, hi0]
      rw [hs]
      simpa only [hi0, hi1, U.liftTo_succ H] using
        (Set.Subset.refl (U.oneLift H r.1 (TreeLevel (T := T) (U.cut r.1))))
    · have hre : r.1 = a := by omega
      have hi1 : (idx r.succ).1 = b := idx_last _ (by change ¬ r.1 + 1 ≤ a; omega)
      have heq : r = Fin.last x.height := Fin.ext hre
      have hs : V.oneLift H r (TreeLevel (T := T) (V.cut r.castSucc)) =
          H.canonicalExtension (h.representative H) (U.cut a) ''
            ImmediateSuccessors (T := T) (TreeLevel (T := T) (U.cut a)) := by
        rw [hcut r.castSucc, hi0, hre, heq]
        exact FiniteFatTree.appendRow_oneLift_last H x h _
      rw [hs]
      simpa only [hi0, hi1, hre] using hlift
  refine ⟨⟨{ index := idx, index_strict := hstrict,
    cut_eq := hcut, lift_subset := hstep }⟩, ?_⟩
  change V.terminalCut = U.cut b
  exact (FiniteFatTree.appendRow_terminalCut H x h).trans hend

end SuccessorTree.SMTree.FatTree

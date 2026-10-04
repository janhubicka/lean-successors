import SuccessorTree.FatTree.A4History

/-!
# Transport and replay of all-trace successor-fan profiles

Two facts are isolated here.

* Passing one history step through the current ambient row preserves the
  complete raw successor-fan profile, including bottom coordinates.
* If that transported occurrence lies below a later history state, the M3
  duplication from the occurrence level to the later level reproduces exactly
  the same profile.  The reverse implication is what keeps bottom coordinates
  bottom.

These are the finite structural facts behind the maximal-profile replay in
the all-trace proof of A4.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

private theorem list_map_eq_self_of_fixed
    (p : List T) (F : MMap H)
    (h : ∀ x ∈ p, F x = x) :
    p.map F = p := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
      have hx : F x = x := h x (by simp)
      have hxs : ∀ y ∈ xs, F y = y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons, hx, ih hxs]

/-- Transport a current-cut letter through the current ambient row.  Its new
skip level is the last image level of that row. -/
noncomputable def rowTransportLetter
    (U : FatTree H) (i : Nat)
    (E : OneLevelLetter H (U.cut i)) :
    OneLevelLetter H ((U.row i).rowEndLevel H) :=
  H.transportLetter ((U.row i).representative H) (U.cut i) E

/-- The history before the transported letter: first apply the old history,
then the canonical ambient row. -/
def rowTransportBase
    (U : FatTree H) (i : Nat) (P : MMap H) : MMap H :=
  MMap.comp H (U.rowExtension H i) P

/-- On every point through the current cut, the transported letter commutes
with the canonical ambient row. -/
theorem rowTransportLetter_commutes
    (U : FatTree H) (i : Nat)
    (E : OneLevelLetter H (U.cut i))
    (x : T) (hx : LevelTree.lev x ≤ U.cut i) :
    rowTransportLetter H U i E (U.rowExtension H i x) =
      U.rowExtension H i (E.toMMap x) := by
  exact H.transportLetter_commutes
    ((U.row i).representative H) (U.cut i) E x hx

/-- Transporting a history step through one ambient row preserves realization
of every fixed raw fan. -/
theorem historyRealizesFan_rowTransport_iff
    {c : Nat}
    (U : FatTree H) (i : Nat)
    (q : AM H c 1)
    (P : MMap H)
    (E : OneLevelLetter H (U.cut i))
    (e : RawSuccessorFan H q)
    (hPtop :
      H.levelMap P.map (q.rowEndLevel H) = U.cut i) :
    HistoryRealizesFan H q P E e ↔
      HistoryRealizesFan H q
        (rowTransportBase H U i P)
        (rowTransportLetter H U i E) e := by
  let R : MMap H := U.rowExtension H i
  have hqle : q.rowEndLevel H ≤ U.cut i := by
    exact (H.levelMap_id_le P.map (q.rowEndLevel H)).trans_eq hPtop
  have pointLevel :
      ∀ (x : InitialNode T c),
        LevelTree.lev x.1 = c →
          LevelTree.lev (P (q.representative H x.1)) = U.cut i := by
    intro x hx
    calc
      LevelTree.lev (P (q.representative H x.1)) =
          H.levelMap P.map
            (LevelTree.lev (q.representative H x.1)) :=
        (H.levelMap_eq P.map
          (a := q.representative H x.1)).symm
      _ = H.levelMap P.map (q.rowEndLevel H) := by
        congr 1
        calc
          LevelTree.lev (q.representative H x.1) =
              H.levelMap (q.representative H).map
                (LevelTree.lev x.1) :=
            (H.levelMap_eq (q.representative H).map (a := x.1)).symm
          _ = H.levelMap (q.representative H).map c := by rw [hx]
          _ = q.rowEndLevel H := rfl
      _ = U.cut i := hPtop
  have rowConsecutive :
      H.levelMap R.map (U.cut i + 1) =
        H.levelMap R.map (U.cut i) + 1 := by
    rw [show H.levelMap R.map (U.cut i + 1) = U.cut (i + 1) by
      simpa [R] using U.rowExtension_level_succ H i]
    rw [show H.levelMap R.map (U.cut i) =
      (U.row i).rowEndLevel H by
        simpa [R] using U.rowExtension_level_at_cut H i]
    exact (U.row_cut i).symm
  constructor
  · intro he x hx
    let code := e.code H x hx
    have hs := he x hx
    have hbase := pointLevel x hx
    have hend :
        LevelTree.lev (E.toMMap (P (q.representative H x.1))) =
          U.cut i + 1 :=
      E.level_succ_at H hbase
    have hlevels :
        H.levelMap R.map
            (LevelTree.lev (E.toMMap (P (q.representative H x.1)))) =
          H.levelMap R.map
            (LevelTree.lev (P (q.representative H x.1))) + 1 := by
      rw [hend, hbase]
      exact rowConsecutive
    have hparams :
        code.params.map R = code.params := by
      apply list_map_eq_self_of_fixed H
      intro z hz
      apply U.rowExtension_fixesBelow H i
      have hzlt :=
        S.parameter_level_lt code.succ_eq hz
      have hqlev :
          LevelTree.lev (q.representative H x.1) =
            q.rowEndLevel H := by
        calc
          LevelTree.lev (q.representative H x.1) =
              H.levelMap (q.representative H).map
                (LevelTree.lev x.1) :=
            (H.levelMap_eq (q.representative H).map (a := x.1)).symm
          _ = H.levelMap (q.representative H).map c := by rw [hx]
          _ = q.rowEndLevel H := rfl
      rw [hqlev] at hzlt
      exact lt_of_lt_of_le hzlt hqle
    have htrans :=
      H.succ_eq_of_consecutive_levels R.map hs hlevels
    rw [hparams] at htrans
    change
      S.succ
          ((rowTransportBase H U i P)
            (q.representative H x.1))
          code.params code.char =
        some
          ((rowTransportLetter H U i E)
            ((rowTransportBase H U i P)
              (q.representative H x.1)))
    change
      S.succ
          (R (P (q.representative H x.1)))
          code.params code.char =
        some
          ((rowTransportLetter H U i E)
            (R (P (q.representative H x.1))))
    rw [rowTransportLetter_commutes H U i E
      (P (q.representative H x.1)) (Nat.le_of_eq hbase)]
    exact htrans
  · intro hout x hx
    let z := P (q.representative H x.1)
    have hzlev : LevelTree.lev z = U.cut i := pointLevel x hx
    let actual := H.letterCode E z hzlev
    have hactual := actual.succ_eq
    have hend :
        LevelTree.lev (E.toMMap z) = U.cut i + 1 :=
      E.level_succ_at H hzlev
    have hlevels :
        H.levelMap R.map (LevelTree.lev (E.toMMap z)) =
          H.levelMap R.map (LevelTree.lev z) + 1 := by
      rw [hend, hzlev]
      exact rowConsecutive
    have hparams :
        actual.params.map R = actual.params := by
      apply list_map_eq_self_of_fixed H
      intro p hp
      apply U.rowExtension_fixesBelow H i
      exact S.parameter_level_lt actual.succ_eq hp
    have hactualR :=
      H.succ_eq_of_consecutive_levels R.map hactual hlevels
    rw [hparams] at hactualR
    have hcomm :
        (rowTransportLetter H U i E) (R z) = R (E.toMMap z) :=
      rowTransportLetter_commutes H U i E z (Nat.le_of_eq hzlev)
    rw [← hcomm] at hactualR
    have houtx := hout x hx
    change
      S.succ (R z) (e.code H x hx).params
          (e.code H x hx).char =
        some ((rowTransportLetter H U i E) (R z)) at houtx
    have hsame := S.s2 houtx hactualR
    have hp : (e.code H x hx).params = actual.params := hsame.2.1
    have hc : (e.code H x hx).char = actual.char := hsame.2.2
    rw [hp, hc]
    exact hactual

/-- Consequently the whole option-valued profile, including its bottom
case, is unchanged by transport through the ambient row. -/
theorem historyProfile_rowTransport
    {c : Nat}
    (U : FatTree H) (i : Nat)
    (q : AM H c 1)
    (P : MMap H)
    (E : OneLevelLetter H (U.cut i))
    (hPtop :
      H.levelMap P.map (q.rowEndLevel H) = U.cut i) :
    historyProfile H q
        (rowTransportBase H U i P)
        (rowTransportLetter H U i E) =
      historyProfile H q P E := by
  classical
  by_cases h :
      ∃ e : RawSuccessorFan H q,
        HistoryRealizesFan H q P E e
  · rcases h with ⟨e, he⟩
    have he' :
        HistoryRealizesFan H q
          (rowTransportBase H U i P)
          (rowTransportLetter H U i E) e :=
      (historyRealizesFan_rowTransport_iff H U i q P E e hPtop).1 he
    rw [historyProfile_eq_some H q P E e he]
    rw [historyProfile_eq_some H q
      (rowTransportBase H U i P)
      (rowTransportLetter H U i E) e he']
  · have h' :
      ¬ ∃ e : RawSuccessorFan H q,
          HistoryRealizesFan H q
            (rowTransportBase H U i P)
            (rowTransportLetter H U i E) e := by
      intro hex
      rcases hex with ⟨e, he⟩
      exact h ⟨e,
        (historyRealizesFan_rowTransport_iff H U i q P E e hPtop).2 he⟩
    unfold historyProfile
    rw [dif_neg h, dif_neg h']

/-- M3 replay from a recorded occurrence to a later history point preserves
realization of a raw fan in both directions. -/
theorem historyRealizesFan_duplicate_iff
    {c r m : Nat}
    (q : AM H c 1)
    (B P : MMap H)
    (E : OneLevelLetter H r)
    (e : RawSuccessorFan H q)
    (hrm : r < m)
    (hBtop : H.levelMap B.map (q.rowEndLevel H) = r)
    (hPtop : H.levelMap P.map (q.rowEndLevel H) = m)
    (hbelow :
      ∀ (x : InitialNode T c)
        (hx : LevelTree.lev x.1 = c),
          E.toMMap (B (q.representative H x.1)) ≤
            P (q.representative H x.1)) :
    HistoryRealizesFan H q P
        (duplicateHistoryLetter H r m hrm) e ↔
      HistoryRealizesFan H q B E e := by
  have endpointLevel :
      ∀ (Q : MMap H) (t : Nat),
        H.levelMap Q.map (q.rowEndLevel H) = t →
        ∀ (x : InitialNode T c),
          LevelTree.lev x.1 = c →
            LevelTree.lev (Q (q.representative H x.1)) = t := by
    intro Q t htop x hx
    calc
      LevelTree.lev (Q (q.representative H x.1)) =
          H.levelMap Q.map
            (LevelTree.lev (q.representative H x.1)) :=
        (H.levelMap_eq Q.map (a := q.representative H x.1)).symm
      _ = H.levelMap Q.map (q.rowEndLevel H) := by
        congr 1
        calc
          LevelTree.lev (q.representative H x.1) =
              H.levelMap (q.representative H).map
                (LevelTree.lev x.1) :=
            (H.levelMap_eq (q.representative H).map (a := x.1)).symm
          _ = H.levelMap (q.representative H).map c := by rw [hx]
          _ = q.rowEndLevel H := rfl
      _ = t := htop
  constructor
  · intro hdup x hx
    let z := B (q.representative H x.1)
    have hzlev : LevelTree.lev z = r :=
      endpointLevel B r hBtop x hx
    let actual := H.letterCode E z hzlev
    have hPlev :
        LevelTree.lev (P (q.representative H x.1)) = m :=
      endpointLevel P m hPtop x hx
    have hactualDup :=
      H.duplicate_rule r m hrm
        z (P (q.representative H x.1))
        actual.params actual.char (E.toMMap z)
        hzlev hPlev actual.succ_eq (hbelow x hx)
    have hdupX := hdup x hx
    change
      S.succ (P (q.representative H x.1))
        (e.code H x hx).params (e.code H x hx).char =
      some
        (H.duplicate r m hrm
          (P (q.representative H x.1))) at hdupX
    have hsame := S.s2 hdupX hactualDup
    have hp : (e.code H x hx).params = actual.params := hsame.2.1
    have hc : (e.code H x hx).char = actual.char := hsame.2.2
    rw [hp, hc]
    exact actual.succ_eq
  · intro he x hx
    have hBlev :
        LevelTree.lev (B (q.representative H x.1)) = r :=
      endpointLevel B r hBtop x hx
    have hPlev :
        LevelTree.lev (P (q.representative H x.1)) = m :=
      endpointLevel P m hPtop x hx
    have hdup :=
      H.duplicate_rule r m hrm
        (B (q.representative H x.1))
        (P (q.representative H x.1))
        (e.code H x hx).params (e.code H x hx).char
        (E.toMMap (B (q.representative H x.1)))
        hBlev hPlev (he x hx) (hbelow x hx)
    simpa [duplicateHistoryLetter] using hdup

/-- Hence M3 replay preserves the complete profile, not only the coordinates
which are realized. -/
theorem historyProfile_duplicate
    {c r m : Nat}
    (q : AM H c 1)
    (B P : MMap H)
    (E : OneLevelLetter H r)
    (hrm : r < m)
    (hBtop : H.levelMap B.map (q.rowEndLevel H) = r)
    (hPtop : H.levelMap P.map (q.rowEndLevel H) = m)
    (hbelow :
      ∀ (x : InitialNode T c)
        (hx : LevelTree.lev x.1 = c),
          E.toMMap (B (q.representative H x.1)) ≤
            P (q.representative H x.1)) :
    historyProfile H q P (duplicateHistoryLetter H r m hrm) =
      historyProfile H q B E := by
  classical
  by_cases h :
      ∃ e : RawSuccessorFan H q,
        HistoryRealizesFan H q B E e
  · rcases h with ⟨e, he⟩
    have he' :
        HistoryRealizesFan H q P
          (duplicateHistoryLetter H r m hrm) e :=
      (historyRealizesFan_duplicate_iff
        H q B P E e hrm hBtop hPtop hbelow).2 he
    rw [historyProfile_eq_some H q B E e he]
    rw [historyProfile_eq_some H q P
      (duplicateHistoryLetter H r m hrm) e he']
  · have h' :
      ¬ ∃ e : RawSuccessorFan H q,
          HistoryRealizesFan H q P
            (duplicateHistoryLetter H r m hrm) e := by
      intro hex
      rcases hex with ⟨e, he⟩
      exact h ⟨e,
        (historyRealizesFan_duplicate_iff
          H q B P E e hrm hBtop hPtop hbelow).1 he⟩
    unfold historyProfile
    rw [dif_neg h', dif_neg h]

end FatTree
end SMTree
end SuccessorTree

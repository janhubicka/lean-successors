import SuccessorTree.FatTree.A4ReviewTransport

/-!
# Algebraic linkage in the review's good-pair lemma

A persistent large-set witness need not equal the head of the simultaneous
line. It factors through that head. Transporting raw fans through the
factor, followed by associativity, is what transfers the line colours to
this particular witness.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v w z
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- Transport a raw successor fan across equality of its base row.  The
finite successor table itself is unchanged. -/
private noncomputable def reviewCastFan
    {c : Nat} {q r : AM H c 1} (h : q = r)
    (e : RawSuccessorFan H q) : RawSuccessorFan H r := by
  cases h
  exact e

@[simp] private theorem reviewCastFan_toFun
    {c : Nat} {q r : AM H c 1} (h : q = r)
    (e : RawSuccessorFan H q) (x : InitialNode T c) :
    ((reviewCastFan H h e).toFun x).1 = (e.toFun x).1 := by
  cases h
  rfl

/-- Compose exact traces, retaining the exact terminal level. -/
noncomputable def reviewExactComp {c d D : Nat}
    (q : AMExact H c d) (p : AMExact H d D) : AMExact H c D :=
  ⟨H.composeAcross q p.1, (review_composeAcross_end H q p.1).trans p.2⟩

/-- Cross-cut substitution is associative on finite one-moving maps. -/
theorem review_composeAcross_assoc {c d D : Nat}
    (q : AMExact H c d) (p : AMExact H d D) (h : AM H D 1) :
    H.composeAcross (reviewExactComp H q p) h =
      H.composeAcross q (H.composeAcross p h) := by
  apply review_AM_ext_top H
  intro x hx
  have hqx : LevelTree.lev (q.1.representative H x) = d :=
    (review_AM_level H q.1 hx).trans q.2
  calc
    (H.composeAcross (reviewExactComp H q p) h).representative H x =
        h.representative H ((H.composeAcross q p.1).representative H x) :=
      H.composeAcross_representative_agrees (reviewExactComp H q p) h x (Nat.le_of_eq hx)
    _ = h.representative H (p.1.representative H (q.1.representative H x)) := by
      rw [H.composeAcross_representative_agrees q p.1 x (Nat.le_of_eq hx)]
    _ = (H.composeAcross p h).representative H (q.1.representative H x) :=
      (H.composeAcross_representative_agrees p h (q.1.representative H x)
        (Nat.le_of_eq hqx)).symm
    _ = (H.composeAcross q (H.composeAcross p h)).representative H x :=
      (H.composeAcross_representative_agrees q (H.composeAcross p h) x (Nat.le_of_eq hx)).symm

/-- A pointwise raw-update witness can be assembled into the finite raw fan
used by the simultaneous line theorem. There is no admissibility assertion
about the resulting table. -/
theorem review_exists_fan_of_pointwise {c : Nat}
    (q : AM H c 1) (F : T → T) (theta : T → T)
    (hraw : ∀ x : T, LevelTree.lev x = c →
      ∃ t : T, q.representative H x ⋖ t ∧ theta x = F t) :
    ∃ e : RawSuccessorFan H q,
      ∀ (x : InitialNode T c), LevelTree.lev x.1 = c →
        theta x.1 = F (e.toFun x).1 := by
  classical
  have hct : c ≤ q.rowEndLevel H := H.levelMap_id_le (q.representative H).map c
  let table : InitialNode T c → InitialNode T (q.rowEndLevel H + 1) := fun x =>
    if hx : LevelTree.lev x.1 < c then
      ⟨x.1, x.2.trans (Nat.le_succ_of_le hct)⟩
    else
      let heq : LevelTree.lev x.1 = c := le_antisymm x.2 (Nat.le_of_not_gt hx)
      let t := Classical.choose (hraw x.1 heq)
      have ht : q.representative H x.1 ⋖ t := (Classical.choose_spec (hraw x.1 heq)).1
      ⟨t, Nat.le_of_eq ((LevelTree.covBy_level_eq ht).trans
        (congrArg (fun n => n + 1) (review_AM_level H q heq)))⟩
  let e : RawSuccessorFan H q := {
    toFun := table
    eq_id_below := by
      intro x hx
      simp only [table, dif_pos hx]
    top_covBy := by
      intro x hx
      have hn : ¬ LevelTree.lev x.1 < c := by omega
      dsimp only [table]
      simp only [dif_neg hn]
      exact (Classical.choose_spec (hraw x.1 hx)).1
  }
  refine ⟨e, ?_⟩
  intro x hx
  have hn : ¬ LevelTree.lev x.1 < c := by omega
  change theta x.1 = F (table x).1
  simp only [table, dif_neg hn]
  exact (Classical.choose_spec (hraw x.1 hx)).2

/-- Transfer one coordinate of a simultaneous line to a head which factors
through the chosen common head. This is the colour equality in the last
paragraph of `lem:trace-good-pair`. -/
theorem reviewFanLine_factor_colour
    {c d : Nat} {C : Type w} {κ : Type z}
    {U : FatTree H} {a : Nat} {trace : C → AM H c 1}
    {hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a}
    {chi : AM H c 1 → κ}
    (L : ReviewFanLine H U a trace hend chi)
    (q : AMExact H c d) (p : AMExact H d (U.cut a))
    (j : C) (hj : trace j = H.composeAcross q p.1)
    (e : RawSuccessorFan H q.1)
    (theta : AM H c 1) (htheta : theta.rowEndLevel H = U.cut L.headDepth)
    (hraw : ∀ (x : InitialNode T c), LevelTree.lev x.1 = c →
      theta.representative H x.1 =
        H.canonicalExtension ((H.composeAcross p L.head).representative H) d (e.toFun x).1) :
    chi (H.composeAcross (⟨theta, htheta⟩ : AMExact H c (U.cut L.headDepth)) L.tail) =
      chi (H.composeAcross q (H.composeAcross p L.head)) := by
  let f := reviewTransportFan H q p e
  have hfraw : ∀ (x : InitialNode T c), LevelTree.lev x.1 = c →
      theta.representative H x.1 =
        H.canonicalExtension (L.head.representative H) (U.cut a) (f.toFun x).1 := by
    intro x hx
    rw [hraw x hx, review_composeAcross_canonical H p L.head]
    rfl
  have hline :
      chi (H.composeAcross (⟨theta, htheta⟩ : AMExact H c (U.cut L.headDepth)) L.tail) =
        chi (H.composeAcross (reviewExactComp H q p) L.head) := by
    let f' : RawSuccessorFan H (trace j) :=
      reviewCastFan H hj.symm f
    have hfraw' : ∀ (x : InitialNode T c), LevelTree.lev x.1 = c →
        theta.representative H x.1 =
          H.canonicalExtension (L.head.representative H) (U.cut a) (f'.toFun x).1 := by
      intro x hx
      simpa only [f', reviewCastFan_toFun] using hfraw x hx
    have he := L.fan_colour j f' theta htheta hfraw'
    have hexact :
        (⟨trace j, hend j⟩ : AMExact H c (U.cut a)) =
          reviewExactComp H q p := by
      apply Subtype.ext
      exact hj
    have hcomp :
        H.composeAcross (⟨trace j, hend j⟩ : AMExact H c (U.cut a)) L.head =
          H.composeAcross (reviewExactComp H q p) L.head :=
      congrArg (fun r : AMExact H c (U.cut a) => H.composeAcross r L.head) hexact
    exact he.trans (congrArg chi hcomp)
  exact hline.trans (congrArg chi (review_composeAcross_assoc H q p L.head))

end SuccessorTree.SMTree.FatTree

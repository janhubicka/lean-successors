import SuccessorTree.FatTree.A4ReviewLine

/-!
# Transport across the persistent-depth factor in the review proof

The good-pair argument factors the chosen large-set witness as H p.  Its
raw successor tables must therefore be transported by p's canonical
extension.  The lemmas below use forward composition only: a raw fan is
never assumed to extend to an admissible M-map.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- Read the last image level from any point on the moving source level. -/
theorem review_AM_level {c : Nat} (q : AM H c 1) {x : T}
    (hx : LevelTree.lev x = c) :
    LevelTree.lev (q.representative H x) = q.rowEndLevel H := by
  calc
    LevelTree.lev (q.representative H x) =
        H.levelMap (q.representative H).map (LevelTree.lev x) :=
      (H.levelMap_eq (q.representative H).map (a := x)).symm
    _ = H.levelMap (q.representative H).map c := by rw [hx]
    _ = q.rowEndLevel H := rfl

/-- A cross-cut composite ends where its outer row ends. -/
theorem review_composeAcross_end {c d : Nat}
    (p : AMExact H c d) (h : AM H d 1) :
    (H.composeAcross p h).rowEndLevel H = h.rowEndLevel H := by
  obtain ⟨x, hx⟩ := H.level_nonempty c
  have hpx : LevelTree.lev (p.1.representative H x) = d :=
    (review_AM_level H p.1 hx).trans p.2
  calc
    (H.composeAcross p h).rowEndLevel H =
        LevelTree.lev ((H.composeAcross p h).representative H x) :=
      (review_AM_level H (H.composeAcross p h) hx).symm
    _ = LevelTree.lev (h.representative H (p.1.representative H x)) :=
      congrArg LevelTree.lev (H.composeAcross_representative_agrees p h x (Nat.le_of_eq hx))
    _ = h.rowEndLevel H := review_AM_level H h hpx

/-- Canonical extensions commute with cross-cut composition. The equality
holds on the whole tree, not just on the moving source level. -/
theorem review_composeAcross_canonical {c d : Nat}
    (p : AMExact H c d) (h : AM H d 1) :
    H.canonicalExtension ((H.composeAcross p h).representative H) c =
      MMap.comp H (H.canonicalExtension (h.representative H) d)
        (H.canonicalExtension (p.1.representative H) c) := by
  let P := H.canonicalExtension (p.1.representative H) c
  let B := H.canonicalExtension (h.representative H) d
  let G := MMap.comp H B P
  apply Eq.symm
  apply H.canonicalExtension_unique ((H.composeAcross p h).representative H) G c
  · intro x hx
    have hpx : LevelTree.lev (p.1.representative H x) ≤ d :=
      (p.1.level_le_topLevel H x hx).trans_eq p.2
    change B (P x) = (H.composeAcross p h).representative H x
    rw [show P x = p.1.representative H x from
      H.canonicalExtension_agrees (p.1.representative H) c x hx]
    exact (H.canonicalExtension_agrees (h.representative H) d
      (p.1.representative H x) hpx).trans
      (H.composeAcross_representative_agrees p h x hx).symm
  · intro ell hell
    have hbound : h.rowEndLevel H ≤ ell := by
      have hend := review_composeAcross_end H p h
      change (H.composeAcross p h).rowEndLevel H ≤ ell at hell
      rwa [hend] at hell
    have hlevel : H.levelMap G.map (c + (ell - h.rowEndLevel H)) = ell := by
      change H.levelMap (MMap.comp H B P).map _ = ell
      rw [H.levelMap_comp B P]
      change H.levelMap B.map
        (H.levelMap (H.canonicalExtension (p.1.representative H) c).map
          (c + (ell - h.rowEndLevel H))) = ell
      rw [H.canonicalExtension_level_tail]
      rw [show H.levelMap (p.1.representative H).map c = d from p.2]
      change H.levelMap (H.canonicalExtension (h.representative H) d).map
        (d + (ell - h.rowEndLevel H)) = ell
      rw [H.canonicalExtension_level_tail]
      change h.rowEndLevel H + (ell - h.rowEndLevel H) = ell
      omega
    rw [← H.range_levelMap G.map]
    exact ⟨c + (ell - h.rowEndLevel H), hlevel⟩

/-- Transport a raw fan at q by the canonical extension of p.  The result
is a raw fan at p q even when neither successor table is admissible. -/
noncomputable def reviewTransportFan {c d D : Nat}
    (q : AMExact H c d) (p : AMExact H d D)
    (e : RawSuccessorFan H q.1) :
    RawSuccessorFan H (H.composeAcross q p.1) := by
  let P := H.canonicalExtension (p.1.representative H) d
  have hcd : c ≤ d := (H.levelMap_id_le (q.1.representative H).map c).trans_eq q.2
  have hqend : q.1.rowEndLevel H = d := q.2
  have hpend : p.1.rowEndLevel H = D := p.2
  have hrend : (H.composeAcross q p.1).rowEndLevel H = D :=
    (review_composeAcross_end H q p.1).trans hpend
  have hPnext : H.levelMap P.map (d + 1) = D + 1 := by
    change H.levelMap (H.canonicalExtension (p.1.representative H) d).map (d + 1) = D + 1
    rw [H.canonicalExtension_level_tail]
    exact congrArg (fun k => k + 1) p.2
  have htop (x : InitialNode T c) (hx : LevelTree.lev x.1 = c) :
      LevelTree.lev (e.toFun x).1 = d + 1 := by
    have he := LevelTree.covBy_level_eq (e.top_covBy x hx)
    rw [review_AM_level H q.1 hx, hqend] at he
    exact he
  refine {
    toFun := fun x => ⟨P (e.toFun x).1, ?_⟩
    eq_id_below := ?_
    top_covBy := ?_
  }
  · calc
      LevelTree.lev (P (e.toFun x).1) = H.levelMap P.map (LevelTree.lev (e.toFun x).1) :=
        (H.levelMap_eq P.map (a := (e.toFun x).1)).symm
      _ ≤ H.levelMap P.map (d + 1) :=
        (H.levelMap_strictMono P.map).monotone (by simpa only [hqend] using (e.toFun x).2)
      _ = D + 1 := hPnext
      _ = (H.composeAcross q p.1).rowEndLevel H + 1 := by rw [hrend]
  · intro x hx
    change P (e.toFun x).1 = x.1
    rw [e.eq_id_below x hx]
    exact (H.canonicalExtension_agrees (p.1.representative H) d x.1
      (Nat.le_of_lt (hx.trans_le hcd))).trans
      (p.1.representative_fixesBelow H x.1 (hx.trans_le hcd))
  · intro x hx
    have hqx : LevelTree.lev (q.1.representative H x.1) = d :=
      (review_AM_level H q.1 hx).trans hqend
    have hbase : (H.composeAcross q p.1).representative H x.1 =
        P (q.1.representative H x.1) :=
      (H.composeAcross_representative_agrees q p.1 x.1 (Nat.le_of_eq hx)).trans
        (H.canonicalExtension_agrees (p.1.representative H) d
          (q.1.representative H x.1) (Nat.le_of_eq hqx)).symm
    apply LevelTree.covBy_of_le_level_succ
    · rw [hbase]
      exact P.map.map_le_of_le (e.top_covBy x hx).le
    · change LevelTree.lev (P (e.toFun x).1) =
        LevelTree.lev ((H.composeAcross q p.1).representative H x.1) + 1
      rw [← H.levelMap_eq P.map (a := (e.toFun x).1), htop x hx, hPnext,
        review_AM_level H (H.composeAcross q p.1) hx, hrend]

@[simp] theorem reviewTransportFan_apply {c d D : Nat}
    (q : AMExact H c d) (p : AMExact H d D)
    (e : RawSuccessorFan H q.1) (x : InitialNode T c) :
    ((reviewTransportFan H q p e).toFun x).1 =
      H.canonicalExtension (p.1.representative H) d (e.toFun x).1 := rfl

end SuccessorTree.SMTree.FatTree

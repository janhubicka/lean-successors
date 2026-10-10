import SuccessorTree.V10.LocalAgeForbiddenTest
import SuccessorTree.V10.ExtractedSuccessorS2
import Mathlib.Tactic

/-!
# The prescribed common-socle column in Lemma 6.51

Condition (B2) of the manuscript means that compatible outputs of the
prescribed crossing map agree on the entire newly completed ORDINARY
socle, not on their distinguished upper type vertices.

Here we encode that finite L+ agreement literally, extract the inserted
ordinary vertex's complete lower L-column, and prove:

* the extracted column is independent of a compatible output choice;
* the E free-cut of that vertex is also unique from ordinary-socle data;
* the actual no-new-tuples condition implies every incident lower L-edge
  is below the extracted E-cut (the hBelow input of insertPartial);
* a gated upper-column construction automatically gives the hAbove
  condition of insertPartial.

This does not assume a prescribed Kpt shape map. It isolates and discharges
two of its genuinely finite construction obligations. The matching-socle
age test and the global upper-type selection still need to be assembled.
-/

namespace SuccessorTree.V10

/-- Agreement on the full induced L+ structure on the first ell+1 ORDINARY
vertices. The distinguished type vertex is deliberately excluded, as in
the manuscript's compatibility condition. -/
def SameOrdinarySocle
    {ell db du dd : Nat}
    (Q R : PartialTypeWithE (ell + 1) db du dd) : Prop :=
  (∀ i j : Fin (ell + 1), ∀ t : Fin db,
    Q.lReduct.binary (some i) (some j) t =
      R.lReduct.binary (some i) (some j) t) ∧
  (∀ i : Fin (ell + 1), ∀ t : Fin du,
    Q.lReduct.unary (some i) t = R.lReduct.unary (some i) t) ∧
  (∀ i : Fin (ell + 1), ∀ t : Fin dd,
    Q.lReduct.diagonal (some i) t = R.lReduct.diagonal (some i) t) ∧
  (∀ i j : Fin (ell + 1),
    Q.eRelation (some i) (some j) = R.eRelation (some i) (some j))

theorem sameOrdinarySocle_refl
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd) :
    SameOrdinarySocle Q Q := by
  exact ⟨by intros; rfl, by intros; rfl,
    by intros; rfl, by intros; rfl⟩

theorem sameOrdinarySocle_symm
    {ell db du dd : Nat}
    {Q R : PartialTypeWithE (ell + 1) db du dd}
    (h : SameOrdinarySocle Q R) :
    SameOrdinarySocle R Q := by
  exact ⟨fun i j t => (h.1 i j t).symm,
    fun i t => (h.2.1 i t).symm,
    fun i t => (h.2.2.1 i t).symm,
    fun i j => (h.2.2.2 i j).symm⟩

/-- Full L-column of the new ordinary vertex ell over its earlier socle.
No upper type vertex appears in this record. -/
structure LowerInsertedColumn (ell db du dd : Nat) where
  loop : Fin db → Bool
  unary : Fin du → Bool
  diagonal : Fin dd → Bool
  incoming : Fin ell → Fin db → Bool
  outgoing : Fin ell → Fin db → Bool

/-- All positive AND negative directed L facts of the inserted ordinary
vertex, as read from an actual one-level extension Q. -/
def lowerInsertedColumn
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd) :
    LowerInsertedColumn ell db du dd where
  loop := Q.lReduct.binary (some (Fin.last ell)) (some (Fin.last ell))
  unary := Q.lReduct.unary (some (Fin.last ell))
  diagonal := Q.lReduct.diagonal (some (Fin.last ell))
  incoming := fun i t =>
    Q.lReduct.binary (some i.castSucc) (some (Fin.last ell)) t
  outgoing := fun i t =>
    Q.lReduct.binary (some (Fin.last ell)) (some i.castSucc) t

/-- Precisely the needed consequence of B2: every possible compatible
prescribed crossing gives the SAME lower column, including all absent
tuples, loops, unary and diagonal data. -/
theorem lowerInsertedColumn_eq_of_sameSocle
    {ell db du dd : Nat}
    {Q R : PartialTypeWithE (ell + 1) db du dd}
    (h : SameOrdinarySocle Q R) :
    lowerInsertedColumn Q = lowerInsertedColumn R := by
  apply LowerInsertedColumn.ext
  · funext t
    exact h.1 (Fin.last ell) (Fin.last ell) t
  · funext t
    exact h.2.1 (Fin.last ell) t
  · funext t
    exact h.2.2.1 (Fin.last ell) t
  · funext i t
    exact h.1 i.castSucc (Fin.last ell) t
  · funext i t
    exact h.1 (Fin.last ell) i.castSucc t

/-- Same ordinary socle plus genuine valid E-columns identifies the UNIQUE
first missing E-coordinate of the new ordinary vertex. No numerical cut
equality is postulated. -/
theorem lowerInsertedCut_eq_of_sameSocle
    {ell db du dd : Nat}
    {Q R : PartialTypeWithE (ell + 1) db du dd}
    (h : SameOrdinarySocle Q R)
    (d e : Nat)
    (hd : d ≤ ell) (he : e ≤ ell)
    (hQ : ValidNewOrdinaryColumn Q d)
    (hR : ValidNewOrdinaryColumn R e) :
    d = e := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · let i : Fin ell := ⟨d, by omega⟩
    have hEq : decide (d < d) = decide (d < e) := by
      calc
        decide (d < d) = Q.eRelation (some i.castSucc) (some (Fin.last ell)) :=
          (hQ.oldToNewE i).symm
        _ = R.eRelation (some i.castSucc) (some (Fin.last ell)) :=
          h.2.2.2 i.castSucc (Fin.last ell)
        _ = decide (d < e) := hR.oldToNewE i
    simp [hlt] at hEq
  · let i : Fin ell := ⟨e, by omega⟩
    have hEq : decide (e < d) = decide (e < e) := by
      calc
        decide (e < d) = Q.eRelation (some i.castSucc) (some (Fin.last ell)) :=
          (hQ.oldToNewE i).symm
        _ = R.eRelation (some i.castSucc) (some (Fin.last ell)) :=
          h.2.2.2 i.castSucc (Fin.last ell)
        _ = decide (e < e) := hR.oldToNewE i
    simp [hgt] at hEq

/-- Combine a prescribed lower column and upper type-to-inserted relations
with the mandatory E-gating: an upper relation is suppressed whenever its
old vertex had free cut below ell. -/
noncomputable def gatedInsertedLData
    {db du dd ell : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (P : LowerInsertedColumn ell db du dd)
    (upperIncoming upperOutgoing : Nat → Fin db → Bool) :
    InsertedLData db du dd where
  loop := P.loop
  unary := P.unary
  diagonal := P.diagonal
  incoming := fun x t =>
    if hx : x < ell then P.incoming ⟨x, hx⟩ t
    else if ell ≤ A.freeLevel x then upperIncoming x t else false
  outgoing := fun x t =>
    if hx : x < ell then P.outgoing ⟨x, hx⟩ t
    else if ell ≤ A.freeLevel x then upperOutgoing x t else false

/-- An actual canonical new-ordinary-column can only link to a lower
vertex strictly BELOW its free cut, precisely the E3 obligation hBelow
of the real finite partial-structure insertion constructor. -/
theorem lowerInsertedColumn_link_lt_cut
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (d : Nat)
    (hValid : ValidNewOrdinaryColumn Q d)
    (x : Fin ell)
    (hLink : ∃ t : Fin db,
      (lowerInsertedColumn Q).incoming x t = true ∨
      (lowerInsertedColumn Q).outgoing x t = true) :
    x.val < d := by
  by_contra hnot
  have hge : d ≤ x.val := by omega
  obtain ⟨t, hbit⟩ := hLink
  obtain ⟨hzIn, hzOut⟩ := hValid.noNewBinaryBeyondCut x hge t
  rcases hbit with hb | hb
  · exact Bool.false_ne_true (hzIn.symm.trans hb)
  · exact Bool.false_ne_true (hzOut.symm.trans hb)

/-- The prescribed lower crossing automatically satisfies the first
linkage condition; no separate assumption on its L bits is necessary. -/
theorem gatedInsertedLData_below
    {db du dd ell : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (d : Nat) (hValid : ValidNewOrdinaryColumn Q d)
    (upperIncoming upperOutgoing : Nat → Fin db → Bool) :
    ∀ x, x < ell →
      (∃ t : Fin db,
        (gatedInsertedLData A (lowerInsertedColumn Q)
          upperIncoming upperOutgoing).incoming x t = true ∨
        (gatedInsertedLData A (lowerInsertedColumn Q)
          upperIncoming upperOutgoing).outgoing x t = true) →
      x < d := by
  intro x hx h
  have hh : ∃ t : Fin db,
      (lowerInsertedColumn Q).incoming ⟨x,hx⟩ t = true ∨
      (lowerInsertedColumn Q).outgoing ⟨x,hx⟩ t = true := by
    simpa [gatedInsertedLData, hx] using h
  exact lowerInsertedColumn_link_lt_cut Q d hValid ⟨x,hx⟩ hh

/-- Gating upper relations by the ORIGINAL vertex's canonical free cut
automatically verifies the second finite insertion linkage obligation. -/
theorem gatedInsertedLData_above
    {db du dd ell : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (P : LowerInsertedColumn ell db du dd)
    (upperIncoming upperOutgoing : Nat → Fin db → Bool) :
    ∀ y, ell ≤ y → y < A.size →
      (∃ t : Fin db,
        (gatedInsertedLData A P upperIncoming upperOutgoing).outgoing y t = true ∨
        (gatedInsertedLData A P upperIncoming upperOutgoing).incoming y t = true) →
      ell ≤ A.freeLevel y := by
  intro y hy hySize h
  by_contra hnot
  have hneg : ¬ ell ≤ A.freeLevel y := by omega
  have hnotlt : ¬ y < ell := Nat.not_lt.mpr hy
  have hfalse : ∀ t : Fin db,
      (gatedInsertedLData A P upperIncoming upperOutgoing).outgoing y t = false ∧
      (gatedInsertedLData A P upperIncoming upperOutgoing).incoming y t = false := by
    intro t
    simp [gatedInsertedLData, hnotlt, hneg]
  obtain ⟨t, hb⟩ := h
  obtain ⟨h1,h2⟩ := hfalse t
  rcases hb with hb | hb
  · exact Bool.false_ne_true (h1.symm.trans hb)
  · exact Bool.false_ne_true (h2.symm.trans hb)

end SuccessorTree.V10

import SuccessorTree.FatTree.A4ReviewAlgebra

/-!
# Reattaching a common tail after the persistent witness

The good-pair proof selects a head different from the original fan-line
head, but with the same terminal cut. A3 and the existing splice operation
suffice to transfer the entire common tail. No first-block factorisation
or equality of the two heads is needed.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- A tail geometrically legal after the full prefix at a cut is legal
after any finite geometric stem ending at that cut. -/
theorem review_occurs_after_matching_stem
    (x : FiniteFatTree H) (U : FatTree H) (a : Nat)
    (hx : StemAt H x U a)
    (k : AM H (U.cut a) 1)
    (hk : OneBlockOccurs H (U.initialSegment H a) U k) :
    OneBlockOccurs H x U
      (FiniteFatTree.castTraceRow H (terminalCut_eq_of_stemAt H hx).symm k) := by
  rcases hk with ⟨b, hkb⟩
  obtain ⟨B, hBU, hBstem⟩ := a3_one_nonempty H hkb
    ⟨reduces_refl H U, initialSegment_extendsStem H U b⟩
  have hBcone : InDepthCone H a U B :=
    ⟨hBU, extendsStem_of_appendRow H hBstem⟩
  have hxB : StemAt H x B a := stemAt_of_depthCone H hx hBcone
  let hc := terminalCut_eq_of_stemAt H hxB
  let C := splice H x B a hc
  have hCstem : ExtendsStem H x C := splice_extendsStem H x B a hc
  have hCB : Reduces H C B := splice_reduces H hxB
  have hCU : Reduces H C U := reduces_trans H hCB hBU
  have hrowC : HEq (C.row x.height) (B.row a) := by
    have h := splice_row_ge H x B a hc (i := x.height) le_rfl
    simpa only [Nat.sub_self, Nat.add_zero] using h
  have hrowB : HEq (B.row a) k := by
    have h := (hBstem.2 (Fin.last a)).trans
      (FiniteFatTree.appendRow_row_last H (U.initialSegment H a) k)
    exact h
  let next := ambientNextRow H x C hCstem
  have hnext : HEq next (C.row x.height) :=
    castRow_heq H (terminalCut_eq_of_extendsStem H hCstem) (C.row x.height)
  have hcast : HEq
      (FiniteFatTree.castTraceRow H (terminalCut_eq_of_stemAt H hx).symm k) k :=
    FiniteFatTree.castTraceRow_heq H (terminalCut_eq_of_stemAt H hx).symm k
  have heq : next =
      FiniteFatTree.castTraceRow H (terminalCut_eq_of_stemAt H hx).symm k :=
    eq_of_heq (hnext.trans (hrowC.trans (hrowB.trans hcast.symm)))
  rw [← heq]
  exact oneBlockOccurs_of_reduces H (ambientNextRow_occurs H x C hCstem) hCU

/-- A geometric appended row may be made the literal next row while
preserving the entire old ambient prefix. -/
theorem review_realize_head
    (U : FatTree H) (a b : Nat) (h : AM H (U.cut a) 1)
    (hh : StemAt H (FiniteFatTree.appendRow H (U.initialSegment H a) h) U b) :
    ∃ V : FatTree H, InDepthCone H a U V ∧
      ExtendsStem H (FiniteFatTree.appendRow H (U.initialSegment H a) h) V := by
  obtain ⟨V, hVU, hstem⟩ := a3_one_nonempty H hh
    ⟨reduces_refl H U, initialSegment_extendsStem H U b⟩
  exact ⟨V, ⟨hVU, extendsStem_of_appendRow H hstem⟩, hstem⟩

/-- Finite traces are unaffected by replacing an ambient tree beyond the
entire prefix in which they are recorded. -/
theorem review_trace_prefix_transport
    (U V : FatTree H) (a n : Nat) (hna : n ≤ a)
    (heq : V.initialSegment H a = U.initialSegment H a)
    (q : FiniteFatTree.ExactTrace H (V.initialSegment H a) n hna) :
    ∃ p : FiniteFatTree.ExactTrace H (U.initialSegment H a) n hna,
      HEq q.1 p.1 := by
  generalize hzV : V.initialSegment H a = y at heq q
  generalize hzU : U.initialSegment H a = z at heq ⊢
  cases heq
  exact ⟨q, HEq.rfl⟩

end SuccessorTree.SMTree.FatTree

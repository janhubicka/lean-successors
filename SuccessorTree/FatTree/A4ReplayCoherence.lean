import SuccessorTree.FatTree.A4OccurrenceStability

/-!
# Actual successor-code coherence for fat-tree replay

Equality of two bottom profile coordinates does not identify their successor
codes. These lemmas instead track the actual recorded edge and its ancestry.
They are the pointwise input to correctness of the common Hales--Jewett tail.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v w
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- Repeating an already repeated edge gives the same successor as repeating
the original edge directly. Only M3 and uniqueness of the successor are used. -/
theorem duplicate_replay_from_repeated_edge
    {r s t : Nat} (hrs : r < s) (hst : s < t)
    {a b z x : T} (ha : LevelTree.lev a = r)
    (hb : LevelTree.lev b = s) (hx : LevelTree.lev x = t)
    {params : List T} {ch : Label}
    (hedge : S.succ a params ch = some z) (hzb : z ≤ b)
    (hnext : H.duplicate r s hrs b ≤ x) :
    H.duplicate s t hst x = H.duplicate r t (hrs.trans hst) x := by
  have hfirst := H.duplicate_rule r s hrs a b params ch z ha hb hedge hzb
  have hsecond := H.duplicate_rule s t hst b x params ch
    (H.duplicate r s hrs b) hb hx hfirst hnext
  have hbx : b ≤ x :=
    (S.covBy_of_succ_eq_some hfirst).le.trans hnext
  have hdirect := H.duplicate_rule r t (hrs.trans hst)
    a x params ch z ha hx hedge (hzb.trans hbx)
  exact Option.some.inj (hsecond.symm.trans hdirect)

namespace ProfileCollector

variable {c : Nat} {C : Type w} [Fintype C]
variable {U : FatTree H} {a : Nat} {trace : C → AM H c 1}
variable (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
variable {K L : ProfileCollector H U a trace}

/-- Every reachable history is pointwise above its starting history on the
fixed source level. This does not require global saturation. -/
theorem reachable_state_mono
    (hKL : ReachableFrom H U a trace hend K L)
    {x : T} (hx : LevelTree.lev x = U.cut a) :
    K.state x ≤ L.state x := by
  induction hKL with
  | refl => exact le_rfl
  | @step P hKP E ih =>
      exact ih.trans (TraceHistoryState.le_step H U a P.index P.state E hx)

/-- The endpoint of an original witnessed occurrence stays below every later
history point. No inference from equality of bottom profiles is involved. -/
theorem original_occurrence_endpoint_below
    (hKL : ReachableFrom H U a trace hend K L)
    (beta : FanProfile H C trace) (hbeta : beta ∈ K.seen)
    (j : C) (x : InitialNode T c) (hx : LevelTree.lev x.1 = c) :
    (K.occurrence beta hbeta).letter.toMMap
        ((K.occurrence beta hbeta).base ((trace j).representative H x.1)) ≤
      L.state ((trace j).representative H x.1) := by
  have hq : LevelTree.lev ((trace j).representative H x.1) = U.cut a := by
    calc
      LevelTree.lev ((trace j).representative H x.1) =
          H.levelMap ((trace j).representative H).map (LevelTree.lev x.1) :=
        (H.levelMap_eq ((trace j).representative H).map (a := x.1)).symm
      _ = (trace j).rowEndLevel H := by rw [hx]; rfl
      _ = U.cut a := hend j
  exact ((K.occurrence beta hbeta).endpoint_below j x hx).trans
    (reachable_state_mono H hend hKL hq)

end ProfileCollector
end SuccessorTree.SMTree.FatTree

import SuccessorTree.Envelope
import Mathlib.Tactic

/-!
# One-level pullback for envelopes

This is the local inverse lemma needed in the noninteresting step of the
envelope algorithm. It isolates precisely the use of manuscript condition (E1).
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Manuscript condition (E1) for one shape map. -/
def PullbackDefined (S : STree T Label) (F : ShapeMap S) : Prop :=
  ∀ ⦃a : T⦄ ⦃p : List T⦄ ⦃c : Label⦄,
    S.Defined (F a) (p.map F) c → S.Defined a p c

/-- Pull back a finite list pointwise whenever all its entries lie in the range. -/
theorem exists_list_preimage
    (F : T → T) {p : List T}
    (h : ∀ ⦃x : T⦄, x ∈ p → x ∈ Set.range F) :
    ∃ q : List T, q.map F = p := by
  induction p with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
      obtain ⟨y, hy⟩ := h (x := x) (by simp)
      have htail : ∀ ⦃z : T⦄, z ∈ xs → z ∈ Set.range F := by
        intro z hz
        exact h (x := z) (by simp [hz])
      obtain ⟨q, hq⟩ := ih htail
      refine ⟨y :: q, ?_⟩
      simp [hy, hq]

/-- Above the skipped level, a successor step whose base and parameters lie
in the range is itself in the range, provided (E1) holds. -/
theorem successor_mem_range_of_pullback
    (H : SMTree S) (F : ShapeMap S) (m : Nat)
    (hskip : F.SkipsOnly m) (hE : PullbackDefined S F)
    {a b : T} {p : List T} {c : Label}
    (hstep : S.succ a p c = some b)
    (ha : a ∈ Set.range F)
    (hp : ∀ ⦃x : T⦄, x ∈ p → x ∈ Set.range F)
    (hm : m < LevelTree.lev a) :
    b ∈ Set.range F := by
  rcases ha with ⟨a0, rfl⟩
  obtain ⟨q, hq⟩ := exists_list_preimage F hp
  have htarget : S.succ (F a0) (q.map F) c = some b := by
    simpa [hq] using hstep
  obtain ⟨b0, hsource⟩ := hE ⟨b, htarget⟩
  have hma0 : m ≤ LevelTree.lev a0 := by
    by_contra hnot
    have ha0m : LevelTree.lev a0 < m := Nat.lt_of_not_ge hnot
    have hlev := H.level_eq_of_lt_skipped F m hskip ha0m
    rw [hlev] at hm
    omega
  have hmb0 : m < LevelTree.lev b0 := by
    have hcov := S.covBy_of_succ_eq_some hsource
    rw [LevelTree.covBy_level_eq hcov]
    omega
  have hexact := H.succ_eq_above_skip F m hskip hsource hmb0
  have hs : (some (F b0) : Option T) = some b :=
    hexact.symm.trans htarget
  exact ⟨b0, Option.some.inj hs⟩

/-- The local inverse lemma used in a noninteresting step of the envelope
algorithm. The crossing equation supplies level `m+1`; E1 then recursively
pulls back every later successor step. -/
theorem mem_range_of_oneLevel
    (H : SMTree S) (F : ShapeMap S) (m : Nat)
    (hskip : F.SkipsOnly m) (hE : PullbackDefined S F)
    (Z : Set T)
    (hparam : ParameterClosedOver S Z {j | m < j})
    (hno : ∀ ⦃z : T⦄, z ∈ Z → LevelTree.lev z ≠ m)
    (hcross :
      ∀ ⦃z : T⦄, z ∈ Z → ∀ (hmz : m < LevelTree.lev z),
        F (LevelTree.ancestor z m (Nat.le_of_lt hmz)) =
          LevelTree.ancestor z (m + 1) (Nat.succ_le_iff.mpr hmz))
    {x z : T} (hz : z ∈ Z) (hxz : x ≤ z)
    (hxne : LevelTree.lev x ≠ m) :
    x ∈ Set.range F := by
  induction hn : LevelTree.lev x using Nat.strong_induction_on generalizing x z with
  | h n ih =>
      by_cases hbelow : n < m
      · refine ⟨x, ?_⟩
        exact H.eq_id_below_skip F m hskip (by simpa [hn] using hbelow)
      have hmn : m ≤ n := Nat.le_of_not_gt hbelow
      have hmstrict : m < n := lt_of_le_of_ne hmn (by
        intro hnm
        exact hxne (hn.trans hnm.symm))
      by_cases hfirst : n = m + 1
      · have hmz : m < LevelTree.lev z := by
          have hnz : n ≤ LevelTree.lev z := by
            simpa [hn] using (LevelTree.level_le_of_le hxz)
          omega
        have hxanc :
            x = LevelTree.ancestor z (m + 1) (Nat.succ_le_iff.mpr hmz) := by
          apply LevelTree.eq_ancestor_of_le hxz
          · exact hn.trans hfirst
        refine ⟨LevelTree.ancestor z m (Nat.le_of_lt hmz), ?_⟩
        rw [hcross hz hmz, ← hxanc]
      · have hm1n : m + 1 < n := by omega
        let k : Nat := n - 1
        have hk : k + 1 = n := by
          dsimp [k]
          omega
        have hkx : k ≤ LevelTree.lev x := by
          rw [hn]
          omega
        let a := LevelTree.ancestor x k hkx
        have hax : a ≤ x := LevelTree.ancestor_le x k hkx
        have halev : LevelTree.lev a = k := LevelTree.level_ancestor x k hkx
        have hcov : a ⋖ x := by
          apply LevelTree.covBy_of_le_level_succ hax
          rw [halev, hn]
          omega
        obtain ⟨p, c, hstep⟩ := S.s3 hcov
        have hma : m < LevelTree.lev a := by
          rw [halev]
          dsimp [k]
          omega
        have harange : a ∈ Set.range F := by
          apply ih (LevelTree.lev a)
          · rw [halev]
            omega
          · exact hz
          · exact hax.trans hxz
          · exact Nat.ne_of_gt hma
          · exact rfl
        have hpZ : ∀ ⦃y : T⦄, y ∈ p → y ∈ Z := by
          intro y hy
          have hnz : n ≤ LevelTree.lev z := by
            have hle := LevelTree.level_le_of_le hxz
            simpa [hn] using hle
          have hkz : k ≤ LevelTree.lev z := by omega
          have hk1z : k + 1 ≤ LevelTree.lev z := by
            rw [hk]
            exact hnz
          have haAnc : a = LevelTree.ancestor z k hkz := by
            apply LevelTree.eq_ancestor_of_le (hax.trans hxz)
            · exact halev
          have hxAnc : x = LevelTree.ancestor z (k + 1) hk1z := by
            apply LevelTree.eq_ancestor_of_le hxz
            · exact hn.trans hk.symm
          have htarget :
              S.succ (LevelTree.ancestor z k hkz) p c =
                some (LevelTree.ancestor z (k + 1) hk1z) := by
            simpa [← haAnc, ← hxAnc] using hstep
          have hmk : m < k := by
            dsimp [k]
            omega
          have hkzlt : k < LevelTree.lev z := by omega
          exact hparam hz hmk hkzlt htarget hy
        have hpRange : ∀ ⦃y : T⦄, y ∈ p → y ∈ Set.range F := by
          intro y hy
          have hyZ := hpZ hy
          have hylevlt : LevelTree.lev y < LevelTree.lev a :=
            S.parameter_level_lt hstep hy
          apply ih (LevelTree.lev y)
          · exact hylevlt.trans (by rw [halev]; dsimp [k]; omega)
          · exact hyZ
          · exact le_rfl
          · exact hno hyZ
          · exact rfl
        exact successor_mem_range_of_pullback H F m hskip hE
          hstep harange hpRange hma

/-- Hence every member of `Z` has a preimage. -/
theorem subset_range_of_oneLevel
    (H : SMTree S) (F : ShapeMap S) (m : Nat)
    (hskip : F.SkipsOnly m) (hE : PullbackDefined S F)
    (Z : Set T)
    (hparam : ParameterClosedOver S Z {j | m < j})
    (hno : ∀ ⦃z : T⦄, z ∈ Z → LevelTree.lev z ≠ m)
    (hcross :
      ∀ ⦃z : T⦄, z ∈ Z → ∀ (hmz : m < LevelTree.lev z),
        F (LevelTree.ancestor z m (Nat.le_of_lt hmz)) =
          LevelTree.ancestor z (m + 1) (Nat.succ_le_iff.mpr hmz)) :
    Z ⊆ Set.range F := by
  intro z hz
  exact mem_range_of_oneLevel H F m hskip hE Z hparam hno hcross hz le_rfl (hno hz)

end Envelope
end SMTree
end SuccessorTree

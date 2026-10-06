import SuccessorTree.Monoid
import Mathlib.Tactic

/-!
# Envelopes: the one-level pullback lemma

This file starts the formalization of the envelope section of the manuscript.
The additional hypothesis E1 is kept separate from the axioms of an
`(S,M)`-tree.  The main result here is the punctured-prefix pullback lemma
used by the decreasing envelope construction.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Manuscript axiom E1.  A one-level skip map reflects the domain of the
successor operation. -/
def EnvelopeE1 (H : SMTree S) : Prop :=
  ∀ (F : MMap H) (i : Nat), F.map.SkipsOnly i →
    ∀ (a : T) (p : List T) (c : Label),
      S.Defined (F a) (p.map F) c → S.Defined a p c

/-- Parameter closure over all successor levels strictly above `i`, in the
edgewise form used in the punctured-prefix proof. -/
def ParameterClosedAbove
    (S : STree T Label) (Z : Set T) (i : Nat) : Prop :=
  ∀ ⦃z a b : T⦄ ⦃p : List T⦄ ⦃c : Label⦄,
    z ∈ Z → a ⋖ b → b ≤ z → i < LevelTree.lev a →
      S.succ a p c = some b →
        ∀ x ∈ p, x ∈ Z

/-- The set `Z` does not meet level `i`. -/
def AvoidsLevel (Z : Set T) (i : Nat) : Prop :=
  ∀ ⦃z : T⦄, z ∈ Z → LevelTree.lev z ≠ i

/-- The prescribed edge across the omitted level: each branch of `Z` above
`i` is pulled from its level-`i` predecessor to its level-`i+1`
predecessor. -/
def PrescribesSkippedEdges
    (F : MMap H) (Z : Set T) (i : Nat) : Prop :=
  ∀ ⦃z : T⦄, z ∈ Z → (hi : i < LevelTree.lev z) →
    F (LevelTree.ancestor z i (Nat.le_of_lt hi)) =
      LevelTree.ancestor z (i + 1) (Nat.succ_le_iff.mpr hi)

/-- A predecessor at the node's own level is the node itself. -/
private theorem ancestor_self
    (x : T) :
    LevelTree.ancestor x (LevelTree.lev x) le_rfl = x := by
  exact (LevelTree.eq_ancestor_of_le
    (a := x) (b := x) le_rfl rfl le_rfl).symm

/-- **Punctured-prefix pullback.**
If a one-level skip map satisfies E1 and realizes the prescribed crossing at
the omitted level, then every predecessor of a member of `Z`, except at the
omitted target level itself, lies in its range.

The finiteness of `Z` assumed in the manuscript is not used by this local
lemma; it enters later when the envelope algorithm closes a finite set. -/
theorem puncturedPrefix_pullback
    (H : SMTree S) (hE1 : EnvelopeE1 H)
    (F : MMap H) (i : Nat) (hskip : F.map.SkipsOnly i)
    (Z : Set T)
    (havoid : AvoidsLevel Z i)
    (hclosed : ParameterClosedAbove S Z i)
    (hcross : PrescribesSkippedEdges F Z i) :
    ∀ ⦃z : T⦄, z ∈ Z →
      ∀ (j : Nat) (hj : j ≤ LevelTree.lev z), j ≠ i →
        ∃ y : T, F y = LevelTree.ancestor z j hj := by
  classical
  have main :
      ∀ j : Nat, ∀ ⦃z : T⦄, z ∈ Z →
        (hj : j ≤ LevelTree.lev z) → j ≠ i →
          ∃ y : T, F y = LevelTree.ancestor z j hj := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        intro z hz hj hji
        by_cases hbelow : j < i
        · let w := LevelTree.ancestor z j hj
          have hwlev : LevelTree.lev w = j :=
            LevelTree.level_ancestor z j hj
          refine ⟨w, ?_⟩
          exact H.eq_id_below_skip F.map i hskip (by
            simpa [w, hwlev] using hbelow)
        · by_cases hnext : j = i + 1
          · subst j
            have hi : i < LevelTree.lev z := by omega
            let y := LevelTree.ancestor z i (Nat.le_of_lt hi)
            refine ⟨y, ?_⟩
            simpa [y] using hcross hz hi
          · have habove : i + 1 < j := by omega
            let q : Nat := j - 1
            have hqj : q < j := by
              dsimp [q]
              omega
            have hqi : i < q := by
              dsimp [q]
              omega
            have hqne : q ≠ i := Nat.ne_of_gt hqi
            have hqle : q ≤ LevelTree.lev z := by
              dsimp [q]
              omega
            let a0 := LevelTree.ancestor z q hqle
            let b0 := LevelTree.ancestor z j hj
            have ha0lev : LevelTree.lev a0 = q :=
              LevelTree.level_ancestor z q hqle
            have hb0lev : LevelTree.lev b0 = j :=
              LevelTree.level_ancestor z j hj
            have ha0z : a0 ≤ z :=
              LevelTree.ancestor_le z q hqle
            have hb0z : b0 ≤ z :=
              LevelTree.ancestor_le z j hj
            have ha0b0 : a0 ≤ b0 := by
              rcases LevelTree.comparable_below ha0z hb0z with hle | hle
              · exact hle
              · have hlevels := LevelTree.level_le_of_le hle
                rw [ha0lev, hb0lev] at hlevels
                omega
            have hcov : a0 ⋖ b0 := by
              apply LevelTree.covBy_of_le_level_succ ha0b0
              rw [ha0lev, hb0lev]
              dsimp [q]
              omega
            obtain ⟨p, c, hsucc⟩ := S.s3 hcov

            obtain ⟨a, ha⟩ :=
              ih q hqj hz hqle hqne
            have ha' : F a = a0 := by
              simpa [a0] using ha

            have hpre :
                ∀ x ∈ p, ∃ y : T, F y = x := by
              intro x hx
              have hxZ : x ∈ Z :=
                hclosed hz hcov hb0z (by
                  simpa [ha0lev] using hqi) hsucc x hx
              have hxltq : LevelTree.lev x < q := by
                have hlt := S.parameter_level_lt hsucc hx
                simpa [ha0lev] using hlt
              have hxltj : LevelTree.lev x < j :=
                hxltq.trans hqj
              have hxi : LevelTree.lev x ≠ i :=
                havoid hxZ
              obtain ⟨y, hy⟩ :=
                ih (LevelTree.lev x) hxltj hxZ le_rfl hxi
              refine ⟨y, ?_⟩
              exact hy.trans (ancestor_self x)

            have pullList :
                ∀ l : List T, (∀ x ∈ l, x ∈ p) →
                  ∃ q' : List T, q'.map F = l := by
              intro l hl
              induction l with
              | nil =>
                  exact ⟨[], rfl⟩
              | cons x xs ihl =>
                  obtain ⟨y, hy⟩ := hpre x (hl x (by simp))
                  have hxs : ∀ z ∈ xs, z ∈ p := by
                    intro z hz'
                    exact hl z (by simp [hz'])
                  obtain ⟨q', hq'⟩ := ihl hxs
                  refine ⟨y :: q', ?_⟩
                  simp [hy, hq']
            obtain ⟨q', hqmap⟩ :=
              pullList p (by intro x hx; exact hx)

            have htarget :
                S.succ (F a) (q'.map F) c = some b0 := by
              rw [ha', hqmap]
              exact hsucc
            obtain ⟨b, hb⟩ :=
              hE1 F i hskip a q' c ⟨b0, htarget⟩

            have hab : a ⋖ b :=
              S.covBy_of_succ_eq_some hb
            have hblev :
                LevelTree.lev b = LevelTree.lev a + 1 :=
              LevelTree.covBy_level_eq hab
            have hia : i ≤ LevelTree.lev a := by
              by_contra hnot
              have halt : LevelTree.lev a < i :=
                Nat.lt_of_not_ge hnot
              have hFa :=
                H.level_eq_of_lt_skipped F.map i hskip halt
              have hFa' :
                  LevelTree.lev (F a) = q := by
                rw [ha', ha0lev]
              omega
            have hib : i < LevelTree.lev b := by
              omega
            have hexact :=
              H.succ_eq_above_skip F.map i hskip hb hib
            have hEq : b0 = F b := by
              apply Option.some.inj
              exact htarget.symm.trans hexact
            refine ⟨b, ?_⟩
            simpa [b0] using hEq.symm
  intro z hz j hj hji
  exact main j hz hj hji

end SMTree
end SuccessorTree

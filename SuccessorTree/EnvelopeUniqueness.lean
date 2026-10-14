import SuccessorTree.EnvelopeInvariantLevels
import Mathlib.Tactic

/-!
# Local inverse uniqueness for the envelope algorithm

Two maps skipping the same level and realizing the same crossing data have the
same inverse on the parameter-closed set relevant to the envelope algorithm.
This is the missing local step in uniqueness of embedding types.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

theorem source_level_succ_of_skipsOnly_image
    (H : SMTree S) (D : ShapeMap S) (i : Nat)
    (hD : D.SkipsOnly i)
    {d x : T} (hDx : D d = x)
    (hix : i < LevelTree.lev x) :
    LevelTree.lev d + 1 = LevelTree.lev x := by
  have hlev :
      LevelTree.lev x =
        if LevelTree.lev d < i
        then LevelTree.lev d
        else LevelTree.lev d + 1 := by
    calc
      LevelTree.lev x = LevelTree.lev (D d) := by rw [hDx]
      _ = H.levelMap D (LevelTree.lev d) :=
        (H.levelMap_eq D (a := d)).symm
      _ = _ := H.levelMap_of_skipsOnly D i hD (LevelTree.lev d)
  split at hlev
  · omega
  · omega

/-- Local inverse uniqueness below members of Z. -/
theorem oneLevel_preimage_unique_below
    (H : SMTree S) (D E : ShapeMap S) (i : Nat)
    (hD : D.SkipsOnly i) (hE : E.SkipsOnly i)
    (Z : Set T)
    (hparam : ParameterClosedOver S Z {j | i < j})
    (hno : ∀ ⦃z : T⦄, z ∈ Z → LevelTree.lev z ≠ i)
    (hcrossD :
      ∀ ⦃z : T⦄, z ∈ Z → ∀ (hiz : i < LevelTree.lev z),
        D (LevelTree.ancestor z i (Nat.le_of_lt hiz)) =
          LevelTree.ancestor z (i + 1) (Nat.succ_le_iff.mpr hiz))
    (hcrossE :
      ∀ ⦃z : T⦄, z ∈ Z → ∀ (hiz : i < LevelTree.lev z),
        E (LevelTree.ancestor z i (Nat.le_of_lt hiz)) =
          LevelTree.ancestor z (i + 1) (Nat.succ_le_iff.mpr hiz)) :
    ∀ {x z d e : T}, z ∈ Z → x ≤ z → LevelTree.lev x ≠ i →
      D d = x → E e = x → d = e := by
  intro x
  induction hn : LevelTree.lev x using Nat.strong_induction_on generalizing x with
  | h n ih =>
      intro z d e hz hxz hxne hDx hEx
      by_cases hbelow : n < i
      · have hDfix : D x = x :=
          H.eq_id_below_skip D i hD (by simpa [hn] using hbelow)
        have hEfix : E x = x :=
          H.eq_id_below_skip E i hE (by simpa [hn] using hbelow)
        have hd : d = x := D.injective (hDx.trans hDfix.symm)
        have he : e = x := E.injective (hEx.trans hEfix.symm)
        exact hd.trans he.symm
      have hin : i ≤ n := Nat.le_of_not_gt hbelow
      have hstrict : i < n := by omega
      by_cases hfirst : n = i + 1
      · have hiz : i < LevelTree.lev z := by
          have hle := LevelTree.level_le_of_le hxz
          rw [hn] at hle
          omega
        have hxanc :
            x =
              LevelTree.ancestor z (i + 1)
                (Nat.succ_le_iff.mpr hiz) := by
          apply LevelTree.eq_ancestor_of_le hxz
          exact hn.trans hfirst
        let a := LevelTree.ancestor z i (Nat.le_of_lt hiz)
        have hDa : D a = x := by
          dsimp [a]
          rw [hcrossD hz hiz, ← hxanc]
        have hEa : E a = x := by
          dsimp [a]
          rw [hcrossE hz hiz, ← hxanc]
        have hd : d = a := D.injective (hDx.trans hDa.symm)
        have he : e = a := E.injective (hEx.trans hEa.symm)
        exact hd.trans he.symm
      · have hfar : i + 1 < n := by omega
        have hDlev := source_level_succ_of_skipsOnly_image H D i hD hDx
          (by simpa [hn] using hstrict)
        have hElev := source_level_succ_of_skipsOnly_image H E i hE hEx
          (by simpa [hn] using hstrict)
        have hdlev : LevelTree.lev d = n - 1 := by omega
        have helev : LevelTree.lev e = n - 1 := by omega
        let k : Nat := n - 2
        have hkD : k ≤ LevelTree.lev d := by
          rw [hdlev]
          omega
        have hkE : k ≤ LevelTree.lev e := by
          rw [helev]
          omega
        let d0 := LevelTree.ancestor d k hkD
        let e0 := LevelTree.ancestor e k hkE
        have hd0d : d0 ≤ d := LevelTree.ancestor_le d k hkD
        have he0e : e0 ≤ e := LevelTree.ancestor_le e k hkE
        have hd0lev : LevelTree.lev d0 = k :=
          LevelTree.level_ancestor d k hkD
        have he0lev : LevelTree.lev e0 = k :=
          LevelTree.level_ancestor e k hkE
        have hd0cov : d0 ⋖ d := by
          apply LevelTree.covBy_of_le_level_succ hd0d
          rw [hd0lev, hdlev]
          dsimp [k]
          omega
        have he0cov : e0 ⋖ e := by
          apply LevelTree.covBy_of_le_level_succ he0e
          rw [he0lev, helev]
          dsimp [k]
          omega
        obtain ⟨pD, cD, hsD⟩ := S.s3 hd0cov
        obtain ⟨pE, cE, hsE⟩ := S.s3 he0cov
        have hiD : i < LevelTree.lev d := by rw [hdlev]; omega
        have hiE : i < LevelTree.lev e := by rw [helev]; omega
        have htD0 :=
          H.succ_eq_above_skip D i hD hsD hiD
        have htE0 :=
          H.succ_eq_above_skip E i hE hsE hiE
        have htD :
            S.succ (D d0) (pD.map D) cD = some x := by
          simpa [hDx] using htD0
        have htE :
            S.succ (E e0) (pE.map E) cE = some x := by
          simpa [hEx] using htE0
        have hsame := S.s2 htD htE
        have hbase : D d0 = E e0 := hsame.1
        have hparams : pD.map D = pE.map E := hsame.2.1
        have hlabel : cD = cE := hsame.2.2
        have htargetBaseLevel : LevelTree.lev (D d0) = n - 1 := by
          have hcov := S.covBy_of_succ_eq_some htD
          have hcovLev := LevelTree.covBy_level_eq hcov
          rw [hn] at hcovLev
          omega
        have hbaseLeX : D d0 ≤ x :=
          (S.covBy_of_succ_eq_some htD).le
        have hbaseLeZ : D d0 ≤ z := hbaseLeX.trans hxz
        have hbaseNe : LevelTree.lev (D d0) ≠ i := by
          rw [htargetBaseLevel]
          omega
        have hd0e0 : d0 = e0 := by
          exact ih (LevelTree.lev (D d0))
            (by rw [htargetBaseLevel]; omega)
            (x := D d0) rfl
            (z := z) (d := d0) (e := e0)
            hz hbaseLeZ hbaseNe rfl hbase.symm
        have hxAnc :
            x =
              LevelTree.ancestor z n (by
                have hle := LevelTree.level_le_of_le hxz
                simpa [hn] using hle) := by
          apply LevelTree.eq_ancestor_of_le hxz
          exact hn
        have hbaseAnc :
            D d0 =
              LevelTree.ancestor z (n - 1) (by
                have hle := LevelTree.level_le_of_le hbaseLeZ
                rw [htargetBaseLevel] at hle
                exact hle) := by
          apply LevelTree.eq_ancestor_of_le hbaseLeZ
          exact htargetBaseLevel
        have hparamTarget :
            ∀ ⦃y : T⦄, y ∈ pD.map D → y ∈ Z := by
          intro y hy
          have hstepZ :
              S.succ
                  (LevelTree.ancestor z (n - 1) (by
                    have hle := LevelTree.level_le_of_le hbaseLeZ
                    rw [htargetBaseLevel] at hle
                    exact hle))
                  (pD.map D) cD =
                some
                  (LevelTree.ancestor z n (by
                    have hle := LevelTree.level_le_of_le hxz
                    simpa [hn] using hle)) := by
            simpa [← hbaseAnc, ← hxAnc] using htD
          have hiBase : i < n - 1 := by omega
          have hBaseZ : n - 1 < LevelTree.lev z := by
            have hle := LevelTree.level_le_of_le hxz
            rw [hn] at hle
            omega
          have hstepZ' :
              S.succ
                  (LevelTree.ancestor z (n - 1) (by
                    have hle := LevelTree.level_le_of_le hbaseLeZ
                    rw [htargetBaseLevel] at hle
                    exact hle))
                  (pD.map D) cD =
                some
                  (LevelTree.ancestor z ((n - 1) + 1)
                    (Nat.succ_le_iff.mpr hBaseZ)) := by
            simpa only [show n - 1 + 1 = n by omega] using hstepZ
          exact hparam hz hiBase hBaseZ hstepZ' hy
        have hparamLevel :
            ∀ ⦃y : T⦄, y ∈ pD.map D → LevelTree.lev y < n := by
          intro y hy
          have hlt := S.parameter_level_lt htD hy
          rw [htargetBaseLevel] at hlt
          omega
        have list_preimages_unique :
            ∀ (p q : List T),
              p.map D = q.map E →
              (∀ ⦃y : T⦄, y ∈ p.map D → y ∈ Z) →
              (∀ ⦃y : T⦄, y ∈ p.map D → LevelTree.lev y < n) →
              p = q := by
          intro p
          induction p with
          | nil =>
              intro q hmap _ _
              cases q with
              | nil => rfl
              | cons v vs => simp at hmap
          | cons u us listIH =>
              intro q hmap hZ hLev
              cases q with
              | nil => simp at hmap
              | cons v vs =>
                  simp only [List.map_cons, List.cons.injEq] at hmap
                  have huZ : D u ∈ Z := hZ (by simp)
                  have huLt : LevelTree.lev (D u) < n := hLev (by simp)
                  have huv : u = v := by
                    exact ih (LevelTree.lev (D u)) huLt
                      (x := D u) rfl
                      (z := D u) (d := u) (e := v)
                      huZ le_rfl (hno huZ) rfl hmap.1.symm
                  have htailZ :
                      ∀ ⦃y : T⦄, y ∈ us.map D → y ∈ Z := by
                    intro y hy
                    exact hZ (by simp [hy])
                  have htailLev :
                      ∀ ⦃y : T⦄, y ∈ us.map D → LevelTree.lev y < n := by
                    intro y hy
                    exact hLev (by simp [hy])
                  have htail : us = vs :=
                    listIH vs hmap.2 htailZ htailLev
                  simp [huv, htail]
        have hlist : pD = pE :=
          list_preimages_unique pD pE hparams hparamTarget hparamLevel
        have hsome : (some d : Option T) = some e := by
          calc
            some d = S.succ d0 pD cD := hsD.symm
            _ = S.succ e0 pE cE := by rw [hd0e0, hlist, hlabel]
            _ = some e := hsE
        exact Option.some.inj hsome

/-- The two one-level maps therefore induce the same inverse set on Z. -/
theorem preimage_eq_of_oneLevel
    (H : SMTree S) (D E : ShapeMap S) (i : Nat)
    (hD : D.SkipsOnly i) (hE : E.SkipsOnly i)
    (Z : Set T)
    (hparam : ParameterClosedOver S Z {j | i < j})
    (hno : ∀ ⦃z : T⦄, z ∈ Z → LevelTree.lev z ≠ i)
    (hcrossD :
      ∀ ⦃z : T⦄, z ∈ Z → ∀ (hiz : i < LevelTree.lev z),
        D (LevelTree.ancestor z i (Nat.le_of_lt hiz)) =
          LevelTree.ancestor z (i + 1) (Nat.succ_le_iff.mpr hiz))
    (hcrossE :
      ∀ ⦃z : T⦄, z ∈ Z → ∀ (hiz : i < LevelTree.lev z),
        E (LevelTree.ancestor z i (Nat.le_of_lt hiz)) =
          LevelTree.ancestor z (i + 1) (Nat.succ_le_iff.mpr hiz))
    (hRangeD : Z ⊆ Set.range D)
    (hRangeE : Z ⊆ Set.range E) :
    D ⁻¹' Z = E ⁻¹' Z := by
  ext x
  constructor
  · intro hx
    have hDxZ : D x ∈ Z := hx
    obtain ⟨e, he⟩ := hRangeE hDxZ
    have hEq : x = e := by
      apply oneLevel_preimage_unique_below
        H D E i hD hE Z hparam hno hcrossD hcrossE
        hDxZ le_rfl (hno hDxZ) rfl he
    subst e
    simpa [he] using hDxZ
  · intro hx
    have hExZ : E x ∈ Z := hx
    obtain ⟨d, hd⟩ := hRangeD hExZ
    have hEq : d = x := by
      apply oneLevel_preimage_unique_below
        H D E i hD hE Z hparam hno hcrossD hcrossE
        hExZ le_rfl (hno hExZ) hd rfl
    subst d
    simpa [hd] using hExZ

end Envelope
end SMTree
end SuccessorTree

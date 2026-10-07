import SuccessorTree.EnvelopeInvariant
import SuccessorTree.ShapeSplit
import SuccessorTree.Canonical
import Mathlib.Tactic

/-!
# Minimality: extracting a one-level skip from a competing envelope

The key step in Proposition 5.5 is local.  If an admissible map crosses a
target level i without representing it, two applications of shape splitting
produce a one-level map which skips i and realises the crossing data.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

theorem canonicalExtension_level_before
    (H : SMTree S) (Q : MMap H) (i : Nat)
    (hfix : Q.FixesBelow H i)
    {k : Nat} (hki : k < i) :
    H.levelMap (H.canonicalExtension Q i).map k = k := by
  obtain ⟨x, hx⟩ := H.level_nonempty k
  calc
    H.levelMap (H.canonicalExtension Q i).map k =
        LevelTree.lev (H.canonicalExtension Q i x) := by
      simpa [hx] using
        H.levelMap_eq (H.canonicalExtension Q i).map (a := x)
    _ = LevelTree.lev (Q x) := by
      rw [H.canonicalExtension_agrees Q i x (by omega)]
    _ = LevelTree.lev x := by
      rw [hfix x (by simpa [hx] using hki)]
    _ = k := hx

/-- If the prescribed prefix fixes below i and sends level i to i+1, its
canonical extension skips exactly i. -/
theorem canonicalExtension_skipsOnly
    (H : SMTree S) (Q : MMap H) (i : Nat)
    (hfix : Q.FixesBelow H i)
    (hnext : H.levelMap Q.map i = i + 1) :
    (H.canonicalExtension Q i).map.SkipsOnly i := by
  change (H.canonicalExtension Q i).map.levelRange = {q | q ≠ i}
  rw [← H.range_levelMap (H.canonicalExtension Q i).map]
  ext q
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk⟩
    by_cases hki : k < i
    · have hlev :=
        canonicalExtension_level_before H Q i hfix hki
      rw [hlev] at hk
      omega
    · have hik : i ≤ k := Nat.le_of_not_gt hki
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hik
      rw [H.canonicalExtension_level_tail Q i d, hnext] at hk
      omega
  · intro hqi
    by_cases hqiLt : q < i
    · refine ⟨q, ?_⟩
      exact canonicalExtension_level_before H Q i hfix hqiLt
    · have hiq : i < q := by omega
      have hi1q : i + 1 ≤ q := by omega
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi1q
      refine ⟨i + d, ?_⟩
      rw [H.canonicalExtension_level_tail Q i d, hnext]
      omega

/-- Agreement on one source level gives equality of the corresponding
level-map values. -/
theorem levelMap_eq_of_agree_on_level
    (H : SMTree S) (F G : MMap H) (n : Nat)
    (h : ∀ x : T, LevelTree.lev x = n → F x = G x) :
    H.levelMap F.map n = H.levelMap G.map n := by
  obtain ⟨x, hx⟩ := H.level_nonempty n
  calc
    H.levelMap F.map n = LevelTree.lev (F x) := by
      simpa [hx] using H.levelMap_eq F.map (a := x)
    _ = LevelTree.lev (G x) := by rw [h x hx]
    _ = H.levelMap G.map n := by
      simpa [hx] using (H.levelMap_eq G.map (a := x)).symm

/-- A gap of an admissible map yields a one-level skip map realising every
crossing in a set contained in its range. This is the core contradiction in
the minimality proof of Proposition 5.5. -/
theorem exists_oneLevel_skip_extension_of_gap
    (H : SMTree S) (E : MMap H)
    (C : Set T) (i n : Nat)
    (hC : C ⊆ Set.range E)
    (htop : i < H.levelMap E.map n)
    (hmin : ∀ k < n, H.levelMap E.map k < i) :
    ∃ D : MMap H,
      D.map.SkipsOnly i ∧
      ∀ ⦃c : T⦄, c ∈ C → ∀ (hic : i < LevelTree.lev c),
        D (LevelTree.ancestor c i (Nat.le_of_lt hic)) =
          LevelTree.ancestor c (i + 1) (Nat.succ_le_iff.mpr hic) := by
  have hcut1 : SplitCut H E n (i + 1) := by
    cases n with
    | zero =>
        exact ⟨by omega, trivial⟩
    | succ k =>
        refine ⟨by omega, ?_⟩
        have hp := hmin k (by omega)
        simpa using (show H.levelMap E.map k < i + 1 by omega)
  obtain ⟨P1, Q1, hP1agree, hP1top, hQ1fix, hQ1P1⟩ :=
    H.exists_shapeSplit_factor E n (i + 1) hcut1
  have hcut0 : SplitCut H P1 n i := by
    cases n with
    | zero =>
        exact ⟨by omega, trivial⟩
    | succ k =>
        have hprev :
            H.levelMap P1.map k = H.levelMap E.map k := by
          apply levelMap_eq_of_agree_on_level H P1 E k
          intro x hx
          exact hP1agree x (by omega)
        refine ⟨by omega, ?_⟩
        simpa [hprev] using hmin k (by omega)
  obtain ⟨P0, Q, hP0agree, hP0top, hQfix, hQP0⟩ :=
    H.exists_shapeSplit_factor P1 n i hcut0
  have hQnext : H.levelMap Q.map i = i + 1 := by
    obtain ⟨x, hx⟩ := H.level_nonempty n
    have hP0lev : LevelTree.lev (P0 x) = i := by
      calc
        LevelTree.lev (P0 x) = H.levelMap P0.map n := by
          simpa [hx] using (H.levelMap_eq P0.map (a := x)).symm
        _ = i := hP0top
    have hP1lev : LevelTree.lev (P1 x) = i + 1 := by
      calc
        LevelTree.lev (P1 x) = H.levelMap P1.map n := by
          simpa [hx] using (H.levelMap_eq P1.map (a := x)).symm
        _ = i + 1 := hP1top
    calc
      H.levelMap Q.map i = LevelTree.lev (Q (P0 x)) := by
        simpa [hP0lev] using H.levelMap_eq Q.map (a := P0 x)
      _ = LevelTree.lev (P1 x) := by
        rw [hQP0 x (by omega)]
      _ = i + 1 := hP1lev
  let D : MMap H := H.canonicalExtension Q i
  have hDskip : D.map.SkipsOnly i :=
    canonicalExtension_skipsOnly H Q i hQfix hQnext
  refine ⟨D, hDskip, ?_⟩
  intro c hc hic
  obtain ⟨y, hy⟩ := hC hc
  have hEyLev :
      H.levelMap E.map (LevelTree.lev y) = LevelTree.lev c := by
    rw [H.levelMap_eq E.map (a := y), hy]
  have hny : n ≤ LevelTree.lev y := by
    by_contra hnot
    have hyn : LevelTree.lev y < n := Nat.lt_of_not_ge hnot
    have hsmall := hmin (LevelTree.lev y) hyn
    rw [hEyLev] at hsmall
    omega
  let x := LevelTree.ancestor y n hny
  have hxy : x ≤ y := LevelTree.ancestor_le y n hny
  have hxlev : LevelTree.lev x = n := LevelTree.level_ancestor y n hny
  have hP1data :=
    H.shapeSplit_top_le_level E P1 Q1 n (i + 1)
      hP1top hQ1fix hQ1P1 hxlev
  have hP0data :=
    H.shapeSplit_top_le_level P1 P0 Q n i
      hP0top hQfix hQP0 hxlev
  have hP1c : P1 x ≤ c := by
    exact hP1data.1.trans ((E.map.map_le_of_le hxy).trans_eq hy)
  have hP0c : P0 x ≤ c := hP0data.1.trans hP1c
  have hP1anc :
      P1 x =
        LevelTree.ancestor c (i + 1) (Nat.succ_le_iff.mpr hic) :=
    LevelTree.eq_ancestor_of_le hP1c hP1data.2
      (Nat.succ_le_iff.mpr hic)
  have hP0anc :
      P0 x = LevelTree.ancestor c i (Nat.le_of_lt hic) :=
    LevelTree.eq_ancestor_of_le hP0c hP0data.2 (Nat.le_of_lt hic)
  change D (LevelTree.ancestor c i (Nat.le_of_lt hic)) =
    LevelTree.ancestor c (i + 1) (Nat.succ_le_iff.mpr hic)
  rw [← hP0anc, ← hP1anc]
  change H.canonicalExtension Q i (P0 x) = P1 x
  rw [H.canonicalExtension_agrees Q i (P0 x) (by
    rw [hP0data.2])]
  exact hQP0 x (by omega)

end Envelope
end SMTree
end SuccessorTree

import SuccessorTree.ShapeSplit
import Mathlib.Tactic

/-!
# Transporting one-step coordinates across a finite prefix

The old manuscript attempted to commute a one-step map through a finite
shape map directly by M3.  The correct argument uses one shape split:
canonicalise the finite prefix, compose with the coordinate, then split the
top value back at the prefix terminal level.

No pullback axiom is used because the right coordinate is explicit.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Level maps compose. -/
theorem levelMap_comp
    (H : SMTree S) (F G : MMap H) (n : Nat) :
    H.levelMap (MMap.comp H F G).map n =
      H.levelMap F.map (H.levelMap G.map n) := by
  obtain ⟨x, hx⟩ := H.level_nonempty n
  calc
    H.levelMap (MMap.comp H F G).map n =
        LevelTree.lev (F (G x)) := by
      simpa [hx] using
        H.levelMap_eq (MMap.comp H F G).map (a := x)
    _ = H.levelMap F.map (LevelTree.lev (G x)) :=
      (H.levelMap_eq F.map (a := G x)).symm
    _ = H.levelMap F.map (H.levelMap G.map n) := by
      have hg := H.levelMap_eq G.map (a := x)
      simpa [hx] using congrArg (H.levelMap F.map) hg.symm

/-- Fixing below n forces the level map to be the identity below n. -/
theorem levelMap_eq_of_fixesBelow
    (H : SMTree S) (F : MMap H) (n : Nat)
    (hfix : F.FixesBelow H n)
    {j : Nat} (hj : j < n) :
    H.levelMap F.map j = j := by
  obtain ⟨x, hx⟩ := H.level_nonempty j
  calc
    H.levelMap F.map j = LevelTree.lev (F x) := by
      simpa [hx] using H.levelMap_eq F.map (a := x)
    _ = LevelTree.lev x := by rw [hfix x (by simpa [hx] using hj)]
    _ = j := hx

/-- The canonical prefix itself has the prescribed terminal level. -/
theorem canonicalExtension_topLevel
    (H : SMTree S) (K : MMap H) (n : Nat) :
    H.levelMap (H.canonicalExtension K n).map n =
      H.levelMap K.map n :=
  H.canonicalExtension_level_at_prefix K n

/-- The level map of a canonical prefix after an arbitrary coordinate fixing
the old lower levels. -/
theorem canonical_comp_level_top
    (H : SMTree S) (K s : MMap H) (n : Nat)
    (hs : s.FixesBelow H n) :
    H.levelMap
        (MMap.comp H (H.canonicalExtension K n) s).map n =
      H.levelMap K.map n + (H.levelMap s.map n - n) := by
  let r := H.levelMap s.map n
  have hnr : n ≤ r := H.levelMap_id_le s.map n
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnr
  have hr : r = n + k := hk
  rw [H.levelMap_comp (H.canonicalExtension K n) s n]
  change H.levelMap (H.canonicalExtension K n).map r =
    H.levelMap K.map n + (r - n)
  rw [hr, H.canonicalExtension_level_tail K n k]
  omega

/-- Correct direct transport lemma.

Let C be the canonical extension of K through source level n and let s fix
all lower levels.  Then there is a target coordinate t fixing below the
terminal level m=C(n) such that C∘s=t∘C through level n.  The amount by which
t moves level m is exactly the amount by which s moves level n. -/
theorem exists_transport_across_canonical
    (H : SMTree S) (K s : MMap H) (n : Nat)
    (hs : s.FixesBelow H n) :
    let C := H.canonicalExtension K n
    let m := H.levelMap K.map n
    ∃ t : MMap H,
      t.FixesBelow H m ∧
      H.levelMap t.map m =
        m + (H.levelMap s.map n - n) ∧
      ∀ x : T, LevelTree.lev x ≤ n →
        C (s x) = t (C x) := by
  let C := H.canonicalExtension K n
  let m := H.levelMap K.map n
  let F := MMap.comp H C s
  have hcut : SplitCut H F n m := by
    refine ⟨?_, ?_⟩
    · have htop := H.canonical_comp_level_top K s n hs
      change m ≤ H.levelMap F.map n
      change m ≤ H.levelMap
        (MMap.comp H (H.canonicalExtension K n) s).map n
      rw [htop]
      exact Nat.le_add_right _ _
    · cases n with
      | zero =>
          trivial
      | succ j =>
          have hsJ :
              H.levelMap s.map j = j :=
            H.levelMap_eq_of_fixesBelow s (j + 1) hs (Nat.lt_succ_self j)
          have hCj :
              H.levelMap C.map j = H.levelMap K.map j := by
            obtain ⟨x, hx⟩ := H.level_nonempty j
            calc
              H.levelMap C.map j = LevelTree.lev (C x) := by
                simpa [hx] using H.levelMap_eq C.map (a := x)
              _ = LevelTree.lev (K x) := by
                rw [H.canonicalExtension_agrees K (j + 1) x (by omega)]
              _ = H.levelMap K.map j := by
                simpa [hx] using (H.levelMap_eq K.map (a := x)).symm
          change H.levelMap F.map j < m
          rw [H.levelMap_comp C s j, hsJ, hCj]
          exact H.levelMap_strictMono K.map (Nat.lt_succ_self j)
  obtain ⟨P, t, hPagree, hPtop, htfix, htP⟩ :=
    H.exists_shapeSplit_factor F n m hcut
  have hPC :
      ∀ x : T, LevelTree.lev x ≤ n → P x = C x := by
    intro x hx
    by_cases hxn : LevelTree.lev x < n
    · calc
        P x = F x := hPagree x hxn
        _ = C (s x) := rfl
        _ = C x := by rw [hs x hxn]
    · have hxlev : LevelTree.lev x = n := by omega
      have hsplit :=
        H.shapeSplit_top_le_level F P t n m hPtop htfix htP hxlev
      have hCxLev : LevelTree.lev (C x) = m := by
        calc
          LevelTree.lev (C x) =
              H.levelMap C.map n := by
            simpa [hxlev] using
              (H.levelMap_eq C.map (a := x)).symm
          _ = m := H.canonicalExtension_topLevel K n
      have hxs : x ≤ s x :=
        H.MMap.le_apply_at_cut s n hs hxlev
      have hCbelow : C x ≤ C (s x) :=
        C.map.map_le_of_le hxs
      have hF : F x = C (s x) := rfl
      have hPbelow : P x ≤ C (s x) := by
        simpa [hF] using hsplit.1
      have hcomp :
          P x ≤ C x ∨ C x ≤ P x :=
        LevelTree.comparable_below hPbelow hCbelow
      rcases hcomp with hle | hle
      · exact LevelTree.same_level_of_le hle
          (hsplit.2.trans hCxLev.symm)
      · exact (LevelTree.same_level_of_le hle
          (hCxLev.trans hsplit.2.symm)).symm
  have htLevel :
      H.levelMap t.map m =
        m + (H.levelMap s.map n - n) := by
    obtain ⟨x, hx⟩ := H.level_nonempty n
    have hPxLev : LevelTree.lev (P x) = m := by
      calc
        LevelTree.lev (P x) =
            H.levelMap P.map n := by
          simpa [hx] using (H.levelMap_eq P.map (a := x)).symm
        _ = m := hPtop
    calc
      H.levelMap t.map m =
          LevelTree.lev (t (P x)) := by
        simpa [hPxLev] using H.levelMap_eq t.map (a := P x)
      _ = LevelTree.lev (F x) := by
        rw [htP x (by simpa [hx])]
      _ = H.levelMap F.map n := by
        simpa [hx] using (H.levelMap_eq F.map (a := x)).symm
      _ = m + (H.levelMap s.map n - n) := by
        exact H.canonical_comp_level_top K s n hs
  refine ⟨t, htfix, htLevel, ?_⟩
  intro x hx
  calc
    C (s x) = F x := rfl
    _ = t (P x) := (htP x hx).symm
    _ = t (C x) := by rw [hPC x hx]

end SMTree
end SuccessorTree

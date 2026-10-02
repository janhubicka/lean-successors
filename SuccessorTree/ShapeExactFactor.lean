import SuccessorTree.Canonical
import Mathlib.Tactic

/-!
# Normalising one further shape level

The direct fusion proof repeatedly uses the following finite factorisation.
After a finite prefix has been fixed, M2 closes the next gap.  The resulting
gap-closed factor agrees with the canonical extension on the entire next
source level; the remaining outer factor fixes everything below the new cut.
This is the precise replacement for the informal "truncate at the last image
level" step in the manuscript.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

private theorem list_map_eq_of_agree
    (p : List T) (F G : MMap H)
    (h : ∀ x ∈ p, F x = G x) :
    p.map F = p.map G := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
      have hx : F x = G x := h x (by simp)
      have hxs : ∀ y ∈ xs, F y = G y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons]
      rw [hx, ih hxs]

/-- Two M-maps which agree through source level n and whose next image level
is consecutive must also agree through source level n+1. -/
theorem agrees_succ_of_consecutive
    (H : SMTree S) (F G : MMap H) (n : Nat)
    (hagree : ∀ x : T, LevelTree.lev x ≤ n → F x = G x)
    (hF :
      H.levelMap F.map (n + 1) =
        H.levelMap F.map n + 1)
    (hG :
      H.levelMap G.map (n + 1) =
        H.levelMap G.map n + 1) :
    ∀ x : T, LevelTree.lev x ≤ n + 1 → F x = G x := by
  intro x hx
  by_cases hxn : LevelTree.lev x ≤ n
  · exact hagree x hxn
  · have hxlev : LevelTree.lev x = n + 1 := by omega
    let y := LevelTree.ancestor x n (by omega)
    have hylev : LevelTree.lev y = n :=
      LevelTree.level_ancestor x n (by omega)
    have hyx : y ≤ x :=
      LevelTree.ancestor_le x n (by omega)
    have hcover : y ⋖ x := by
      apply LevelTree.covBy_of_le_level_succ hyx
      omega
    obtain ⟨p, c, hsucc⟩ := S.s3 hcover
    have hyEq : F y = G y :=
      hagree y (by simpa [hylev])
    have hpEq : p.map F = p.map G := by
      apply list_map_eq_of_agree
      intro z hz
      have hzlt : LevelTree.lev z < n := by
        have hz' := S.parameter_level_lt hsucc hz
        simpa [hylev] using hz'
      exact hagree z (Nat.le_of_lt hzlt)
    have hFlevels :
        H.levelMap F.map (LevelTree.lev x) =
          H.levelMap F.map (LevelTree.lev y) + 1 := by
      simpa [hxlev, hylev] using hF
    have hGlevels :
        H.levelMap G.map (LevelTree.lev x) =
          H.levelMap G.map (LevelTree.lev y) + 1 := by
      simpa [hxlev, hylev] using hG
    have hFs :=
      H.succ_eq_of_consecutive_levels F.map hsucc hFlevels
    have hGs :=
      H.succ_eq_of_consecutive_levels G.map hsucc hGlevels
    have hsome : (some (F x) : Option T) = some (G x) := by
      calc
        some (F x) = S.succ (F y) (p.map F) c := hFs.symm
        _ = S.succ (G y) (p.map G) c := by rw [hyEq, hpEq]
        _ = some (G x) := hGs
    exact Option.some.inj hsome

/-- Normal form for one further source level.

For every M-map K, its restriction through n+1 factors through the canonical
extension of its restriction through n.  The outer factor fixes all levels
strictly below the first new target level. -/
theorem exists_factor_through_canonical_succ
    (H : SMTree S) (K : MMap H) (n : Nat) :
    ∃ Q : MMap H,
      Q.FixesBelow H (H.levelMap K.map n + 1) ∧
      H.levelMap Q.map (H.levelMap K.map n + 1) =
        H.levelMap K.map (n + 1) ∧
      ∀ x : T, LevelTree.lev x ≤ n + 1 →
        Q (H.canonicalExtension K n x) = K x := by
  obtain ⟨P, Q, hPagree, hQfix, hQP, hPnext⟩ :=
    H.exists_close_gap_factor K n
  have hPn :
      H.levelMap P.map n = H.levelMap K.map n := by
    obtain ⟨x, hx⟩ := H.level_nonempty n
    calc
      H.levelMap P.map n = LevelTree.lev (P x) := by
        simpa [hx] using H.levelMap_eq P.map (a := x)
      _ = LevelTree.lev (K x) := by
        rw [hPagree x (by simpa [hx])]
      _ = H.levelMap K.map n := by
        simpa [hx] using (H.levelMap_eq K.map (a := x)).symm
  let C : MMap H := H.canonicalExtension K n
  have hPCprefix :
      ∀ x : T, LevelTree.lev x ≤ n → P x = C x := by
    intro x hx
    calc
      P x = K x := hPagree x hx
      _ = C x := (H.canonicalExtension_agrees K n x hx).symm
  have hPconsecutive :
      H.levelMap P.map (n + 1) =
        H.levelMap P.map n + 1 := by
    rw [hPnext, hPn]
  have hCconsecutive :
      H.levelMap C.map (n + 1) =
        H.levelMap C.map n + 1 := by
    exact H.canonicalExtension_level_succ K n n le_rfl
  have hPC :
      ∀ x : T, LevelTree.lev x ≤ n + 1 → P x = C x :=
    H.agrees_succ_of_consecutive P C n hPCprefix
      hPconsecutive hCconsecutive
  have hQC :
      ∀ x : T, LevelTree.lev x ≤ n + 1 → Q (C x) = K x := by
    intro x hx
    rw [← hPC x hx]
    exact hQP x hx
  have hQlevel :
      H.levelMap Q.map (H.levelMap K.map n + 1) =
        H.levelMap K.map (n + 1) := by
    obtain ⟨x, hx⟩ := H.level_nonempty (n + 1)
    have hClev :
        LevelTree.lev (C x) = H.levelMap K.map n + 1 := by
      calc
        LevelTree.lev (C x) =
            H.levelMap C.map (n + 1) := by
          simpa [hx] using (H.levelMap_eq C.map (a := x)).symm
        _ = H.levelMap C.map n + 1 :=
          H.canonicalExtension_level_succ K n n le_rfl
        _ = H.levelMap K.map n + 1 := by
          rw [H.canonicalExtension_level_at_prefix K n]
    have hKlev :
        LevelTree.lev (K x) = H.levelMap K.map (n + 1) := by
      simpa [hx] using (H.levelMap_eq K.map (a := x)).symm
    calc
      H.levelMap Q.map (H.levelMap K.map n + 1) =
          LevelTree.lev (Q (C x)) := by
        simpa [hClev] using H.levelMap_eq Q.map (a := C x)
      _ = LevelTree.lev (K x) := by
        rw [hQC x (by simpa [hx])]
      _ = H.levelMap K.map (n + 1) := hKlev
  exact ⟨Q, hQfix, hQlevel, hQC⟩

end SMTree
end SuccessorTree

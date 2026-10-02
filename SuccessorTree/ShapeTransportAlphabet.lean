import SuccessorTree.ShapeTransport
import SuccessorTree.ShapePigeonhole
import Mathlib.Tactic

/-!
# Transporting the one-level alphabet across a canonical prefix

A coordinate at the frozen source cut can be pushed to the terminal target
cut of a canonical finite prefix.  Canonical extension turns the transported
map into a genuine one-level letter at the target cut.  On the prescribed
finite source segment, the resulting high letter commutes with the canonical
prefix.

This is the anchored replacement for the false unrestricted pullback used in
the old fat-tree proof.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- A canonical extension which fixes below m and moves level m to m+1 skips
exactly target level m. -/
theorem canonicalExtension_skipsOnly_of_oneStep
    (H : SMTree S) (F : MMap H) (m : Nat)
    (hfix : F.FixesBelow H m)
    (htop : H.levelMap F.map m = m + 1) :
    (H.canonicalExtension F m).map.SkipsOnly m := by
  unfold ShapeMap.SkipsOnly
  rw [← H.range_levelMap (H.canonicalExtension F m).map]
  ext q
  constructor
  · rintro ⟨j, hj⟩
    intro hqm
    subst q
    by_cases hjm : j < m
    · have hlev :
          H.levelMap (H.canonicalExtension F m).map j = j := by
        obtain ⟨x, hx⟩ := H.level_nonempty j
        calc
          H.levelMap (H.canonicalExtension F m).map j =
              LevelTree.lev (H.canonicalExtension F m x) := by
            simpa [hx] using
              H.levelMap_eq (H.canonicalExtension F m).map (a := x)
          _ = LevelTree.lev (F x) := by
            rw [H.canonicalExtension_agrees F m x (by omega)]
          _ = LevelTree.lev x := by
            rw [hfix x (by simpa [hx] using hjm)]
          _ = j := hx
      rw [hlev] at hj
      omega
    · have hmj : m ≤ j := Nat.le_of_not_gt hjm
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hmj
      rw [hk, H.canonicalExtension_level_tail F m k, htop] at hj
      omega
  · intro hqm
    by_cases hqm' : q < m
    · refine ⟨q, ?_⟩
      obtain ⟨x, hx⟩ := H.level_nonempty q
      calc
        H.levelMap (H.canonicalExtension F m).map q =
            LevelTree.lev (H.canonicalExtension F m x) := by
          simpa [hx] using
            H.levelMap_eq (H.canonicalExtension F m).map (a := x)
        _ = LevelTree.lev (F x) := by
          rw [H.canonicalExtension_agrees F m x (by omega)]
        _ = LevelTree.lev x := by
          rw [hfix x (by simpa [hx] using hqm')]
        _ = q := hx
    · have hmq : m < q := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hmq)
      refine ⟨m + k, ?_⟩
      rw [H.canonicalExtension_level_tail F m k, htop]
      omega

/-- The chosen transported map for a lower one-level letter. -/
noncomputable def transportedMap
    (H : SMTree S) (K : MMap H) (n : Nat)
    (e : OneLevelLetter H n) : MMap H :=
  Classical.choose
    (H.exists_transport_across_canonical K e.toMMap n
      (by
        intro x hx
        exact e.eq_id_below H hx))

theorem transportedMap_spec
    (H : SMTree S) (K : MMap H) (n : Nat)
    (e : OneLevelLetter H n) :
    let C := H.canonicalExtension K n
    let m := H.levelMap K.map n
    (H.transportedMap K n e).FixesBelow H m ∧
      H.levelMap (H.transportedMap K n e).map m = m + 1 ∧
      ∀ x : T, LevelTree.lev x ≤ n →
        C (e x) = (H.transportedMap K n e) (C x) := by
  have hs : e.toMMap.FixesBelow H n := by
    intro x hx
    exact e.eq_id_below H hx
  rcases Classical.choose_spec
      (H.exists_transport_across_canonical K e.toMMap n hs) with
    ⟨hfix, hlev, hcomm⟩
  refine ⟨hfix, ?_, hcomm⟩
  have he :
      H.levelMap e.toMMap.map n = n + 1 := by
    rw [H.levelMap_of_skipsOnly e.toMMap.map n e.skips]
    simp
  rw [he] at hlev
  simpa using hlev

/-- Transport a source-cut letter to a genuine one-level letter at the
terminal target cut of K. -/
noncomputable def transportLetter
    (H : SMTree S) (K : MMap H) (n : Nat)
    (e : OneLevelLetter H n) :
    OneLevelLetter H (H.levelMap K.map n) := by
  let t := H.transportedMap K n e
  have htfix :
      t.FixesBelow H (H.levelMap K.map n) :=
    (H.transportedMap_spec K n e).1
  have httop :
      H.levelMap t.map (H.levelMap K.map n) =
        H.levelMap K.map n + 1 :=
    (H.transportedMap_spec K n e).2.1
  exact ⟨H.canonicalExtension t (H.levelMap K.map n),
    H.canonicalExtension_skipsOnly_of_oneStep
      t (H.levelMap K.map n) htfix httop⟩

/-- The transported high letter commutes with the canonical finite prefix on
the whole prescribed source segment. -/
theorem transportLetter_commutes
    (H : SMTree S) (K : MMap H) (n : Nat)
    (e : OneLevelLetter H n)
    (x : T) (hx : LevelTree.lev x ≤ n) :
    let C := H.canonicalExtension K n
    H.transportLetter K n e (C x) = C (e x) := by
  let C := H.canonicalExtension K n
  let t := H.transportedMap K n e
  have ht :=
    (H.transportedMap_spec K n e).2.2 x hx
  have hClev :
      LevelTree.lev (C x) ≤ H.levelMap K.map n := by
    calc
      LevelTree.lev (C x) =
          H.levelMap C.map (LevelTree.lev x) :=
        (H.levelMap_eq C.map (a := x)).symm
      _ ≤ H.levelMap C.map n :=
        (H.levelMap_strictMono C.map).monotone hx
      _ = H.levelMap K.map n :=
        H.canonicalExtension_level_at_prefix K n
  change
    H.canonicalExtension t (H.levelMap K.map n) (C x) =
      C (e x)
  rw [H.canonicalExtension_agrees t (H.levelMap K.map n) (C x) hClev]
  exact ht.symm

end SMTree
end SuccessorTree

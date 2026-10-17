import SuccessorTree.Counterexample.NowhereDense
import Mathlib.Tactic

/-!
# Mandatory and inserted ancestral successor codes

The counterexample maps retain mandatory successor codes at an increasing
sequence of positive levels, and use the original root as a parameter at
all omitted levels. These two types of codes are disjoint. This is the
finite-code core of the compatibility obstruction, before constructing
the full infinite maps \`Q_A\`.
-/

namespace SuccessorTree.FreeAncestral

/-- Transport an ancestral tuple along any strictly increasing level map.
Each source parameter index \`k < n\` is replaced by \`levels k < levels n\`. -/
def remapTuple (levels : Nat → Nat) (mono : StrictMono levels)
    {n : Nat} (t : ParamTuple 1 n) : ParamTuple 1 (levels n) where
  len := t.len
  value := fun j => ⟨levels (t.value j).val, mono (t.value j).isLt⟩

/-- Mandatory code at a retained level: original parameters are transported
along the image-level map, never replaced by root markers. -/
def remapCode (levels : Nat → Nat) (mono : StrictMono levels)
    {n : Nat} (c : Code Unit 1 n) : Code Unit 1 (levels n) where
  label := ()
  params := remapTuple levels mono c.params

@[simp] theorem levelList_remapTuple (levels : Nat → Nat)
    (mono : StrictMono levels) {n : Nat} (t : ParamTuple 1 n) :
    levelList (remapTuple levels mono t) = (levelList t).map levels := by
  simp only [levelList, remapTuple, List.map_ofFn]
  rfl

/-- Mandatory codes are never marked with the original root if the
source root maps to a *positive* target level. -/
theorem remapCode_avoids_root (levels : Nat → Nat)
    (mono : StrictMono levels) (pos : 0 < levels 0)
    {n : Nat} (c : Code Unit 1 n) :
    0 ∉ levelList (remapCode levels mono c).params := by
  change 0 ∉ List.ofFn
    (fun j : Fin c.params.len.val => levels (c.params.value j).val)
  intro hzero
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hzero
  have hle : levels 0 ≤ levels (c.params.value j).val :=
    mono.monotone (Nat.zero_le _)
  omega

/-- Inserted code at a positive target level: one parameter referencing
precisely the original root (target level zero). -/
def rootMarkerCode (m : Nat) (hm : 0 < m) : Code Unit 1 m where
  label := ()
  params :=
    { len := ⟨1, by decide⟩
      value := fun _ => ⟨0, hm⟩ }

/-- The actual distinguishing parameter of the counterexample. -/
theorem rootMarkerCode_has_root (m : Nat) (hm : 0 < m) :
    0 ∈ levelList (rootMarkerCode m hm).params := by
  change 0 ∈ List.ofFn (fun _ : Fin 1 => (0 : Nat))
  decide

/-- Remapping mandatory source codes is injective. -/
theorem remapTuple_injective (levels : Nat → Nat)
    (mono : StrictMono levels) {n : Nat} :
    Function.Injective
      (remapTuple levels mono : ParamTuple 1 n → ParamTuple 1 (levels n)) := by
  intro t u h
  apply levelList_injective
  have hm := congrArg (levelList (arity := 1)) h
  rw [levelList_remapTuple, levelList_remapTuple] at hm
  exact list_map_injective_of_injective mono.injective hm

theorem remapCode_injective (levels : Nat → Nat)
    (mono : StrictMono levels) {n : Nat} :
    Function.Injective
      (remapCode levels mono : Code Unit 1 n → Code Unit 1 (levels n)) := by
  rintro ⟨lc, tc⟩ ⟨ld, td⟩ h
  cases lc
  cases ld
  have ht : tc = td :=
    remapTuple_injective levels mono (congrArg Code.params h)
  subst td
  rfl

end SuccessorTree.FreeAncestral

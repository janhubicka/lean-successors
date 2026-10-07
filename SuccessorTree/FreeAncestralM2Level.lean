import SuccessorTree.FreeAncestralM2Prep
import Mathlib.Tactic

/-! # Level map for the inner M2 factor

Below the chosen source cut n the inner factor follows F.  Source level n is
lowered to the missing target level h, and all later source levels continue
consecutively above h.  This file isolates the arithmetic needed by the
recursive inner shape map.
-/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat}
variable [Fintype Label] [Nonempty Label]

/-- Target level used by a shape map F on source level k. -/
noncomputable def imageLevel
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (k : Nat) : Nat :=
  (F (canonicalNode (Label := Label) (arity := arity) k)).level

theorem imageLevel_eq
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    {x : Node Label arity}
    (hx : x.level = k) :
    (F x).level = imageLevel F k := by
  unfold imageLevel
  apply F.level_eq_of_level_eq
  simpa [canonicalNode_level] using hx

theorem imageLevel_strictMono
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity))) :
    StrictMono (imageLevel F) := by
  intro i j hij
  unfold imageLevel
  apply F.level_lt_of_level_lt
  simpa using hij

theorem imageLevel_ne_of_skips
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (h : Nat)
    (hskip : F.Skips h)
    (k : Nat) :
    imageLevel F k ≠ h := by
  intro heq
  apply hskip
  exact
    ⟨canonicalNode (Label := Label) (arity := arity) k,
      by simpa [imageLevel] using heq⟩

/-- Level map of the inner M2 compression. -/
noncomputable def m2InnerLevel
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h k : Nat) : Nat :=
  if k < n then imageLevel F k else h + (k - n)

@[simp] theorem m2InnerLevel_of_lt
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    {n h k : Nat}
    (hk : k < n) :
    m2InnerLevel F n h k = imageLevel F k := by
  simp [m2InnerLevel, hk]

@[simp] theorem m2InnerLevel_of_ge
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    {n h k : Nat}
    (hk : n ≤ k) :
    m2InnerLevel F n h k = h + (k - n) := by
  simp [m2InnerLevel, Nat.not_lt.mpr hk]

@[simp] theorem m2InnerLevel_at_cut
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat) :
    m2InnerLevel F n h n = h := by
  simp [m2InnerLevel]

theorem imageLevel_cut
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1) :
    imageLevel F n = h + 1 := by
  symm
  apply hlevel
  exact canonicalNode_level n

theorem imageLevel_below_lt_missing
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h k : Nat)
    (hk : k < n)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1) :
    imageLevel F k < h := by
  have hlt :
      imageLevel F k < imageLevel F n :=
    imageLevel_strictMono F hk
  rw [imageLevel_cut F n h hlevel] at hlt
  have hne : imageLevel F k ≠ h :=
    imageLevel_ne_of_skips F h hskip k
  omega

theorem m2InnerLevel_strictMono
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1) :
    StrictMono (m2InnerLevel F n h) := by
  intro i j hij
  by_cases hi : i < n
  · by_cases hj : j < n
    · rw [m2InnerLevel_of_lt F hi,
          m2InnerLevel_of_lt F hj]
      exact imageLevel_strictMono F hij
    · have hjge : n ≤ j := Nat.le_of_not_gt hj
      rw [m2InnerLevel_of_lt F hi,
          m2InnerLevel_of_ge F hjge]
      have hilth :
          imageLevel F i < h :=
        imageLevel_below_lt_missing
          F n h i hi hskip hlevel
      omega
  · have hige : n ≤ i := Nat.le_of_not_gt hi
    have hjge : n ≤ j := hige.trans (Nat.le_of_lt hij)
    rw [m2InnerLevel_of_ge F hige,
        m2InnerLevel_of_ge F hjge]
    omega

/-- Transport an intrinsic parameter tuple through the inner M2 level map. -/
noncomputable def m2InnerParamTuple
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (k : Nat)
    (t : ParamTuple arity k) :
    ParamTuple arity (m2InnerLevel F n h k) where
  len := t.len
  value := fun j =>
    ⟨m2InnerLevel F n h (t.value j).val, by
      exact m2InnerLevel_strictMono F n h hskip hlevel
        (t.value j).isLt⟩

@[simp] theorem m2InnerParamTuple_len
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (k : Nat)
    (t : ParamTuple arity k) :
    (m2InnerParamTuple F n h hskip hlevel k t).len = t.len := rfl

end FreeAncestral
end SuccessorTree

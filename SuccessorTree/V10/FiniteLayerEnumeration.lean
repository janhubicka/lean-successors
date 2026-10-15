import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Enumerating positive finite layers in their prescribed order

The cumulative offset gives an explicit rank on the disjoint union
of Fin (width n). Positivity makes these finite intervals partition Nat.
The inverse rank is therefore exhaustive, has no repetitions, and has
nondecreasing layer index. No enumeration hypothesis is assumed.
-/

namespace SuccessorTree.V10.FiniteLayerEnumeration

/-- Starting index of layer n. -/
def offset (width : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => offset width n + width n

@[simp] theorem offset_zero (width : Nat → Nat) : offset width 0 = 0 := rfl

@[simp] theorem offset_succ (width : Nat → Nat) (n : Nat) :
    offset width (n+1) = offset width n + width n := rfl

theorem offset_mono (width : Nat → Nat) : Monotone (offset width) :=
  monotone_nat_of_le_succ (fun n => by simp [offset])

theorem index_le_offset (width : Nat → Nat) (hPos : ∀ n, 0 < width n)
    (n : Nat) : n ≤ offset width n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [offset_succ]
      have hp := hPos n
      omega

/-- Rank the i-th element of layer n by its cumulative offset plus i. -/
def rank (width : Nat → Nat) (x : Σ n : Nat, Fin (width n)) : Nat :=
  offset width x.1 + x.2.val

theorem rank_lt_of_layer_lt (width : Nat → Nat)
    (x y : Σ n : Nat, Fin (width n)) (h : x.1 < y.1) :
    rank width x < rank width y := by
  have hi := x.2.isLt
  have hm := offset_mono width (Nat.succ_le_of_lt h)
  rw [offset_succ] at hm
  dsimp [rank]
  omega

theorem rank_injective (width : Nat → Nat) : Function.Injective (rank width) := by
  rintro ⟨n,i⟩ ⟨m,j⟩ h
  have hnm : n = m := by
    rcases lt_trichotomy n m with hlt | heq | hgt
    · have hh := rank_lt_of_layer_lt width ⟨n,i⟩ ⟨m,j⟩ hlt
      omega
    · exact heq
    · have hh := rank_lt_of_layer_lt width ⟨m,j⟩ ⟨n,i⟩ hgt
      omega
  subst m
  have hij : i = j := by
    apply Fin.ext
    change offset width n + i.val = offset width n + j.val at h
    omega
  subst j
  rfl

/-- Every natural index belongs to one of the finite layer intervals.
The least upper endpoint selects its layer; subtraction selects its entry. -/
theorem rank_surjective (width : Nat → Nat) (hPos : ∀ n, 0 < width n) :
    Function.Surjective (rank width) := by
  intro m
  have hex : ∃ n : Nat, m < offset width (n+1) := by
    refine ⟨m, ?_⟩
    have hm := index_le_offset width hPos (m+1)
    omega
  let n := Nat.find hex
  have hUpper : m < offset width (n+1) := Nat.find_spec hex
  have hLower : offset width n ≤ m := by
    by_cases hz : n = 0
    · simp [hz]
    · have hPred : n-1+1 = n := by omega
      have hlt : n-1 < Nat.find hex := by change n-1 < n; omega
      have hNot := Nat.find_min hex hlt
      rw [hPred] at hNot
      omega
  have hi : m - offset width n < width n := by
    rw [offset_succ] at hUpper
    omega
  refine ⟨⟨n, ⟨m-offset width n,hi⟩⟩, ?_⟩
  change offset width n + (m-offset width n) = m
  omega

/-- The explicit rank is a bijection, not a possibly repetitive schedule. -/
noncomputable def rankEquiv (width : Nat → Nat) (hPos : ∀ n, 0 < width n) :
    (Σ n : Nat, Fin (width n)) ≃ Nat :=
  Equiv.ofBijective (rank width) ⟨rank_injective width, rank_surjective width hPos⟩

/-- Inverse ranks visit the layers in nondecreasing order. -/
theorem rankEquiv_symm_layer_mono (width : Nat → Nat)
    (hPos : ∀ n, 0 < width n) :
    Monotone (fun m : Nat => ((rankEquiv width hPos).symm m).1) := by
  intro i j hij
  by_contra h
  have hlt : ((rankEquiv width hPos).symm j).1 <
      ((rankEquiv width hPos).symm i).1 := Nat.lt_of_not_ge h
  have hh := rank_lt_of_layer_lt width
    ((rankEquiv width hPos).symm j) ((rankEquiv width hPos).symm i) hlt
  have hj : rank width ((rankEquiv width hPos).symm j) = j :=
    (rankEquiv width hPos).apply_symm_apply j
  have hi : rank width ((rankEquiv width hPos).symm i) = i :=
    (rankEquiv width hPos).apply_symm_apply i
  rw [hj, hi] at hh
  omega

end SuccessorTree.V10.FiniteLayerEnumeration

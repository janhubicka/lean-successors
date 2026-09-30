import SuccessorTree.HalesJewett.ForcingFusion
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# A concrete length-sorted schedule of starred lines

For a finite alphabet there are finitely many starred lines of each fixed raw
length. We list the lines of length 1, then length 2, and so on. This gives the
nondecreasing, unbounded schedule required by the fusion proof.
-/

namespace SuccessorTree
namespace HalesJewett

def lineSymbolEquivOption (α : Type u) : LineSymbol α ≃ Option α where
  toFun
    | .const a => some a
    | .parameter => none
  invFun
    | some a => .const a
    | none => .parameter
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

noncomputable instance lineSymbolFintype [Fintype α] :
    Fintype (LineSymbol α) :=
  Fintype.ofEquiv (Option α) (lineSymbolEquivOption α).symm

/-- A starred line represented as a function on exactly n coordinates. -/
abbrev FixedLine (α : Type u) (n : Nat) :=
  {f : Fin n → LineSymbol α // LineSymbol.parameter ∈ List.ofFn f}

noncomputable instance fixedLineFintype [Fintype α] :
    Fintype (FixedLine α n) :=
  Fintype.ofFinite _

def FixedLine.toStarLine (F : FixedLine α n) : StarLine α :=
  ⟨List.ofFn F.1, F.2⟩

theorem starLine_word_injective :
    Function.Injective (fun L : StarLine α => L.word) := by
  intro L K h
  cases L with
  | mk w hw =>
      cases K with
      | mk v hv =>
          cases h
          rfl

/-- All starred lines of one fixed raw length. -/
noncomputable def lineBucket [Fintype α] (n : Nat) : List (StarLine α) := by
  classical
  exact (Finset.univ : Finset (FixedLine α n)).toList.map FixedLine.toStarLine

theorem length_eq_of_mem_lineBucket
    [Fintype α] {n : Nat} {L : StarLine α}
    (hL : L ∈ lineBucket (α := α) n) :
    L.word.length = n := by
  classical
  rw [lineBucket] at hL
  rcases List.mem_map.mp hL with ⟨F, hF, rfl⟩
  simp [FixedLine.toStarLine]

theorem mem_lineBucket_self
    [Fintype α] (L : StarLine α) :
    L ∈ lineBucket (α := α) L.word.length := by
  classical
  let F : FixedLine α L.word.length :=
    ⟨fun i => L.word.get i, by
      simpa using L.hasParameter⟩
  have hF : F ∈ (Finset.univ : Finset (FixedLine α L.word.length)).toList := by
    simp
  have hEq : F.toStarLine = L := by
    apply starLine_word_injective
    simp [FixedLine.toStarLine, F]
  rw [lineBucket]
  exact List.mem_map.mpr ⟨F, hF, hEq⟩

theorem lineBucket_nonempty
    [Fintype α] (n : Nat) :
    (lineBucket (α := α) (n + 1)).length > 0 := by
  classical
  let F : FixedLine α (n + 1) :=
    ⟨fun _ => LineSymbol.parameter, by
      simp⟩
  have hF : F ∈ (Finset.univ : Finset (FixedLine α (n + 1))).toList := by
    simp
  have hm : F.toStarLine ∈ lineBucket (α := α) (n + 1) := by
    rw [lineBucket]
    exact List.mem_map.mpr ⟨F, hF, rfl⟩
  exact List.length_pos_iff_exists_mem.mpr ⟨_, hm⟩

/-- Size of the bucket of lines of raw length n+1. -/
noncomputable def lineBucketSize [Fintype α] (n : Nat) : Nat :=
  (lineBucket (α := α) (n + 1)).length

theorem lineBucketSize_pos [Fintype α] (n : Nat) :
    0 < lineBucketSize (α := α) n :=
  lineBucket_nonempty (α := α) n

/-- Start position of the bucket indexed by n (which contains lines of length
n+1). -/
noncomputable def lineBucketStart [Fintype α] : Nat → Nat
  | 0 => 0
  | n + 1 =>
      lineBucketStart (α := α) n + lineBucketSize (α := α) n

@[simp] theorem lineBucketStart_zero [Fintype α] :
    lineBucketStart (α := α) 0 = 0 := rfl

theorem lineBucketStart_succ [Fintype α] (n : Nat) :
    lineBucketStart (α := α) (n + 1) =
      lineBucketStart (α := α) n + lineBucketSize (α := α) n := rfl

theorem lineBucketStart_lt_succ [Fintype α] (n : Nat) :
    lineBucketStart (α := α) n <
      lineBucketStart (α := α) (n + 1) := by
  rw [lineBucketStart_succ]
  exact Nat.lt_add_of_pos_right (lineBucketSize_pos (α := α) n)

theorem lineBucketStart_mono [Fintype α] :
    Monotone (lineBucketStart (α := α)) :=
  monotone_nat_of_le_succ fun n =>
    Nat.le_of_lt (lineBucketStart_lt_succ (α := α) n)

theorem index_le_lineBucketStart [Fintype α] :
    ∀ n : Nat, n ≤ lineBucketStart (α := α) n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [lineBucketStart_succ]
      have hp := lineBucketSize_pos (α := α) n
      omega

theorem exists_lineBucketStart_gt [Fintype α] (i : Nat) :
    ∃ n : Nat, i < lineBucketStart (α := α) (n + 1) := by
  refine ⟨i, ?_⟩
  have h := index_le_lineBucketStart (α := α) (i + 1)
  omega

/-- Index of the length bucket containing schedule position i. -/
noncomputable def lineBucketNumber [Fintype α] (i : Nat) : Nat :=
  Nat.find (exists_lineBucketStart_gt (α := α) i)

theorem lineBucketNumber_spec [Fintype α] (i : Nat) :
    i < lineBucketStart (α := α) (lineBucketNumber (α := α) i + 1) :=
  Nat.find_spec (exists_lineBucketStart_gt (α := α) i)

theorem lineBucketStart_number_le [Fintype α] (i : Nat) :
    lineBucketStart (α := α) (lineBucketNumber (α := α) i) ≤ i := by
  classical
  cases hnum : lineBucketNumber (α := α) i with
  | zero =>
      simp
  | succ n =>
      by_contra h
      have hi : i < lineBucketStart (α := α) (n + 1) :=
        Nat.lt_of_not_ge h
      have hmin :
          lineBucketNumber (α := α) i ≤ n :=
        Nat.find_min' (exists_lineBucketStart_gt (α := α) i) hi
      rw [hnum] at hmin
      omega

noncomputable def lineBucketOffset [Fintype α] (i : Nat) : Nat :=
  i - lineBucketStart (α := α) (lineBucketNumber (α := α) i)

theorem lineBucketOffset_lt [Fintype α] (i : Nat) :
    lineBucketOffset (α := α) i <
      lineBucketSize (α := α) (lineBucketNumber (α := α) i) := by
  have hlo := lineBucketStart_number_le (α := α) i
  have hhi := lineBucketNumber_spec (α := α) i
  rw [lineBucketStart_succ] at hhi
  unfold lineBucketOffset
  omega

theorem lineBucketOffset_lt_length [Fintype α] (i : Nat) :
    lineBucketOffset (α := α) i <
      (lineBucket (α := α) (lineBucketNumber (α := α) i + 1)).length := by
  exact lineBucketOffset_lt (α := α) i

/-- A harmless default line; the schedule's proved offset bound means
it is never actually selected. -/
def defaultStarLine (α : Type u) : StarLine α :=
  ⟨[LineSymbol.parameter], by simp⟩

/-- The line at schedule position i. -/
noncomputable def scheduledLine [Fintype α] (i : Nat) : StarLine α :=
  (lineBucket (α := α) (lineBucketNumber (α := α) i + 1)).getD
    (lineBucketOffset (α := α) i) (defaultStarLine α)

theorem scheduledLine_eq_get [Fintype α] (i : Nat) :
    scheduledLine (α := α) i =
      (lineBucket (α := α) (lineBucketNumber (α := α) i + 1)).get
        ⟨lineBucketOffset (α := α) i,
          lineBucketOffset_lt_length (α := α) i⟩ := by
  unfold scheduledLine
  simpa using
    (List.getD_eq_getElem
      (lineBucket (α := α) (lineBucketNumber (α := α) i + 1))
      (defaultStarLine α)
      (lineBucketOffset_lt_length (α := α) i))

theorem scheduledLine_length [Fintype α] (i : Nat) :
    (scheduledLine (α := α) i).word.length =
      lineBucketNumber (α := α) i + 1 := by
  rw [scheduledLine_eq_get]
  apply length_eq_of_mem_lineBucket
  exact List.get_mem _ _

theorem lineBucketNumber_mono [Fintype α] :
    Monotone (lineBucketNumber (α := α)) := by
  intro i j hij
  by_contra h
  have hlt : lineBucketNumber (α := α) j <
      lineBucketNumber (α := α) i := Nat.lt_of_not_ge h
  have hj := lineBucketNumber_spec (α := α) j
  have hmono :
      lineBucketStart (α := α) (lineBucketNumber (α := α) j + 1) ≤
        lineBucketStart (α := α) (lineBucketNumber (α := α) i) :=
    lineBucketStart_mono (α := α) (by omega)
  have hi := lineBucketStart_number_le (α := α) i
  omega

theorem scheduledLine_length_mono [Fintype α] :
    Monotone (fun i => (scheduledLine (α := α) i).word.length) := by
  intro i j hij
  change
    (scheduledLine (α := α) i).word.length ≤
      (scheduledLine (α := α) j).word.length
  rw [scheduledLine_length, scheduledLine_length]
  exact Nat.add_le_add_right (lineBucketNumber_mono (α := α) hij) 1

theorem scheduledLine_covers [Fintype α] (L : StarLine α) :
    ∃ i : Nat, scheduledLine (α := α) i = L := by
  classical
  have hpos : 0 < L.word.length := by
    exact lt_of_le_of_lt (Nat.zero_le _) L.length_star_lt_word_length
  obtain ⟨m, hm⟩ : ∃ m : Nat, L.word.length = m + 1 := by
    exact Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hmem : L ∈ lineBucket (α := α) (m + 1) := by
    simpa [hm] using mem_lineBucket_self (α := α) L
  obtain ⟨k, hk⟩ := List.get_of_mem hmem
  let i : Nat := lineBucketStart (α := α) m + k.val
  have hcandidate :
      i < lineBucketStart (α := α) (m + 1) := by
    rw [lineBucketStart_succ]
    have hklt : k.val < lineBucketSize (α := α) m := by
      simpa [lineBucketSize] using k.isLt
    dsimp [i]
    omega
  have hnum : lineBucketNumber (α := α) i = m := by
    apply le_antisymm
    · exact Nat.find_min' (exists_lineBucketStart_gt (α := α) i) hcandidate
    · by_contra hle
      have hlt : lineBucketNumber (α := α) i < m :=
        Nat.lt_of_not_ge hle
      have hspec := lineBucketNumber_spec (α := α) i
      have hmono :
          lineBucketStart (α := α)
              (lineBucketNumber (α := α) i + 1) ≤
            lineBucketStart (α := α) m :=
        lineBucketStart_mono (α := α) (by omega)
      have hiStart : lineBucketStart (α := α) m ≤ i := by
        dsimp [i]
        exact Nat.le_add_right _ _
      exact (not_lt_of_ge hiStart) (lt_of_lt_of_le hspec hmono)
  have hoff : lineBucketOffset (α := α) i = k.val := by
    unfold lineBucketOffset
    rw [hnum]
    dsimp [i]
    omega
  refine ⟨i, ?_⟩
  unfold scheduledLine
  rw [hnum, hoff]
  rw [List.getD_eq_getElem
      (lineBucket (α := α) (m + 1))
      (defaultStarLine α)
      k.isLt]
  simpa using hk

theorem scheduledLine_length_unbounded [Fintype α] :
    ∀ r : Nat, ∃ N : Nat, ∀ i : Nat, N ≤ i →
      r < (scheduledLine (α := α) i).word.length := by
  intro r
  refine ⟨lineBucketStart (α := α) r, ?_⟩
  intro i hi
  rw [scheduledLine_length]
  have hbn : r ≤ lineBucketNumber (α := α) i := by
    by_contra h
    have hlt : lineBucketNumber (α := α) i < r :=
      Nat.lt_of_not_ge h
    have hspec := lineBucketNumber_spec (α := α) i
    have hmono :
        lineBucketStart (α := α)
            (lineBucketNumber (α := α) i + 1) ≤
          lineBucketStart (α := α) r :=
      lineBucketStart_mono (α := α) (by omega)
    omega
  omega

/-- Concrete length-sorted line schedule for a finite alphabet. -/
noncomputable def finiteLineSchedule [Fintype α] : LineSchedule α where
  line := scheduledLine (α := α)
  covers := scheduledLine_covers (α := α)
  length_mono := scheduledLine_length_mono (α := α)
  length_unbounded := scheduledLine_length_unbounded (α := α)

end HalesJewett
end SuccessorTree

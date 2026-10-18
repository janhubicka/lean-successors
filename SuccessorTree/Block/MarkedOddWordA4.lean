import SuccessorTree.Block.MarkedParityExact

/-!
# Infinite marked-word A4 obstruction with literal four-line reductions

A marked odd word is an infinite sequence of complete one-variable
blocks, each with odd variable multiplicity. No parity condition is
put on constants in individual marked blocks: cuts may split them.
The four-block reduction groups [0,4) with one of three legal
three-variable selectors and copies the whole infinite tail. This
proves root-A4 failure for any full reduction containing those moves.
An SMTree instance of the restricted parity monoid is not claimed.
-/

namespace SuccessorTree.Block
namespace ParityFat

structure OddMarkedWord where
  block : Nat → List (Option Bool)
  odd : ∀ i, varCount (block i) % 2 = 1

def firstColour (U : OddMarkedWord) : Nat :=
  varCount (U.block 0) % 4

def ChoiceFour (v w0 w1 w2 w3 : List (Option Bool)) : Prop :=
  v = grouped12 w0 w1 w2 w3 ∨
  v = grouped13 w0 w1 w2 w3 ∨
  v = grouped23 w0 w1 w2 w3

def FourBlockReduces (V U : OddMarkedWord) : Prop :=
  ChoiceFour (V.block 0) (U.block 0) (U.block 1) (U.block 2) (U.block 3) ∧
  ∀ i, V.block (i+1) = U.block (i+4)

theorem firstColour_flip (U : OddMarkedWord) :
    ∃ V : OddMarkedWord,
      FourBlockReduces V U ∧ firstColour V ≠ firstColour U := by
  have h0 := U.odd 0
  have h1 := U.odd 1
  have h2 := U.odd 2
  have h3 := U.odd 3
  rcases equal_residue_among_three_odds
      (varCount (U.block 1)) (varCount (U.block 2))
      (varCount (U.block 3)) h1 h2 h3 with h12 | h13 | h23
  · let g := grouped12 (U.block 0) (U.block 1) (U.block 2) (U.block 3)
    have hgodd : varCount g % 2 = 1 := by
      dsimp [g]; rw [grouped12_vars]; omega
    let V : OddMarkedWord := {
      block := fun i => if i=0 then g else U.block (i+3)
      odd := by
        intro i
        by_cases hi : i=0
        · simp [hi, hgodd]
        · simpa [hi] using U.odd (i+3)
    }
    refine ⟨V, ?_, ?_⟩
    · constructor
      · exact Or.inl (by simp [V, g])
      · intro i
        simp [V, Nat.add_assoc]
    · dsimp [firstColour, V]
      simp
      dsimp [g]
      rw [grouped12_vars]
      exact same_odd_pair_flips _ _ _ h1 h2 h12
  · let g := grouped13 (U.block 0) (U.block 1) (U.block 2) (U.block 3)
    have hgodd : varCount g % 2 = 1 := by
      dsimp [g]; rw [grouped13_vars]; omega
    let V : OddMarkedWord := {
      block := fun i => if i=0 then g else U.block (i+3)
      odd := by
        intro i
        by_cases hi : i=0
        · simp [hi, hgodd]
        · simpa [hi] using U.odd (i+3)
    }
    refine ⟨V, ?_, ?_⟩
    · constructor
      · exact Or.inr (Or.inl (by simp [V, g]))
      · intro i
        simp [V, Nat.add_assoc]
    · dsimp [firstColour, V]
      simp
      dsimp [g]
      rw [grouped13_vars]
      exact same_odd_pair_flips _ _ _ h1 h3 h13
  · let g := grouped23 (U.block 0) (U.block 1) (U.block 2) (U.block 3)
    have hgodd : varCount g % 2 = 1 := by
      dsimp [g]; rw [grouped23_vars]; omega
    let V : OddMarkedWord := {
      block := fun i => if i=0 then g else U.block (i+3)
      odd := by
        intro i
        by_cases hi : i=0
        · simp [hi, hgodd]
        · simpa [hi] using U.odd (i+3)
    }
    refine ⟨V, ?_, ?_⟩
    · constructor
      · exact Or.inr (Or.inr (by simp [V, g]))
      · intro i
        simp [V, Nat.add_assoc]
    · dsimp [firstColour, V]
      simp
      dsimp [g]
      rw [grouped23_vars]
      exact same_odd_pair_flips _ _ _ h2 h3 h23

/-- The root A4 pigeonhole assertion for a reduction relation R. -/
def A4Root (R : OddMarkedWord → OddMarkedWord → Prop) : Prop :=
  ∀ U, ∃ V, R V U ∧
    ∀ W, R W V → firstColour W = firstColour V

theorem no_A4Root_of_fourBlockReduces
    (R : OddMarkedWord → OddMarkedWord → Prop)
    (hR : ∀ V U, FourBlockReduces V U → R V U) :
    ¬ A4Root R := by
  intro hA4
  let seed : OddMarkedWord := {
    block := fun _ => [none]
    odd := by intro i; decide
  }
  obtain ⟨V, _, hHom⟩ := hA4 seed
  obtain ⟨W, hWV, hColour⟩ := firstColour_flip V
  exact hColour (hHom W (hR W V hWV))

end ParityFat
end SuccessorTree.Block

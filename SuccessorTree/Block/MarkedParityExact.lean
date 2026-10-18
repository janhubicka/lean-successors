import SuccessorTree.Block.BranchFirstParityObstruction

/-!
# Mod-four parity obstruction survives freely movable marked cuts

A cut between the last appearance of variable x_i and the first of
x_(i+1) may split the constant suffix/prefix. Therefore individual
marked blocks need NOT have even constant-one parity. This module
proves the correct four-block obstruction using ONLY the invariant
that each marked block contains an odd number of variable symbols.

The selector itself has three live variable positions and only one
frozen constant 0. It is a legal parity-selector (odd variable
multiplicity, zero constant ones). Composing this selector with a
member of the parity monoid is allowed by monoid closure; that
infinitary monoid instance and the tail-splice are not in this file.
-/

namespace SuccessorTree.Block
namespace ParityFat

def selector12 : List (Option Bool) :=
  [none, none, none, some false]
def selector13 : List (Option Bool) :=
  [none, none, some false, none]
def selector23 : List (Option Bool) :=
  [none, some false, none, none]

theorem selector12_allowed : AllowedParity selector12 := by decide
theorem selector13_allowed : AllowedParity selector13 := by decide
theorem selector23_allowed : AllowedParity selector23 := by decide

/-- The selected 4-block word is obtained by substituting the
selector symbols into the original consecutive marked blocks. -/
def selectorValue (w0 w1 w2 w3 : List (Option Bool))
    (sel : List (Option Bool)) : List (Option Bool) :=
  match sel with
  | [s0,s1,s2,s3] =>
      (fun w s => if s == none then w else frozenZero w) w0 s0 ++
      (fun w s => if s == none then w else frozenZero w) w1 s1 ++
      (fun w s => if s == none then w else frozenZero w) w2 s2 ++
      (fun w s => if s == none then w else frozenZero w) w3 s3
  | _ => []

theorem selector12_value (w0 w1 w2 w3 : List (Option Bool)) :
    selectorValue w0 w1 w2 w3 selector12 =
      grouped12 w0 w1 w2 w3 := by
  simp [selectorValue, selector12, grouped12]

theorem selector13_value (w0 w1 w2 w3 : List (Option Bool)) :
    selectorValue w0 w1 w2 w3 selector13 =
      grouped13 w0 w1 w2 w3 := by
  simp [selectorValue, selector13, grouped13]

theorem selector23_value (w0 w1 w2 w3 : List (Option Bool)) :
    selectorValue w0 w1 w2 w3 selector23 =
      grouped23 w0 w1 w2 w3 := by
  simp [selectorValue, selector23, grouped23]

/-- Arbitrary redistribution of constants between complete marked
blocks is harmless. The four-block flip uses no parity hypothesis on
the constants of the individual blocks. The selector is explicitly
one of the three globally admissible parity-selector words. -/
theorem four_marked_blocks_flip
    (w0 w1 w2 w3 : List (Option Bool))
    (h0 : varCount w0 % 2 = 1)
    (h1 : varCount w1 % 2 = 1)
    (h2 : varCount w2 % 2 = 1)
    (h3 : varCount w3 % 2 = 1) :
    ∃ (sel : List (Option Bool)) (v : List (Option Bool)),
      AllowedParity sel ∧
      v = selectorValue w0 w1 w2 w3 sel ∧
      varCount v % 2 = 1 ∧
      (∀ a : Bool, evaluate v a ∈ span4 w0 w1 w2 w3) ∧
      varCount v % 4 ≠ varCount w0 % 4 := by
  rcases equal_residue_among_three_odds
      (varCount w1) (varCount w2) (varCount w3)
      h1 h2 h3 with heq | heq | heq
  · refine ⟨selector12, grouped12 w0 w1 w2 w3,
        selector12_allowed, (selector12_value ..).symm, ?_, ?_, ?_⟩
    · rw [grouped12_vars]; omega
    · exact grouped12_span w0 w1 w2 w3
    · rw [grouped12_vars]
      exact same_odd_pair_flips _ _ _ h1 h2 heq
  · refine ⟨selector13, grouped13 w0 w1 w2 w3,
        selector13_allowed, (selector13_value ..).symm, ?_, ?_, ?_⟩
    · rw [grouped13_vars]; omega
    · exact grouped13_span w0 w1 w2 w3
    · rw [grouped13_vars]
      exact same_odd_pair_flips _ _ _ h1 h3 heq
  · refine ⟨selector23, grouped23 w0 w1 w2 w3,
        selector23_allowed, (selector23_value ..).symm, ?_, ?_, ?_⟩
    · rw [grouped23_vars]; omega
    · exact grouped23_span w0 w1 w2 w3
    · rw [grouped23_vars]
      exact same_odd_pair_flips _ _ _ h2 h3 heq

end ParityFat
end SuccessorTree.Block

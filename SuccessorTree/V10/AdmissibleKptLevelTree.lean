import SuccessorTree.V10.AdmissibleKptMeet
import SuccessorTree.Tree
import Mathlib.Tactic

/-!
# LevelTree on the normalized forbidden-free Kpt partial-type family

Every field of the paper's LevelTree interface is now derived from
the concrete admissible representation:

* levels are the number of vertices in the initial socle;
* a strict prefix raises the level;
* an immediate cover adds precisely one socle vertex;
* prefixes below a common type are linearly ordered;
* every lower level has an admissible ancestor;
* each level is finite because a complete finite L+ record is a
  finite Boolean table;
* two admissible nodes with a common predecessor have the greatest
  common admissible prefix.

The crucial age closure and meet membership are supplied by the
proved one-neutral-filler replica, not postulated as an abstract
subtree property. This establishes the Kpt tree/forest component
for the explicit normalized finite unary/binary presentation,
subject to the common treatment of nullary symbols.

It is NOT yet the manuscript's full Proposition 6.32: the exact
partial-type successor operation S and its unique decomposition,
nor the monoid M and M1-M3, are part of the next milestone.
-/

namespace SuccessorTree.V10

/-- Strict order in the admissible Kpt subtype is strict order of
the corresponding raw L+ records. -/
theorem admissibleKpt_level_lt_of_lt
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {a b : AdmissibleKptNode family}
    (hab : a < b) :
    a.1.1 < b.1.1 := by
  have hraw : a.1 < b.1 := hab
  exact rawPartialType_level_lt_of_lt hraw

/-- There is no skipped level in a cover of admissible Kpt nodes.
The intermediate raw prefix is admissible by the one-filler
prefix-closure theorem, hence also an intermediate Kpt node. -/
theorem admissibleKpt_covBy_level
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {a b : AdmissibleKptNode family}
    (hab : a ⋖ b) :
    b.1.1 = a.1.1 + 1 := by
  have hlt : a.1.1 < b.1.1 :=
    admissibleKpt_level_lt_of_lt hab.lt
  by_contra hne
  have hgap : a.1.1 + 1 < b.1.1 := by omega
  let z := admissibleKptAncestor b (a.1.1 + 1) (by omega)
  have hzb : z ≤ b :=
    admissibleKptAncestor_le b (a.1.1 + 1) (by omega)
  have haz : a ≤ z := by
    rcases rawPartialType_lower_linear
        (show a.1 ≤ b.1 from hab.le)
        (show z.1 ≤ b.1 from hzb) with h | h
    · exact h
    · have hlevels := rawPartialTypePrefix_level_le h
      change a.1.1 + 1 ≤ a.1.1 at hlevels
      omega
  have hazStrict : a < z := by
    refine lt_of_le_of_ne haz ?_
    intro heq
    have hlevel := congrArg
      (fun x : AdmissibleKptNode family => x.1.1) heq
    change a.1.1 = a.1.1 + 1 at hlevel
    omega
  have hzbStrict : z < b := by
    refine lt_of_le_of_ne hzb ?_
    intro heq
    have hlevel := congrArg
      (fun x : AdmissibleKptNode family => x.1.1) heq
    change a.1.1 + 1 = b.1.1 at hlevel
    omega
  exact (not_covBy_of_lt_of_lt hazStrict hzbStrict) hab

/-- The normalized forbidden-free finite partial-type subforest
has an honest LevelTree instance, with ALL axioms proved from the
literal induced prefix relation and forbidden-age preservation.
No extra abstract Kpt axioms or unproved meet axioms are added. -/
noncomputable instance instAdmissibleKptLevelTree
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    LevelTree (AdmissibleKptNode family) where
  level := fun a => a.1.1
  level_lt := admissibleKpt_level_lt_of_lt
  covBy_level := admissibleKpt_covBy_level
  lower_linear := by
    intro a b c hac hbc
    exact rawPartialType_lower_linear
      (show a.1 ≤ c.1 from hac)
      (show b.1 ≤ c.1 from hbc)
  ancestor_exists := by
    intro a n hn
    exact admissibleKpt_ancestor_exists a n hn
  level_finite := admissibleRawTypeLevel_finite family
  meet := admissibleKptMeet
  meet_le_left := by
    intro a b hcommon
    exact (admissibleKptMeet_spec a b hcommon).1
  meet_le_right := by
    intro a b hcommon
    exact (admissibleKptMeet_spec a b hcommon).2.1
  le_meet := by
    intro a b c hca hcb
    exact (admissibleKptMeet_spec a b ⟨c, hca, hcb⟩).2.2 c hca hcb

/-- The abstract LevelTree meet is exactly the admitted induced
prefix meet, not an additional choice with unproved properties. -/
theorem admissibleKpt_levelTree_meet_eq
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (a b : AdmissibleKptNode family) :
    LevelTree.meet a b = admissibleKptMeet a b := rfl

/-- An abstract Kpt ancestor at a lower level equals the literal
induced L+ restriction, using the already-checked prefix closure. -/
theorem admissibleKpt_levelTree_ancestor_eq
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (a : AdmissibleKptNode family)
    (n : Nat) (hn : n ≤ LevelTree.lev a) :
    LevelTree.ancestor a n hn =
      admissibleKptAncestor a n (by exact hn) := by
  have hraw : n ≤ a.1.1 := hn
  have hancestor :
      admissibleKptAncestor a n hraw ≤ a :=
    admissibleKptAncestor_le a n hraw
  have hlevel : LevelTree.lev
      (admissibleKptAncestor a n hraw) = n := rfl
  exact (LevelTree.eq_ancestor_of_le hancestor hlevel hn).symm

end SuccessorTree.V10

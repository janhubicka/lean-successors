import SuccessorTree.V10.RawMeetLevel
import Mathlib.Tactic

/-!
# The actual prefix partial order of finite complete L+ types

The nodes are dependent pairs of their cut and all induced L+ bits.
Initial-socle restrictions compose and preserve identity; therefore
the raw prefix relation is a genuine partial order, not merely a
surrogate comparison of traces.

We verify the underlying tree geometry used by the paper: any two
prefixes of a common type are comparable, and every smaller level
has a unique predecessor. Level finiteness, meets for all pairs with
a common root, and the forbidden-free Kpt subforest will be added
in separate, independently audited modules.
-/

namespace SuccessorTree.V10

/-- Cutting a complete finite L+ record at its existing cut changes
nothing. The proof checks the L and E components, not just a code. -/
theorem PartialTypeWithE.restrict_self
    {n db du dd : Nat}
    (T : PartialTypeWithE n db du dd)
    (h : n ≤ n) :
    T.restrict h = T := by
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      cases a <;> cases b <;> rfl
    · intro a r
      cases a <;> rfl
    · intro a r
      cases a <;> rfl
  · intro a b
    cases a <;> cases b <;> rfl

/-- Two consecutive restrictions equal their composite restriction,
including every binary/unary/diagonal L-atom and auxiliary E-atom. -/
theorem PartialTypeWithE.restrict_trans
    {a b c db du dd : Nat}
    (T : PartialTypeWithE c db du dd)
    (hab : a ≤ b) (hbc : b ≤ c) :
    (T.restrict hbc).restrict hab =
      T.restrict (hab.trans hbc) := by
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y r
      cases x <;> cases y <;> rfl
    · intro x r
      cases x <;> rfl
    · intro x r
      cases x <;> rfl
  · intro x y
    cases x <;> cases y <;> rfl

theorem rawPartialTypePrefix_refl
    {db du dd : Nat}
    (a : RawPartialTypeNode db du dd) :
    RawPartialTypePrefix a a := by
  refine ⟨le_rfl, ?_⟩
  exact (PartialTypeWithE.restrict_self a.2 le_rfl).symm

theorem rawPartialTypePrefix_trans
    {db du dd : Nat}
    {a b c : RawPartialTypeNode db du dd}
    (hab : RawPartialTypePrefix a b)
    (hbc : RawPartialTypePrefix b c) :
    RawPartialTypePrefix a c := by
  obtain ⟨habLev, habEq⟩ := hab
  obtain ⟨hbcLev, hbcEq⟩ := hbc
  refine ⟨habLev.trans hbcLev, ?_⟩
  calc
    a.2 = b.2.restrict habLev := habEq
    _ = (c.2.restrict hbcLev).restrict habLev := by
        rw [hbcEq]
    _ = c.2.restrict (habLev.trans hbcLev) :=
        PartialTypeWithE.restrict_trans c.2 habLev hbcLev

theorem rawPartialTypePrefix_antisymm
    {db du dd : Nat}
    {a b : RawPartialTypeNode db du dd}
    (hab : RawPartialTypePrefix a b)
    (hba : RawPartialTypePrefix b a) :
    a = b := by
  obtain ⟨habLev, habEq⟩ := hab
  obtain ⟨hbaLev, _⟩ := hba
  rcases a with ⟨n, ta⟩
  rcases b with ⟨m, tb⟩
  dsimp at habLev hbaLev habEq
  have hLevel : n = m := Nat.le_antisymm habLev hbaLev
  subst m
  have hRecord : ta = tb := by
    simpa only [PartialTypeWithE.restrict_self] using habEq
  subst tb
  rfl

/-- The exact raw full-type prefix relation is a partial order. -/
instance rawPartialTypePartialOrder
    (db du dd : Nat) :
    PartialOrder (RawPartialTypeNode db du dd) where
  le := RawPartialTypePrefix
  le_refl := rawPartialTypePrefix_refl
  le_trans := fun _ _ _ hab hbc => rawPartialTypePrefix_trans hab hbc
  le_antisymm := fun _ _ hab hba => rawPartialTypePrefix_antisymm hab hba

/-- Levels never decrease along an actual complete L+ prefix. -/
theorem rawPartialTypePrefix_level_le
    {db du dd : Nat}
    {a b : RawPartialTypeNode db du dd}
    (hab : a ≤ b) :
    a.1 ≤ b.1 := hab.1

/-- At a fixed cut, a partial-type prefix is unique. -/
theorem rawPartialTypePrefix_eq_of_same_level
    {db du dd : Nat}
    {a b : RawPartialTypeNode db du dd}
    (hab : a ≤ b) (hcut : a.1 = b.1) :
    a = b := by
  obtain ⟨hl, heq⟩ := hab
  rcases a with ⟨n, ta⟩
  rcases b with ⟨m, tb⟩
  dsimp at hl heq hcut
  subst m
  have hT : ta = tb := by
    simpa only [PartialTypeWithE.restrict_self] using heq
  subst tb
  rfl

/-- The canonical predecessor at any smaller socle cut. -/
def rawPartialTypeAncestor
    {db du dd : Nat}
    (a : RawPartialTypeNode db du dd)
    (n : Nat) (hn : n ≤ a.1) : RawPartialTypeNode db du dd :=
  ⟨n, a.2.restrict hn⟩

theorem rawPartialTypeAncestor_le
    {db du dd : Nat}
    (a : RawPartialTypeNode db du dd)
    (n : Nat) (hn : n ≤ a.1) :
    rawPartialTypeAncestor a n hn ≤ a := by
  exact ⟨hn, rfl⟩

/-- Two raw prefixes below a common full type are linearly ordered.
This is the literal forest property for complete records. -/
theorem rawPartialType_lower_linear
    {db du dd : Nat}
    {a b c : RawPartialTypeNode db du dd}
    (hac : a ≤ c) (hbc : b ≤ c) :
    a ≤ b ∨ b ≤ a := by
  obtain ⟨hacLev, hacEq⟩ := hac
  obtain ⟨hbcLev, hbcEq⟩ := hbc
  rcases le_total a.1 b.1 with habLev | hbaLev
  · left
    refine ⟨habLev, ?_⟩
    calc
      a.2 = c.2.restrict hacLev := hacEq
      _ = c.2.restrict (habLev.trans hbcLev) := rfl
      _ = (c.2.restrict hbcLev).restrict habLev :=
        (PartialTypeWithE.restrict_trans c.2 habLev hbcLev).symm
      _ = b.2.restrict habLev := by rw [←hbcEq]
  · right
    refine ⟨hbaLev, ?_⟩
    calc
      b.2 = c.2.restrict hbcLev := hbcEq
      _ = c.2.restrict (hbaLev.trans hacLev) := rfl
      _ = (c.2.restrict hacLev).restrict hbaLev :=
        (PartialTypeWithE.restrict_trans c.2 hbaLev hacLev).symm
      _ = a.2.restrict hbaLev := by rw [←hacEq]

/-- Every lower level has a predecessor, which is unique by the
same-level prefix lemma. The full LevelTree instance additionally
needs finite levels and greatest common predecessors. -/
theorem rawPartialType_ancestor_exists
    {db du dd : Nat}
    (a : RawPartialTypeNode db du dd)
    (n : Nat) (hn : n ≤ a.1) :
    ∃ b : RawPartialTypeNode db du dd,
      b ≤ a ∧ b.1 = n :=
  ⟨rawPartialTypeAncestor a n hn,
    rawPartialTypeAncestor_le a n hn, rfl⟩

end SuccessorTree.V10

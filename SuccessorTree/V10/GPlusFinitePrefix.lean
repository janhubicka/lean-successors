import SuccessorTree.V10.GPlusFiniteCode
import Mathlib.Tactic

/-!
# Finite-coordinate prefix tree for Definition 6.40's G+

G+ is the tree of finite enumerated L+ partial structures
under initial-segment restriction, NOT the raw type of functions
on Nat with arbitrary off-carrier Boolean values.

This file introduces restriction of a finite atomic code to an
earlier length and its induced prefix relation. Restriction
retains every directed binary, unary, diagonal and E bit of
the initial segment. Iterated restriction agrees with one
direct restriction; consequently prefix is transitive.
Two codes with the same length that are prefixes of one
common larger code are equal.

These are the canonical combinatorial facts underlying the
tree order on the countable G+ vertex set. Subsequent files
must prove prefix restriction preserves admissibility and
define the original relational tuples of G+ by the larger
node's two-last-coordinate pattern.
-/

namespace SuccessorTree.V10

/-- Exact finite induced restriction, with the same underlying
atomic values on the first n coordinates and no new E atoms. -/
def FinitePartialCode.restrict
    {db du dd : Nat}
    (C : FinitePartialCode db du dd)
    (n : Nat) (hn : n ≤ C.size) :
    FinitePartialCode db du dd where
  size := n
  binary := fun i j a =>
    C.binary ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
      ⟨j.val, lt_of_lt_of_le j.isLt hn⟩ a
  unary := fun i a =>
    C.unary ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ a
  diagonal := fun i a =>
    C.diagonal ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ a
  eRelation := fun i j =>
    C.eRelation ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
      ⟨j.val, lt_of_lt_of_le j.isLt hn⟩

@[simp] theorem FinitePartialCode.restrict_size
    {db du dd : Nat}
    (C : FinitePartialCode db du dd)
    (n : Nat) (hn : n ≤ C.size) :
    (C.restrict n hn).size = n := rfl

/-- The original code is its own full-length prefix. -/
theorem FinitePartialCode.restrict_self
    {db du dd : Nat}
    (C : FinitePartialCode db du dd) :
    C.restrict C.size le_rfl = C := by
  cases C
  rfl

/-- Restricting first to n, then to m≤n, is the same as
restricting immediately to m. This uses proof irrelevance for
the bounds, not any quotient on the relation data. -/
theorem FinitePartialCode.restrict_restrict
    {db du dd : Nat}
    (C : FinitePartialCode db du dd)
    (m n : Nat) (hmn : m ≤ n) (hn : n ≤ C.size) :
    (C.restrict n hn).restrict m hmn =
      C.restrict m (hmn.trans hn) := by
  cases C
  rfl

/-- Restriction respects equality of complete codes, with
proof irrelevance taking care of the dependent length witnesses. -/
private theorem FinitePartialCode.restrict_congr
    {db du dd : Nat}
    {A B : FinitePartialCode db du dd}
    (h : A = B) (n : Nat)
    (ha : n ≤ A.size) (hb : n ≤ B.size) :
    A.restrict n ha = B.restrict n hb := by
  cases h
  rfl

/-- Restriction at provably equal lengths has equal finite tables. -/
private theorem FinitePartialCode.restrict_eq_of_length_eq
    {db du dd : Nat}
    (C : FinitePartialCode db du dd)
    {n m : Nat} (h : n = m)
    (hn : n ≤ C.size) (hm : m ≤ C.size) :
    C.restrict n hn = C.restrict m hm := by
  subst m
  rfl

/-- The canonical initial-segment order on finite partial
codes used for the countable vertex tree of G+. -/
def FinitePartialCode.IsPrefix
    {db du dd : Nat}
    (A B : FinitePartialCode db du dd) : Prop :=
  ∃ h : A.size ≤ B.size, A = B.restrict A.size h

theorem FinitePartialCode.isPrefix_refl
    {db du dd : Nat}
    (A : FinitePartialCode db du dd) :
    A.IsPrefix A :=
  ⟨le_rfl,A.restrict_self.symm⟩

theorem FinitePartialCode.isPrefix_trans
    {db du dd : Nat}
    {A B C : FinitePartialCode db du dd}
    (hAB : A.IsPrefix B)
    (hBC : B.IsPrefix C) : A.IsPrefix C := by
  rcases hAB with ⟨hAB,hA⟩
  rcases hBC with ⟨hBC,hB⟩
  refine ⟨hAB.trans hBC,?_⟩
  have hCong :
      B.restrict A.size hAB =
        (C.restrict B.size hBC).restrict A.size hAB :=
    FinitePartialCode.restrict_congr hB A.size hAB hAB
  calc
    A = B.restrict A.size hAB := hA
    _ = (C.restrict B.size hBC).restrict A.size hAB := hCong
    _ = C.restrict A.size (hAB.trans hBC) :=
      C.restrict_restrict A.size B.size hAB hBC

/-- Equal-length prefixes of one vertex coincide. Thus distinct
nodes of one length cannot both occur on a branch of G+. -/
theorem FinitePartialCode.prefix_unique_at_size
    {db du dd : Nat}
    {A B C : FinitePartialCode db du dd}
    (hA : A.IsPrefix C) (hB : B.IsPrefix C)
    (hSize : A.size = B.size) : A = B := by
  rcases hA with ⟨ha,hAC⟩
  rcases hB with ⟨hb,hBC⟩
  exact hAC.trans
    ((C.restrict_eq_of_length_eq hSize ha hb).trans hBC.symm)

/-- Distinct sizes force different finite codes; prefix maps
with strictly increasing size are automatically injective. -/
theorem FinitePartialCode.ne_of_size_ne
    {db du dd : Nat}
    (A B : FinitePartialCode db du dd)
    (h : A.size ≠ B.size) : A ≠ B := by
  intro heq
  exact h (congrArg FinitePartialCode.size heq)

/-- Prefixes are linearly ordered under a common top code:
the shorter one is a prefix of the longer. -/
theorem FinitePartialCode.prefixes_comparable
    {db du dd : Nat}
    {A B C : FinitePartialCode db du dd}
    (hA : A.IsPrefix C) (hB : B.IsPrefix C) :
    A.IsPrefix B ∨ B.IsPrefix A := by
  rcases hA with ⟨ha,hAC⟩
  rcases hB with ⟨hb,hBC⟩
  rcases le_total A.size B.size with hab | hba
  · left
    refine ⟨hab,?_⟩
    have hCong :
        B.restrict A.size hab =
          (C.restrict B.size hb).restrict A.size hab :=
      FinitePartialCode.restrict_congr hBC A.size hab hab
    calc
      A = C.restrict A.size ha := hAC
      _ = C.restrict A.size (hab.trans hb) := rfl
      _ = (C.restrict B.size hb).restrict A.size hab :=
        (C.restrict_restrict A.size B.size hab hb).symm
      _ = B.restrict A.size hab := hCong.symm
  · right
    refine ⟨hba,?_⟩
    have hCong :
        A.restrict B.size hba =
          (C.restrict A.size ha).restrict B.size hba :=
      FinitePartialCode.restrict_congr hAC B.size hba hba
    calc
      B = C.restrict B.size hb := hBC
      _ = C.restrict B.size (hba.trans ha) := rfl
      _ = (C.restrict A.size ha).restrict B.size hba :=
        (C.restrict_restrict B.size A.size hba ha).symm
      _ = A.restrict B.size hba := hCong.symm

end SuccessorTree.V10
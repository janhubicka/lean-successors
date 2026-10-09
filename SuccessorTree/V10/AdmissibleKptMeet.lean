import SuccessorTree.V10.RawPartialTypeLevelTree
import SuccessorTree.V10.AdmissibleKptPrefix
import Mathlib.Tactic

/-!
# Admissible Kpt predecessors and their actual common meets

The raw partial-type forest has a complete LevelTree instance, but
arbitrary raw L+ records need not arise from forbidden-free partial
structures. This module *does not* identify those two families.

Instead, fix the normalized forbidden family from the preceding
admissible-prefix theorem. Its node type is the subtype of raw records
that are actually represented at a free E cut of a vertex of some
forbidden-free partial structure.

The previously proved one-neutral-filler construction makes that
subtype prefix-closed. As a result each admissible node has every
lower ancestor, and if two admissible nodes have a common predecessor
their RAW greatest common prefix is itself admissible. Therefore
this greatest prefix gives a genuine meet on the admissible family.

When nodes lie in different root components, the total meet returns
its first argument. No meet axiom is claimed in that case. The
nonempty-fallback issue does not introduce any new assumption.
-/

namespace SuccessorTree.V10

/-- Nodes of the normalized forbidden-free finite Kpt subforest. -/
abbrev AdmissibleKptNode
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :=
  {N : RawPartialTypeNode db du dd //
    IsAdmissibleRawType family N}

/-- Prefixes of any admissible type are again admissible, including
arbitrary raw prefixes, not merely its chosen original's ancestors. -/
theorem admissibleRawType_of_prefix
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {a b : RawPartialTypeNode db du dd}
    (hb : IsAdmissibleRawType family b)
    (hab : a ≤ b) :
    IsAdmissibleRawType family a := by
  obtain ⟨hcut, hEq⟩ := hab
  have hClosed := admissibleRawType_closed_under_prefix
    family hb a.1 hcut
  rcases a with ⟨n, T⟩
  change T = b.2.restrict hcut at hEq
  change IsAdmissibleRawType family
    (⟨n, T⟩ : RawPartialTypeNode db du dd)
  rw [hEq]
  exact hClosed

/-- The exact ancestor of an admissible node is an admissible
restriction of its complete L+ record. -/
def admissibleKptAncestor
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (a : AdmissibleKptNode family)
    (n : Nat) (hn : n ≤ a.1.1) :
    AdmissibleKptNode family :=
  ⟨rawPartialTypeAncestor a.1 n hn,
    admissibleRawType_closed_under_prefix family a.2 n hn⟩

theorem admissibleKptAncestor_le
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (a : AdmissibleKptNode family)
    (n : Nat) (hn : n ≤ a.1.1) :
    admissibleKptAncestor a n hn ≤ a :=
  rawPartialTypeAncestor_le a.1 n hn

/-- A common admissible predecessor is a common RAW predecessor.
We use no converse: the raw meet must be shown admissible separately. -/
theorem admissible_common_implies_raw_common
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (a b : AdmissibleKptNode family)
    (h : ∃ c : AdmissibleKptNode family, c ≤ a ∧ c ≤ b) :
    ∃ c : RawPartialTypeNode db du dd, c ≤ a.1 ∧ c ≤ b.1 := by
  obtain ⟨c, hca, hcb⟩ := h
  exact ⟨c.1, hca, hcb⟩

/-- A total greatest-common-predecessor operation on the admissible
Kpt subtype, using the RAW meet and proved closure under prefixes.
No default admissible root or global nonemptiness assumption is
needed: the disjoint-component case simply returns a itself. -/
noncomputable def admissibleKptMeet
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (a b : AdmissibleKptNode family) :
    AdmissibleKptNode family :=
  if h : ∃ c : AdmissibleKptNode family, c ≤ a ∧ c ≤ b then
    ⟨rawMeet a.1 b.1,
      admissibleRawType_of_prefix family a.2
        (rawMeet_le_left a.1 b.1
          (admissible_common_implies_raw_common a b h))⟩
  else a

/-- The raw meet of two admissible nodes with a common predecessor
is in the admissible family. Both lower-bound and greatest-bound
properties follow from the raw meet proofs, now without a
representation interface left as a hypothesis. -/
theorem admissibleKptMeet_spec
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (a b : AdmissibleKptNode family)
    (h : ∃ c : AdmissibleKptNode family, c ≤ a ∧ c ≤ b) :
    admissibleKptMeet a b ≤ a ∧
    admissibleKptMeet a b ≤ b ∧
    (∀ c : AdmissibleKptNode family,
      c ≤ a → c ≤ b → c ≤ admissibleKptMeet a b) := by
  classical
  have hRaw := admissible_common_implies_raw_common a b h
  unfold admissibleKptMeet
  rw [dif_pos h]
  refine ⟨rawMeet_le_left a.1 b.1 hRaw,
    rawMeet_le_right a.1 b.1 hRaw, ?_⟩
  intro c hca hcb
  exact raw_le_meet hca hcb

/-- Every finite admissible Kpt node has a same-branch ancestor
at every smaller level, with that original cut. -/
theorem admissibleKpt_ancestor_exists
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (a : AdmissibleKptNode family)
    (n : Nat) (hn : n ≤ a.1.1) :
    ∃ b : AdmissibleKptNode family,
      b ≤ a ∧ b.1.1 = n :=
  ⟨admissibleKptAncestor a n hn,
    admissibleKptAncestor_le a n hn, rfl⟩

end SuccessorTree.V10

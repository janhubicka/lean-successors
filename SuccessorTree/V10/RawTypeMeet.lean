import SuccessorTree.V10.FirstFullPrefix

/-!
# Actual greatest common prefixes of finite partial L+ types

This module removes the next abstract meet-interface assumption in the
v10 proof. For a fixed finite unary/binary signature, a node is a
dependent pair (cut, complete L+ type at that cut); the literal
initial-socle prefix relation retains every E and L atomic bit.

For two genuine types extracted from the SAME ambient partial
structure A, with their actual E free levels as cuts, we construct a
greatest common predecessor whenever their root types agree. The
maximal prefix is proved in the full dependent type of finite L+
records, not in a surrogate binary trace and not by assuming a
LevelTree meet operation.

The remaining paper-specific step is to identify the forbidden-free
Kpt membership predicate and order with this raw prefix relation,
and to show that the maximal prefix is itself a Kpt member.
This is deliberately not hidden in an instance declaration.
-/

namespace SuccessorTree.V10

/-- A complete finite partial-type record with its socle length. -/
abbrev RawPartialTypeNode (db du dd : Nat) :=
  Σ cut : Nat, PartialTypeWithE cut db du dd

/-- The exact initial-socle restriction relation on complete types. -/
def RawPartialTypePrefix {db du dd : Nat}
    (a b : RawPartialTypeNode db du dd) : Prop :=
  ∃ h : a.1 ≤ b.1, a.2 = b.2.restrict h

/-- The actual extracted partial type of a vertex, at its unique
free level determined by its E-socle. -/
noncomputable def EnumeratedPartialStructure.rawTypeAtFree
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (v : Nat) : RawPartialTypeNode db du dd :=
  ⟨A.freeLevel v, A.partialTypeAt (A.freeLevel v) v⟩

/-- A shorter induced partial type is a literal prefix of its full
partial type. This includes ALL E, unary and binary atomic facts. -/
theorem rawPartialType_prefix_of_cut
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v d : Nat) (hd : d ≤ A.freeLevel v) :
    RawPartialTypePrefix
      (⟨d, A.partialTypeAt d v⟩ : RawPartialTypeNode db du dd)
      (A.rawTypeAtFree v) := by
  refine ⟨hd, ?_⟩
  exact (A.partialTypeAt_restrict d (A.freeLevel v) v hd).symm

/-- Two actual partial types extracted from one ambient A and having
the same complete root type have a greatest common predecessor in
the RAW full-type prefix order. It is not a hypothetical meet chosen
in an unrelated abstract tree.

This theorem is a universal property: any other common full L+
prefix (whether or not chosen as an extracted type) lies below the
constructed prefix. The complete L+ record includes the E bits. -/
theorem rawPartialTypes_have_greatest_common_prefix
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v w : Nat)
    (hroot : A.partialTypeAt 0 v = A.partialTypeAt 0 w) :
    ∃ m : RawPartialTypeNode db du dd,
      RawPartialTypePrefix m (A.rawTypeAtFree v) ∧
      RawPartialTypePrefix m (A.rawTypeAtFree w) ∧
      (∀ q : RawPartialTypeNode db du dd,
        RawPartialTypePrefix q (A.rawTypeAtFree v) →
        RawPartialTypePrefix q (A.rawTypeAtFree w) →
        RawPartialTypePrefix q m) := by
  let bound := min (A.freeLevel v) (A.freeLevel w)
  obtain ⟨d, hd, hEq, hMax⟩ :=
    exists_maximal_common_fullPrefix A v w bound hroot
  have hdv : d ≤ A.freeLevel v :=
    hd.trans (Nat.min_le_left _ _)
  have hdw : d ≤ A.freeLevel w :=
    hd.trans (Nat.min_le_right _ _)
  let m : RawPartialTypeNode db du dd :=
    ⟨d, A.partialTypeAt d v⟩
  refine ⟨m, ?_, ?_, ?_⟩
  · exact rawPartialType_prefix_of_cut A v d hdv
  · refine ⟨hdw, ?_⟩
    calc
      A.partialTypeAt d v = A.partialTypeAt d w := hEq
      _ = (A.partialTypeAt (A.freeLevel w) w).restrict hdw :=
        (A.partialTypeAt_restrict d (A.freeLevel w) w hdw).symm
  · intro q hqv hqw
    obtain ⟨hqvlev, hqvEq⟩ := hqv
    obtain ⟨hqwlev, hqwEq⟩ := hqw
    have hvAt : q.2 = A.partialTypeAt q.1 v := by
      calc
        q.2 = (A.partialTypeAt (A.freeLevel v) v).restrict hqvlev :=
          hqvEq
        _ = A.partialTypeAt q.1 v :=
          A.partialTypeAt_restrict q.1 (A.freeLevel v) v hqvlev
    have hwAt : q.2 = A.partialTypeAt q.1 w := by
      calc
        q.2 = (A.partialTypeAt (A.freeLevel w) w).restrict hqwlev :=
          hqwEq
        _ = A.partialTypeAt q.1 w :=
          A.partialTypeAt_restrict q.1 (A.freeLevel w) w hqwlev
    have hqEq : A.partialTypeAt q.1 v =
        A.partialTypeAt q.1 w := hvAt.symm.trans hwAt
    have hqbound : q.1 ≤ bound :=
      Nat.le_min.mpr ⟨hqvlev, hqwlev⟩
    have hqd : q.1 ≤ d := by
      by_contra hnot
      have hlarge : d < q.1 := by omega
      rcases hMax with hTop | hDiff
      · omega
      · exact hDiff (fullPartialType_eq_at_smaller A v w
          (d + 1) q.1 (by omega) hqEq)
    refine ⟨hqd, ?_⟩
    calc
      q.2 = A.partialTypeAt q.1 v := hvAt
      _ = (A.partialTypeAt d v).restrict hqd :=
        (A.partialTypeAt_restrict q.1 d v hqd).symm

end SuccessorTree.V10

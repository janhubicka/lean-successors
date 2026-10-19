import SuccessorTree.V10.FiniteTypeProfile
import SuccessorTree.V10.NonedgePaddingSocleCap

/-!
# Neutral representatives of every finite profile front

The neutral singleton admitted by the normalized forbidden presentation gives
an admissible cap over every finite base, including the empty base. Taking its
prefixes shows that no cut of the full profile is empty.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

namespace TypeProfile

/-- The complete neutral cap over the finite ordinary base. -/
noncomputable def cap (A : FiniteTypeBase family) : TypeProfile A :=
  ⟨NonedgePadding.socleCapNode family A.str A.avoids, by
    refine ⟨le_rfl, ?_⟩
    exact ⟨fun i j t => NonedgePadding.twoNeutralL_old_binary A.str
        i.val j.val i.isLt j.isLt t,
      fun i t => NonedgePadding.twoNeutralL_old_unary A.str i.val i.isLt t,
      fun i t => NonedgePadding.twoNeutralL_old_diagonal A.str i.val i.isLt t,
      fun i j => NonedgePadding.socleCap_old_E A.str i.val j.val j.isLt⟩⟩

@[simp] theorem cap_level (A : FiniteTypeBase family) :
    (cap A).level = A.size := rfl

theorem cap_record (A : FiniteTypeBase family) :
    (cap A).1.1.2 =
      (NonedgePadding.socleCap A.str).partialTypeAt A.size (A.size + 1) := rfl

/-- A neutral representative at any cut of the finite base. -/
noncomputable def atCut (A : FiniteTypeBase family)
    (n : Nat) (hn : n ≤ A.size) : TypeProfile A :=
  ⟨admissibleKptAncestor (cap A).1 n hn, by
    refine ⟨hn, ?_⟩
    change SameOrdinaryAtCut ((cap A).1.1.2.restrict hn)
      (A.str.partialTypeAt n 0)
    exact ⟨fun i j t => (cap A).same_socle.1
        ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
        ⟨j.val, lt_of_lt_of_le j.isLt hn⟩ t,
      fun i t => (cap A).same_socle.2.1
        ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ t,
      fun i t => (cap A).same_socle.2.2.1
        ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ t,
      fun i j => (cap A).same_socle.2.2.2
        ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
        ⟨j.val, lt_of_lt_of_le j.isLt hn⟩⟩⟩

@[simp] theorem atCut_level (A : FiniteTypeBase family)
    (n : Nat) (hn : n ≤ A.size) : (atCut A n hn).level = n := rfl

theorem front_nonempty (A : FiniteTypeBase family)
    (n : Nat) (hn : n ≤ A.size) :
    ∃ u : TypeProfile A, u.level = n := ⟨atCut A n hn, rfl⟩

end TypeProfile
end SuccessorTree.V10

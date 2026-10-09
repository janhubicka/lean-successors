import SuccessorTree.V10.OriginalPool
import SuccessorTree.Envelope

/-!
# Original pools for the actual envelope closure

The preceding OriginalPool module proves provenance for an inductively
generated closure and depends only on LevelTree. This module uses the
*actual closure* defined in Section 5 of the manuscript:

  closure S I X = intersection of all meet- and I-parameter-closed
                  supersets of X.

To apply it to v10, it suffices to establish that the downward prefixes
of the maintained pool V are parameter-closed at I. Observation 6.47(3)
is supposed to supply precisely that fact; its concrete H construction
has not yet been identified formally with these abstract premises.
-/

namespace SuccessorTree.V10

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]

/-- The downward closure of any pool of originals is meet-closed in
each tree component. -/
theorem prefixesOf_meetClosed (V : Set T) :
    SMTree.Envelope.MeetClosed (prefixesOf V) := by
  intro a b ha hb hc
  exact meet_mem_prefixesOf ha hb hc

/-- Closure-minimality converts the sole remaining parameter condition
into the original-pool invariant for the *actual* Section 5 closure.
No finitary-generation theorem or stabilization assumption is needed. -/
theorem closure_subset_original_pool
    (S : STree T Label) (I : Set Nat) (X V : Set T)
    (hX : X ⊆ prefixesOf V)
    (hparam : SMTree.Envelope.ParameterClosedOver S (prefixesOf V) I) :
    SMTree.Envelope.closure S I X ⊆ prefixesOf V := by
  exact SMTree.Envelope.closure_minimal S I X (prefixesOf V)
    hX (prefixesOf_meetClosed V) hparam

/-- Every nontrivial meet of two nodes in the actual Section 5 closure
is already a meet of two members of the original pool, once the concrete
parameter-closure premise has been checked. -/
theorem closure_meet_has_originals
    (S : STree T Label) (I : Set Nat) (X V : Set T)
    (hX : X ⊆ prefixesOf V)
    (hparam : SMTree.Envelope.ParameterClosedOver S (prefixesOf V) I)
    {a b : T}
    (ha : a ∈ SMTree.Envelope.closure S I X)
    (hb : b ∈ SMTree.Envelope.closure S I X)
    (hc : ∃ c : T, c ≤ a ∧ c ≤ b)
    (hleft : LevelTree.meet a b ≠ a)
    (hright : LevelTree.meet a b ≠ b) :
    ∃ p ∈ V, ∃ q ∈ V,
      (∃ c : T, c ≤ p ∧ c ≤ q) ∧
      LevelTree.meet a b = LevelTree.meet p q := by
  have hclosure := closure_subset_original_pool S I X V hX hparam
  exact nontrivial_meet_has_originals
    (hclosure ha) (hclosure hb) hc hleft hright

end SuccessorTree.V10

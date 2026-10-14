import SuccessorTree.V10.EmptyParameterS2
import SuccessorTree.V10.AdmissibleKptLevelTree
import SuccessorTree.Successor
import Mathlib.Tactic

/-!
# The exact graph of the proposed successor operation on admissible types

This is the first bridge from the concrete normalized Kpt LevelTree to
the paper's S-tree operation. The letters are temporarily represented
by ALL complete two-vertex L+ types, rather than just the admissible
Sigma alphabet; the final restriction of Sigma requires the concrete
age-preservation argument for extracting the last ordinary vertex.

For a step from a to b, the source is exactly the immediate predecessor
of the latter's complete raw record, its parameter list is EMPTY when
the new vertex's E free cut f is zero and is the unique admissible
shortened type at level f otherwise, and the terminal letter is the
complete induced type on {last ordinary vertex, t}.

All old-new directed binary relations beyond f vanish. This is not a
postulated axiom: for genuine partial structures it follows from E3.

The predicate gives the exact GRAPH of a forward successor, with
existence still to be established from every admissible cover.
We do not yet install STree or assert S2/S3.
-/

namespace SuccessorTree.V10

/-- Explicit full terminal L+ letter; the same Sigma candidates as
in Definition 6.30, before restricting to age-admissible letters. -/
abbrev RawKptLetter (db du dd : Nat) :=
  PartialTypeWithE 1 db du dd

/-- A canonical step is an *admissible* next partial-type record with
the actual old predecessor, an empty-or-singleton free-cut parameter,
the exact terminal Sigma letter and E3 no-new-tuples crossing law. -/
def IsCanonicalKptStep
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (a : AdmissibleKptNode family)
    (p : List (AdmissibleKptNode family))
    (c : RawKptLetter db du dd)
    (b : AdmissibleKptNode family) : Prop :=
  ∃ (ell f : Nat) (hf : f ≤ ell)
    (Q : PartialTypeWithE (ell + 1) db du dd),
      a.1 = (⟨ell, Q.restrict (Nat.le_succ ell)⟩ :
        RawPartialTypeNode db du dd) ∧
      b.1 = (⟨ell + 1, Q⟩ : RawPartialTypeNode db du dd) ∧
      c = Q.terminalLetter ∧
      ValidNewOrdinaryColumn Q f ∧
      p.map (fun x => x.1) =
        (Q.canonicalParameterRecord f hf).toList ∧
      (f = 0 ∨ f < ell)

/-- The exact successor-graph relation has the base as an actual
one-step predecessor of its output. -/
theorem canonicalKptStep_covBy
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : RawKptLetter db du dd}
    (h : IsCanonicalKptStep family a p c b) :
    a ⋖ b := by
  obtain ⟨ell, f, hf, Q, hBase, hTarget, _, _, _, _⟩ := h
  have hraw : a.1 ≤ b.1 := by
    rw [hBase, hTarget]
    exact ⟨Nat.le_succ ell, rfl⟩
  have hlev : LevelTree.lev b = LevelTree.lev a + 1 := by
    change b.1.1 = a.1.1 + 1
    rw [hBase, hTarget]
  exact LevelTree.covBy_of_le_level_succ hraw hlev

/-- A canonical step's parameter list contains only a type at a
strictly lower level than the source, proving the second part of S1. -/
theorem canonicalKptStep_parameter_lt
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : RawKptLetter db du dd}
    (h : IsCanonicalKptStep family a p c b)
    (x : AdmissibleKptNode family) (hx : x ∈ p) :
    LevelTree.lev x < LevelTree.lev a := by
  obtain ⟨ell, f, hf, Q, hBase, _, _, _, hParam, hGate⟩ := h
  have hMem : x.1 ∈ p.map (fun y => y.1) :=
    List.mem_map.mpr ⟨x, hx, rfl⟩
  rw [hParam] at hMem
  by_cases hz : f = 0
  · simp [PartialTypeWithE.canonicalParameterRecord, hz] at hMem
  · have hlt : f < ell := by
      rcases hGate with h | h
      · exact False.elim (hz h)
      · exact h
    have hRecord : x.1 =
        (⟨f, Q.lastOrdinaryParameter f hf⟩ :
          RawPartialTypeNode db du dd) := by
      simpa [PartialTypeWithE.canonicalParameterRecord, hz]
        using hMem
    have hLevel : x.1.1 = f := congrArg Sigma.fst hRecord
    change x.1.1 < a.1.1
    rw [hBase]
    change x.1.1 < ell
    omega

end SuccessorTree.V10

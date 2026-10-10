import SuccessorTree.V10.HDirectedTraces
import Mathlib.Tactic

/-!
# A single finite packet for every directed binary L-atom of a pair

The existing v10 H first-positive-disagreement classifier takes one
finite Boolean vector. For a directed binary language, the complete
ordered pair carries TWO possibly different vectors, not one:
the atoms in order (u,i), and those in order (i,u).

We concatenate these two vectors into Fin (2*d), with explicit
bounded coordinate decoding. The corresponding numerical H packet
agrees exactly with the bundled H trace of the concatenated base
tuple for all legal ordered real pairs.

The first-nonempty-neighbour predicate of this packet therefore
means irreducibility of the base pair in either binary orientation,
rather than an unqualified one-way relation.
-/

namespace SuccessorTree.V10

/-- The complete pair of ordered binary L-atom vectors; index <d is
the forward orientation, and index >=d is the reverse orientation. -/
def bothDirectedAtoms
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (u i : Nat) (t : Fin (2 * d)) : Bool :=
  if h : t.val < d then B u i ⟨t.val, h⟩
  else B i u ⟨t.val - d, by
    have htop := t.isLt
    omega⟩

/-- Both directions of the exact numeric H L-atom tuple packaged
into one vector. The two directions share the same real pair but
use their actual ordered relation values independently. -/
noncomputable def hNumericBoth
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k x y : Nat) (t : Fin (2 * d)) : Bool :=
  if h : t.val < d then
    hNumericBinary B k x y ⟨t.val, h⟩
  else
    hNumericBinary B k y x ⟨t.val - d, by
      have htop := t.isLt
      omega⟩

/-- A numerical H real pair's WHOLE bidirectional L-atom packet is
the bundled trace of the base pair's whole bidirectional packet.
The equality includes all absent tuples and does not assume the
underlying relation symbols are symmetric. -/
theorem hNumericBoth_matches_bundledTrace
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k u i q n : Nat)
    (hui : u < i) (hq : q ≤ k) (hn : n ≤ k) :
    (fun t : Fin (2 * d) =>
      hNumericBoth B k
        (hPosition k u q) (hPosition k i n) t) =
      bundledTrace (bothDirectedAtoms B) k i n u q := by
  funext t
  by_cases ht : t.val < d
  · have hOne := congrFun
      (hNumericBinary_forward_matches_bundledTrace
        B k u i q n hui hq hn) ⟨t.val, ht⟩
    calc
      hNumericBoth B k (hPosition k u q) (hPosition k i n) t =
          hNumericBinary B k (hPosition k u q)
            (hPosition k i n) ⟨t.val, ht⟩ := by
            simp only [hNumericBoth, dif_pos ht]
      _ = bundledTrace B k i n u q ⟨t.val, ht⟩ := hOne
      _ = bundledTrace (bothDirectedAtoms B) k i n u q t := by
        by_cases hg : q < n ∨ (q = n ∧ n = k)
        · simp [bundledTrace, traceBit, hui, hg, bothDirectedAtoms, ht]
        · simp [bundledTrace, traceBit, hui, hg, bothDirectedAtoms, ht]
  · have hvalid : t.val - d < d := by
      have htop := t.isLt
      omega
    have hOne := congrFun
      (hNumericBinary_reverse_matches_bundledTrace
        B k u i q n hui hq hn) ⟨t.val - d, hvalid⟩
    calc
      hNumericBoth B k (hPosition k u q) (hPosition k i n) t =
          hNumericBinary B k (hPosition k i n)
            (hPosition k u q) ⟨t.val - d, hvalid⟩ := by
            simp only [hNumericBoth, dif_neg ht]
      _ = bundledTrace (fun a b r => B b a r)
          k i n u q ⟨t.val - d, hvalid⟩ := hOne
      _ = bundledTrace (bothDirectedAtoms B) k i n u q t := by
        by_cases hg : q < n ∨ (q = n ∧ n = k)
        · simp [bundledTrace, traceBit, hui, hg, bothDirectedAtoms, ht]
        · simp [bundledTrace, traceBit, hui, hg, bothDirectedAtoms, ht]

/-- A complete directed pair has a positive binary atom exactly
when either ordered direction does. This is the finite language's
irreducibility test for a two-vertex substructure. -/
theorem bothDirectedAtoms_nonempty_iff
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (u i : Nat) :
    (∃ t : Fin (2 * d), bothDirectedAtoms B u i t = true) ↔
      (∃ r : Fin d, B u i r = true) ∨
      (∃ r : Fin d, B i u r = true) := by
  constructor
  · rintro ⟨t, ht⟩
    by_cases h : t.val < d
    · left
      refine ⟨⟨t.val, h⟩, ?_⟩
      simpa [bothDirectedAtoms, h] using ht
    · right
      have hvalid : t.val - d < d := by
        have htop := t.isLt
        omega
      refine ⟨⟨t.val - d, hvalid⟩, ?_⟩
      simpa [bothDirectedAtoms, h] using ht
  · rintro (⟨r, hr⟩ | ⟨r, hr⟩)
    · refine ⟨⟨r.val, by omega⟩, ?_⟩
      simpa [bothDirectedAtoms, r.isLt] using hr
    · refine ⟨⟨d + r.val, by omega⟩, ?_⟩
      simpa [bothDirectedAtoms, Nat.not_lt.mpr (Nat.le_add_right d r.val)]
        using hr

end SuccessorTree.V10

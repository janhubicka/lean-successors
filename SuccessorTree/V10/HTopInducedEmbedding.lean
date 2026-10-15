import SuccessorTree.V10.HFinitePartial
import Mathlib.Tactic

/-!
# The top-generation real copy of the base L-structure in numerical H

The v10 manuscript first embeds the given countable enumerated
binary/unary L-structure K into the top generation of its H
construction. For every pair of distinct base indices, the
explicit directed H relation at the corresponding real top
vertices must be exactly the original base relation, in BOTH
tuple orientations. Unary and diagonal symbols must likewise
be copied, and the numerical positions must be strictly
increasing with the base enumeration.

All of this is derived here from the existing exact numerical H
constructor, not from a new abstract embedding hypothesis.
The finite carrier bound is explicit; choosing a large enough
finite N is the only further requirement for a finite prefix.
The countable/universal and G+ transfer is separate.
-/

namespace SuccessorTree.V10

/-- An earlier/later TOP-generation real pair retains exactly
the base binary tuple in the forward direction. -/
theorem hNumericBinary_top_forward_eq
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j : Nat) (r : Fin d) (hij : i < j) :
    hNumericBinary B k (hPosition k i k)
      (hPosition k j k) r = B i j r := by
  have hIff :
      hNumericBinary B k (hPosition k i k)
          (hPosition k j k) r = true ↔
        B i j r = true := by
    constructor
    · intro h
      exact ((hNumericBinary_real_forward_iff
        B k i j k k r hij le_rfl le_rfl).1 h).2
    · intro h
      exact (hNumericBinary_real_forward_iff
        B k i j k k r hij le_rfl le_rfl).2
          ⟨Or.inr ⟨rfl,rfl⟩,h⟩
  cases hb : B i j r with
  | false =>
      cases hh : hNumericBinary B k (hPosition k i k)
        (hPosition k j k) r with
      | false => rfl
      | true =>
          have hImpossible := hIff.mp hh
          simp [hb] at hImpossible
  | true =>
      simpa [hb] using (hIff.mpr hb)

/-- Reverse tuple orientation at two top-generation vertices is
also copied exactly, not reconstructed by symmetry of the base.
Directed binary relations are not assumed symmetric. -/
theorem hNumericBinary_top_reverse_true_iff
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j : Nat) (r : Fin d) (hij : i < j) :
    hNumericBinary B k (hPosition k j k)
      (hPosition k i k) r = true ↔ B j i r = true := by
  rw [hNumericBinary_true_iff]
  constructor
  · rintro ⟨i',j',q',m',hij',hq',hm',_hGate,hDir⟩
    rcases hDir with ⟨hx,hy,_hBit⟩ | ⟨hx,hy,hBit⟩
    · have hAscending :
          hPosition k i k < hPosition k j k :=
        hPosition_lt_of_block_lt k i j k k le_rfl hij
      have hDescending :
          hPosition k j k < hPosition k i k := by
        calc
          hPosition k j k = hPosition k i' q' := hx
          _ < hPosition k j' m' :=
            hPosition_lt_of_block_lt k i' j' q' m' hq' hij'
          _ = hPosition k i k := hy.symm
      omega
    · obtain ⟨hi,hq⟩ := hPosition_injective_bounded
        k i k i' q' le_rfl hq' hy
      obtain ⟨hj,hm⟩ := hPosition_injective_bounded
        k j k j' m' le_rfl hm' hx
      rw [hi,hj]
      exact hBit
  · intro hBit
    exact ⟨i,j,k,k,hij,le_rfl,le_rfl,
      Or.inr ⟨rfl,rfl⟩,Or.inr ⟨rfl,rfl,hBit⟩⟩

theorem hNumericBinary_top_reverse_eq
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j : Nat) (r : Fin d) (hij : i < j) :
    hNumericBinary B k (hPosition k j k)
      (hPosition k i k) r = B j i r := by
  have hIff := hNumericBinary_top_reverse_true_iff
    B k i j r hij
  cases hb : B j i r with
  | false =>
      cases hh : hNumericBinary B k (hPosition k j k)
        (hPosition k i k) r with
      | false => rfl
      | true =>
          have hImpossible := hIff.mp hh
          simp [hb] at hImpossible
  | true =>
      simpa [hb] using (hIff.mpr hb)

/-- Every off-diagonal directed binary atom agrees on the
top-generation copy, in EITHER tuple orientation. -/
theorem hNumericBinary_top_induced_pair
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j : Nat) (r : Fin d) (hij : i ≠ j) :
    hNumericBinary B k (hPosition k i k)
      (hPosition k j k) r = B i j r := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hNumericBinary_top_forward_eq B k i j r hlt
  · exact hNumericBinary_top_reverse_eq B k j i r hgt

/-- Finite ordered base-prefix vertices are represented by
actual carrier vertices in finite H and retain all induced
unary, diagonal and both directed off-diagonal binary records. -/
theorem finiteNumericHL_top_induced_ordered_copy
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N n : Nat)
    (hInside : ∀ i : Fin n, hPosition k i.val k < N) :
    (∀ i : Fin n,
        hPosition k i.val k ∈ (finiteNumericHL K k N).carrier) ∧
    Function.Injective (fun i : Fin n => hPosition k i.val k) ∧
    (∀ i j : Fin n, i < j →
      hPosition k i.val k < hPosition k j.val k) ∧
    (∀ i j : Fin n, i ≠ j → ∀ r : Fin db,
      (finiteNumericHL K k N).binary
        (hPosition k i.val k) (hPosition k j.val k) r =
          K.binary i.val j.val r) ∧
    (∀ i : Fin n, ∀ r : Fin du,
      (finiteNumericHL K k N).unary
        (hPosition k i.val k) r = K.unary i.val r) ∧
    (∀ i : Fin n, ∀ r : Fin dd,
      (finiteNumericHL K k N).diagonal
        (hPosition k i.val k) r = K.diagonal i.val r) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact hInside i
  · intro i j heq
    exact Fin.ext
      (hPosition_injective_bounded
        k i.val k j.val k le_rfl le_rfl heq).1
  · intro i j hij
    exact hPosition_lt_of_block_lt
      k i.val j.val k k le_rfl (Fin.lt_def.mp hij)
  · intro i j hij r
    change hNumericBinary K.binary k (hPosition k i.val k)
      (hPosition k j.val k) r = K.binary i.val j.val r
    apply hNumericBinary_top_induced_pair
    intro heq
    exact hij (Fin.ext heq)
  · intro i r
    change hNumericSingleton K.unary k
      (hPosition k i.val k) r = K.unary i.val r
    rw [hNumericSingleton_real K.unary k i.val k le_rfl]
  · intro i r
    change hNumericSingleton K.diagonal k
      (hPosition k i.val k) r = K.diagonal i.val r
    rw [hNumericSingleton_real K.diagonal k i.val k le_rfl]

end SuccessorTree.V10
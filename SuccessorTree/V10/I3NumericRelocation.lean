import SuccessorTree.V10.HDirectedTraces
import SuccessorTree.V10.HGenerationRank
import Mathlib.Tactic

/-!
# Exact numerical H relation transport for the I3 lower relocation

In the current successor v10 proof (Lemma 6.53), lower vertices
iota(i,q) are relocated to iota(i,a), while later upper original
vertices iota(j,m) are unchanged. The whole *directed* binary L
record must be preserved, including false atoms.

This module proves that both numerical H relation directions are
exactly the base L bits when their generation gate holds. It also
shows that lowering an old generation to a rank a < k keeps a
linked lower--upper pair admissible, including the exceptional
top-generation tie.

The claims are local, true for arbitrary Boolean base tables and do
not introduce new axioms or hypotheses into the manuscript. The
full finite I3 age-witness relocation remains a separate composition.
-/

namespace SuccessorTree.V10

/-- The Boolean forward numerical H atom equals the base atom
under the exact generation gate, not merely when the atom is true. -/
theorem numericH_forward_eq_base_of_gate
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j q m : Nat) (t : Fin d)
    (hij : i < j) (hq : q ≤ k) (hm : m ≤ k)
    (hgate : q < m ∨ (q = m ∧ m = k)) :
    hNumericBinary B k
      (hPosition k i q) (hPosition k j m) t = B i j t := by
  have hiff := hNumericBinary_real_forward_iff
    B k i j q m t hij hq hm
  by_cases hb : B i j t = true
  · exact (hiff.mpr ⟨hgate,hb⟩).trans hb.symm
  · have hFalse : hNumericBinary B k
        (hPosition k i q) (hPosition k j m) t = false := by
      cases h : hNumericBinary B k
          (hPosition k i q) (hPosition k j m) t with
      | false => rfl
      | true =>
          have hf := (hiff.mp h).2
          exact False.elim (hb hf)
    cases hB : B i j t with
    | false => exact hFalse
    | true => exact False.elim (hb hB)

/-- The reverse numerical H tuple copies the REVERSED base atom
under the same gate; no symmetry of relations is assumed. -/
theorem numericH_reverse_eq_base_of_gate
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j q m : Nat) (t : Fin d)
    (hij : i < j) (hq : q ≤ k) (hm : m ≤ k)
    (hgate : q < m ∨ (q = m ∧ m = k)) :
    hNumericBinary B k
      (hPosition k j m) (hPosition k i q) t = B j i t := by
  have hiff := hNumericBinary_real_reverse_iff
    B k i j q m t hij hq hm
  by_cases hb : B j i t = true
  · exact (hiff.mpr ⟨hgate,hb⟩).trans hb.symm
  · have hFalse : hNumericBinary B k
        (hPosition k j m) (hPosition k i q) t = false := by
      cases h : hNumericBinary B k
          (hPosition k j m) (hPosition k i q) t with
      | false => rfl
      | true =>
          have hf := (hiff.mp h).2
          exact False.elim (hb hf)
    cases hB : B j i t with
    | false => exact hFalse
    | true => exact False.elim (hb hB)

/-- A linked lower--upper real pair remains an allowed pair after
replacing the lower generation q by a rank a≤q, provided a<k.
Its full original and relocated Boolean records then agree in
both directions, including negative atoms. -/
theorem numericH_linked_lower_upper_relocation
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j q m a : Nat)
    (hij : i < j) (hq : q ≤ k) (hm : m ≤ k)
    (ha : a ≤ q) (hak : a < k)
    (hLink : ∃ t : Fin d,
      hNumericBinary B k (hPosition k i q) (hPosition k j m) t = true ∨
      hNumericBinary B k (hPosition k j m) (hPosition k i q) t = true) :
    a < m ∧
    ∀ t : Fin d,
      hNumericBinary B k (hPosition k i q) (hPosition k j m) t =
        hNumericBinary B k (hPosition k i a) (hPosition k j m) t ∧
      hNumericBinary B k (hPosition k j m) (hPosition k i q) t =
        hNumericBinary B k (hPosition k j m) (hPosition k i a) t := by
  obtain ⟨r,hr⟩ := hLink
  have hgate : q < m ∨ (q = m ∧ m = k) := by
    rcases hr with hForward | hBackward
    · exact ((hNumericBinary_real_forward_iff
        B k i j q m r hij hq hm).mp hForward).1
    · exact ((hNumericBinary_real_reverse_iff
        B k i j q m r hij hq hm).mp hBackward).1
  have ham : a < m := by
    rcases hgate with hlt | ⟨heq,htop⟩
    · omega
    · omega
  refine ⟨ham,?_⟩
  intro t
  constructor
  · calc
      hNumericBinary B k (hPosition k i q) (hPosition k j m) t =
          B i j t :=
        numericH_forward_eq_base_of_gate B k i j q m t
          hij hq hm hgate
      _ = hNumericBinary B k (hPosition k i a)
          (hPosition k j m) t :=
        (numericH_forward_eq_base_of_gate B k i j a m t
          hij (by omega) hm (Or.inl ham)).symm
  · calc
      hNumericBinary B k (hPosition k j m) (hPosition k i q) t =
          B j i t :=
        numericH_reverse_eq_base_of_gate B k i j q m t
          hij hq hm hgate
      _ = hNumericBinary B k (hPosition k j m)
          (hPosition k i a) t :=
        (numericH_reverse_eq_base_of_gate B k i j a m t
          hij (by omega) hm (Or.inl ham)).symm

/-- Two linked lower real H vertices with increasing first indices
have all their directed atoms preserved when their generations q,m
are replaced by their ordered ranks a<b, provided both ranks are
at most k. This is the lower--lower zone of Lemma 6.53. -/
theorem numericH_linked_lower_lower_relocation
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j q m a b : Nat)
    (hij : i < j)
    (hab : a < b) (hb : b ≤ k)
    (hq : q ≤ k) (hm : m ≤ k)
    (hLink : ∃ t : Fin d,
      hNumericBinary B k (hPosition k i q) (hPosition k j m) t = true ∨
      hNumericBinary B k (hPosition k j m) (hPosition k i q) t = true) :
    ∀ t : Fin d,
      hNumericBinary B k (hPosition k i q) (hPosition k j m) t =
        hNumericBinary B k (hPosition k i a) (hPosition k j b) t ∧
      hNumericBinary B k (hPosition k j m) (hPosition k i q) t =
        hNumericBinary B k (hPosition k j b) (hPosition k i a) t := by
  obtain ⟨r,hr⟩ := hLink
  have hgate : q < m ∨ (q = m ∧ m = k) := by
    rcases hr with hForward | hBackward
    · exact ((hNumericBinary_real_forward_iff
        B k i j q m r hij hq hm).mp hForward).1
    · exact ((hNumericBinary_real_reverse_iff
        B k i j q m r hij hq hm).mp hBackward).1
  intro t
  have ha : a ≤ k := by omega
  constructor
  · calc
      hNumericBinary B k (hPosition k i q) (hPosition k j m) t =
          B i j t :=
        numericH_forward_eq_base_of_gate B k i j q m t hij hq hm hgate
      _ = hNumericBinary B k (hPosition k i a)
          (hPosition k j b) t :=
        (numericH_forward_eq_base_of_gate B k i j a b t
          hij ha hb (Or.inl hab)).symm
  · calc
      hNumericBinary B k (hPosition k j m) (hPosition k i q) t =
          B j i t :=
        numericH_reverse_eq_base_of_gate B k i j q m t hij hq hm hgate
      _ = hNumericBinary B k (hPosition k j b)
          (hPosition k i a) t :=
        (numericH_reverse_eq_base_of_gate B k i j a b t
          hij ha hb (Or.inl hab)).symm

end SuccessorTree.V10

import SuccessorTree.V10.HNumericBinary
import SuccessorTree.V10.MeetBundle

/-!
# Both directed binary H traces, with absent tuples preserved

The ordered H L-construction is encoded by an exact generator predicate
on numerical coordinates. The existing first-positive-disagreement
classification concerns bundled one-direction traces. We now prove
that BOTH real-real ordered directions of the numerical H relation
are exactly those traces: the reverse trace uses the transposed base
relation, and the same generation gate.

This does not silently identify the manuscript's underdetermined
one-way "substructure of K" clause with exact copying. That is an
editorial proof correction to be recorded in the TODOs.

The type-socle cutoff and Kpt predecessor/meet operations are handled
by the independently checked KptMeetBridge; their joint H application
remains a separate final theorem.
-/

namespace SuccessorTree.V10

/-- For a legal earlier-base-index real pair, the reversed
numerical H tuple has exactly the reversed base relation bit, under
the SAME generation gate as the forward tuple. -/
theorem hNumericBinary_real_reverse_iff
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k u i q n : Nat) (r : Fin d)
    (hui : u < i) (hq : q ≤ k) (hn : n ≤ k) :
    hNumericBinary B k
        (hPosition k i n) (hPosition k u q) r = true ↔
      (q < n ∨ (q = n ∧ n = k)) ∧ B i u r = true := by
  rw [hNumericBinary_true_iff]
  constructor
  · rintro ⟨u', i', q', n', hui', hq', hn', hgate', hdir⟩
    rcases hdir with ⟨hx, hy, hbit⟩ | ⟨hx, hy, hbit⟩
    · have hSourceOrder :
        hPosition k u q < hPosition k i n :=
        hPosition_lt_of_block_lt k u i q n hq hui
      have hGeneratedOrder :
        hPosition k u' q' < hPosition k i' n' :=
        hPosition_lt_of_block_lt k u' i' q' n' hq' hui'
      have hReverse : hPosition k i n < hPosition k u q := by
        calc
          hPosition k i n = hPosition k u' q' := hx
          _ < hPosition k i' n' := hGeneratedOrder
          _ = hPosition k u q := hy.symm
      omega
    · obtain ⟨hi, hnEq⟩ :=
        hPosition_injective_bounded k i n i' n' hn hn' hx
      obtain ⟨hu, hqEq⟩ :=
        hPosition_injective_bounded k u q u' q' hq hq' hy
      subst u'
      subst i'
      subst q'
      subst n'
      exact ⟨hgate', hbit⟩
  · rintro ⟨hgate, hbit⟩
    exact ⟨u, i, q, n, hui, hq, hn, hgate,
      Or.inr ⟨rfl, rfl, hbit⟩⟩

/-- Two Boolean values agree if and only if they agree on the
positive outcome; this converts the exact truth predicates to full
binary patterns including the absent tuples. -/
private theorem bool_eq_of_true_iff
    {a b : Bool} (h : (a = true ↔ b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Exact forward L atom vectors of numerical H are the complete
bundled trace of their base pair. This includes zero/absent atoms
and the exceptional top-generation gate. -/
theorem hNumericBinary_forward_matches_bundledTrace
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k u i q n : Nat)
    (hui : u < i) (hq : q ≤ k) (hn : n ≤ k) :
    (fun r : Fin d =>
      hNumericBinary B k
        (hPosition k u q) (hPosition k i n) r) =
      bundledTrace B k i n u q := by
  funext r
  apply bool_eq_of_true_iff
  rw [hNumericBinary_real_forward_iff B k u i q n r hui hq hn]
  by_cases hgate : q < n ∨ (q = n ∧ n = k)
  · simp [bundledTrace, traceBit, hui, hgate]
  · simp [bundledTrace, traceBit, hui, hgate]

/-- Exact REVERSED L atom vectors of numerical H are obtained by
transposing the base relation bits; no symmetry of the language
or its actual binary relations is assumed. -/
theorem hNumericBinary_reverse_matches_bundledTrace
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k u i q n : Nat)
    (hui : u < i) (hq : q ≤ k) (hn : n ≤ k) :
    (fun r : Fin d =>
      hNumericBinary B k
        (hPosition k i n) (hPosition k u q) r) =
      bundledTrace (fun a b r => B b a r) k i n u q := by
  funext r
  apply bool_eq_of_true_iff
  rw [hNumericBinary_real_reverse_iff B k u i q n r hui hq hn]
  by_cases hgate : q < n ∨ (q = n ∧ n = k)
  · simp [bundledTrace, traceBit, hui, hgate]
  · simp [bundledTrace, traceBit, hui, hgate]

end SuccessorTree.V10

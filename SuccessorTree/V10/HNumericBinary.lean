import SuccessorTree.V10.HExactE
import SuccessorTree.V10.FirstDisagreement
import Mathlib.Tactic

/-!
# Literal numerical encoding of H's directed binary L relations

H's auxiliary E predicate was already verified exactly on Nat.
For the binary L reduct, we now avoid any ambiguous 'substructure
of K' clause by defining every atom at numbered H vertices as the
existence of an allowed real-real generator carrying that atomic bit.
Both numeric orders of the endpoints are included, and every other
pair has an empty binary tuple. In particular, odd fake vertices
receive NO binary atoms.

This is a total relation on the numbered vertices, not an opaque
compatibility hypothesis about traces. The first theorem identifies
its value on a legal earlier/later real pair, using injectivity of
iota on bounded generations. Further integration with the finite
admissible Kpt witness will be kept separate.
-/

namespace SuccessorTree.V10

/-- A directed binary atom in the exact numerical H L-reduct.
The first disjunct includes (lower-index, higher-index) orientation;
the second includes the reversed ordered tuple. The generation gate
is symmetric as an undirected support condition, but the base relation
bits are always copied in the actual tuple orientation. -/
def HNumericCrossing
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k x y : Nat) (r : Fin d) : Prop :=
  ∃ i j q m : Nat,
    i < j ∧ q ≤ k ∧ m ≤ k ∧
    (q < m ∨ (q = m ∧ m = k)) ∧
    ((x = hPosition k i q ∧ y = hPosition k j m ∧
        B i j r = true) ∨
     (x = hPosition k j m ∧ y = hPosition k i q ∧
        B j i r = true))

/-- The exact directed numerical binary relation of H, including
all absent tuples. Classical decidability is only used to convert
the mathematical generator predicate into a Boolean vector. -/
noncomputable def hNumericBinary
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k x y : Nat) (r : Fin d) : Bool := by
  classical
  exact decide (HNumericCrossing B k x y r)

theorem hNumericBinary_true_iff
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k x y : Nat) (r : Fin d) :
    hNumericBinary B k x y r = true ↔
      HNumericCrossing B k x y r := by
  classical
  simp [hNumericBinary]

/-- A real earlier/later pair has exactly its prescribed directed
base atom if and only if its generations satisfy the H gate.
No other real vertex can represent either endpoint because the
numerical encoding is injective on generations <= k. -/
theorem hNumericBinary_real_forward_iff
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k u i q n : Nat) (r : Fin d)
    (hui : u < i) (hq : q ≤ k) (hn : n ≤ k) :
    hNumericBinary B k
        (hPosition k u q) (hPosition k i n) r = true ↔
      (q < n ∨ (q = n ∧ n = k)) ∧ B u i r = true := by
  rw [hNumericBinary_true_iff]
  constructor
  · rintro ⟨u',i',q',n',hUi',hq',hn',hgate',hdir⟩
    rcases hdir with ⟨hx,hy,hB⟩ | ⟨hx,hy,hB⟩
    · obtain ⟨hu,hqEq⟩ :=
        hPosition_injective_bounded k u q u' q' hq hq' hx
      obtain ⟨hi,hnEq⟩ :=
        hPosition_injective_bounded k i n i' n' hn hn' hy
      subst u'
      subst i'
      subst q'
      subst n'
      exact ⟨hgate',hB⟩
    · have hOrdered :=
        hPosition_lt_of_block_lt k u i q n hq hui
      have hOpposite :=
        hPosition_lt_of_block_lt k u' i' q' n' hq' hUi'
      have hReverse :
          hPosition k i n < hPosition k u q := by
        calc
          hPosition k i n = hPosition k u' q' := hy
          _ < hPosition k i' n' := hOpposite
          _ = hPosition k u q := hx.symm
      omega
  · rintro ⟨hgate,hbit⟩
    exact ⟨u,i,q,n,hui,hq,hn,hgate,Or.inl ⟨rfl,rfl,hbit⟩⟩

/-- Odd fake vertices cannot occur as either endpoint of a
positive directed binary relation in the exact H L-reduct.
This should not be confused with their auxiliary E incidences. -/
theorem hNumericBinary_odd_left_false
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k a y : Nat) (r : Fin d) :
    hNumericBinary B k (2 * a + 1) y r = false := by
  by_cases hbit : hNumericBinary B k (2 * a + 1) y r = true
  · obtain ⟨i,j,q,m,_,_,_,_,hdir⟩ :=
      (hNumericBinary_true_iff B k (2 * a + 1) y r).mp hbit
    rcases hdir with ⟨hx,_,_⟩ | ⟨hx,_,_⟩
    · obtain ⟨t,ht⟩ := hPosition_even k i q
      omega
    · obtain ⟨t,ht⟩ := hPosition_even k j m
      omega
  · cases h : hNumericBinary B k (2 * a + 1) y r with
    | false => rfl
    | true => exact False.elim (hbit h)

/-- The reverse endpoint has the same fake-vertex protection:
no binary atom may involve an odd fake vertex in either direction. -/
theorem hNumericBinary_odd_right_false
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k x a : Nat) (r : Fin d) :
    hNumericBinary B k x (2 * a + 1) r = false := by
  by_cases hbit : hNumericBinary B k x (2 * a + 1) r = true
  · obtain ⟨i,j,q,m,_,_,_,_,hdir⟩ :=
      (hNumericBinary_true_iff B k x (2 * a + 1) r).mp hbit
    rcases hdir with ⟨_,hy,_⟩ | ⟨_,hy,_⟩
    · obtain ⟨t,ht⟩ := hPosition_even k j m
      omega
    · obtain ⟨t,ht⟩ := hPosition_even k i q
      omega
  · cases h : hNumericBinary B k x (2 * a + 1) r with
    | false => rfl
    | true => exact False.elim (hbit h)

end SuccessorTree.V10

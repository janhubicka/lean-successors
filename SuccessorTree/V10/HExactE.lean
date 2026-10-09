import SuccessorTree.V10.EFreeLevel
import SuccessorTree.V10.SocleE
import SuccessorTree.V10.BlockOrder
import Mathlib.Tactic

/-!
# One exact E relation for the explicitly generated H structure

In the v10 H construction each real upper vertex v = iota(j,m) has a
generated E-socle, and no fake upper vertex generates E. We combine
these columns into one Boolean E relation on all Nat coordinates.

A bounded generation m ≤ k makes the map (j,m) -> iota(j,m) injective.
Thus there is no ambiguity about which E-column belongs to a real
upper vertex. We derive the spacing/downward axioms and compute its
unique canonical free level from the *exact* generated predicate.

The main manuscript obligation is still to prove that the actual
definition of H+ uses exactly this E predicate and includes no
additional E-pairs. In particular, the relation is NOT being
identified here with an arbitrary one-way substructure description.
-/

namespace SuccessorTree.V10

/-- Injectivity of the concrete real-vertex encoding on generations
0,...,k. This prevents two E-column generators from sharing an upper
vertex in the numerical H enumeration. -/
theorem hPosition_injective_bounded
    (k i q j m : Nat) (hq : q ≤ k) (hm : m ≤ k)
    (heq : hPosition k i q = hPosition k j m) :
    i = j ∧ q = m := by
  have hij : i = j := by
    by_contra hne
    have hcases : i < j ∨ j < i := by omega
    rcases hcases with hij | hji
    · have hlt := hPosition_lt_of_block_lt k i j q m hq hij
      omega
    · have hlt := hPosition_lt_of_block_lt k j i m q hm hji
      omega
  constructor
  · exact hij
  · rw [hij] at heq
    unfold hPosition at heq
    omega

/-- The exact generated E predicate of H on all numbered vertices.
All lower coordinates, including odd fake ones, are eligible E-socle
coordinates. Only real vertices appear as E targets. -/
def exactHE (k u v : Nat) : Prop :=
  ∃ j m : Nat, m ≤ k ∧ v = hPosition k j m ∧
    generatedE k j m u

/-- Boolean interpretation of the exact H E predicate. Classical
decidability is only used to express a numerical proposition as Bool. -/
noncomputable def exactHEBool (k u v : Nat) : Bool := by
  classical
  exact decide (exactHE k u v)

/-- The Boolean encoding is extensionally the generated proposition. -/
theorem exactHEBool_true_iff (k u v : Nat) :
    exactHEBool k u v = true ↔ exactHE k u v := by
  classical
  simp [exactHEBool]

/-- No other generated E columns can occur at the position of one
fixed real original: the bounded encoding has unique coordinates. -/
theorem exactHEBool_at_real_iff
    (k j m u : Nat) (hm : m ≤ k) :
    exactHEBool k u (hPosition k j m) = true ↔
      generatedE k j m u := by
  rw [exactHEBool_true_iff]
  constructor
  · rintro ⟨j', m', hm', heq, hgen⟩
    obtain ⟨hj, hg⟩ :=
      hPosition_injective_bounded k j m j' m' hm hm' heq
    subst j'
    subst m'
    exact hgen
  · intro hgen
    exact ⟨j, m, hm, rfl, hgen⟩

/-- Generated E has the literal spacing condition in Definition 6.28:
there is an intervening coordinate between E-related vertices. -/
theorem exactHEBool_spaced (k : Nat) :
    SpacedE (exactHEBool k) := by
  intro u v h
  obtain ⟨j, m, _, hv, hgen⟩ :=
    (exactHEBool_true_iff k u v).1 h
  rw [hv]
  exact generatedE_gap k j m u hgen

/-- Generated E has the literal downward-closure condition. -/
theorem exactHEBool_downward (k : Nat) :
    DownwardE (exactHEBool k) := by
  intro u v h w hw
  obtain ⟨j, m, hm, hv, hgen⟩ :=
    (exactHEBool_true_iff k u v).1 h
  exact (exactHEBool_true_iff k w v).2
    ⟨j, m, hm, hv,
      generatedE_downward k j m u w (Nat.le_of_lt hw) hgen⟩

/-- All nontrivial generated E columns are initial segments; this
helper compares the paper's explicit generated threshold with the
canonical free level derived from the global E relation. -/
theorem exactHEBool_freeLevel_eq_of_column
    (k j m cut : Nat) (hm : m ≤ k)
    (hColumn : ∀ u, generatedE k j m u ↔ u < cut) :
    canonicalFreeLevel (exactHEBool k)
        (exactHEBool_spaced k) (exactHEBool_downward k)
        (hPosition k j m) = cut := by
  have hCut : IsFreeCut (exactHEBool k)
      (hPosition k j m) cut := by
    constructor
    · intro u hu
      exact (exactHEBool_at_real_iff k j m u hm).2
        ((hColumn u).2 hu)
    · have hnot : ¬ generatedE k j m cut := by
        intro h
        exact (Nat.lt_irrefl cut) ((hColumn cut).1 h)
      have hb : exactHEBool k cut (hPosition k j m) ≠ true := by
        intro ht
        exact hnot ((exactHEBool_at_real_iff k j m cut hm).1 ht)
      cases h : exactHEBool k cut (hPosition k j m) with
      | false => rfl
      | true => exact False.elim (hb h)
  exact freeCut_unique (exactHEBool k) (hPosition k j m)
    (canonicalFreeLevel (exactHEBool k)
      (exactHEBool_spaced k) (exactHEBool_downward k)
      (hPosition k j m))
    cut
    (canonicalFreeLevel_isFreeCut (exactHEBool k)
      (exactHEBool_spaced k) (exactHEBool_downward k)
      (hPosition k j m))
    hCut

/-- Full free-level equation for a positive non-top generation in
the explicit H model, not just an isolated E-column calculation. -/
theorem exactHEBool_nonTop_freeLevel
    (k j m : Nat)
    (hj : 0 < j) (hm : 0 < m) (hmk : m < k) :
    canonicalFreeLevel (exactHEBool k)
        (exactHEBool_spaced k) (exactHEBool_downward k)
        (hPosition k j m) = nonTopFreeCut k j m := by
  apply exactHEBool_freeLevel_eq_of_column k j m
    (nonTopFreeCut k j m) (Nat.le_of_lt hmk)
  intro u
  exact generatedE_nonTop_iff k j m u hj hm hmk

/-- Full free-level equation for the top generation. The top
diagonal generation gate is treated separately. -/
theorem exactHEBool_top_freeLevel
    (k j : Nat) (hj : 0 < j) (hk : 0 < k) :
    canonicalFreeLevel (exactHEBool k)
        (exactHEBool_spaced k) (exactHEBool_downward k)
        (hPosition k j k) = hPosition k (j - 1) k + 1 := by
  apply exactHEBool_freeLevel_eq_of_column k j k
    (hPosition k (j - 1) k + 1) le_rfl
  intro u
  exact generatedE_top_iff k j u hj hk

/-- First block and generation-zero real vertices have free level
zero for k>0, exactly as in Observation 6.46. -/
theorem exactHEBool_initial_freeLevel
    (k j m : Nat) (hk : 0 < k) (hmk : m ≤ k)
    (hinitial : j = 0 ∨ m = 0) :
    canonicalFreeLevel (exactHEBool k)
        (exactHEBool_spaced k) (exactHEBool_downward k)
        (hPosition k j m) = 0 := by
  apply exactHEBool_freeLevel_eq_of_column k j m 0 hmk
  intro u
  constructor
  · intro h
    exact False.elim ((generatedE_empty_of_initial k j m u hk hinitial) h)
  · intro h
    omega


/-- Real H positions are even, so odd target vertices are genuinely
fake: they cannot support an incoming generated E column. -/
theorem hPosition_even (k j m : Nat) :
    ∃ t : Nat, hPosition k j m = 2 * t := by
  refine ⟨(k + 1) * j + m, ?_⟩
  unfold hPosition
  ring

/-- Every odd-numbered vertex has an empty incoming E-column in
the exact numerical H model. This does not make it an isolated
vertex of the full L+ structure. -/
theorem exactHEBool_odd_target_false (k u a : Nat) :
    exactHEBool k u (2 * a + 1) = false := by
  by_cases ht : exactHEBool k u (2 * a + 1) = true
  · obtain ⟨j, m, _, hv, _⟩ :=
      (exactHEBool_true_iff k u (2 * a + 1)).1 ht
    obtain ⟨t, heven⟩ := hPosition_even k j m
    have hodd : 2 * a + 1 = 2 * t := hv.trans heven
    omega
  · cases h : exactHEBool k u (2 * a + 1) with
    | false => rfl
    | true => exact False.elim (ht h)

/-- Fake odd vertices have free level zero, complementing the real
first-block and generation-zero statements. -/
theorem exactHEBool_fake_freeLevel
    (k a : Nat) :
    canonicalFreeLevel (exactHEBool k)
        (exactHEBool_spaced k) (exactHEBool_downward k)
        (2 * a + 1) = 0 := by
  have hCut : IsFreeCut (exactHEBool k) (2 * a + 1) 0 := by
    constructor
    · intro u hu
      omega
    · exact exactHEBool_odd_target_false k 0 a
  exact freeCut_unique (exactHEBool k) (2 * a + 1)
    (canonicalFreeLevel (exactHEBool k)
      (exactHEBool_spaced k) (exactHEBool_downward k)
      (2 * a + 1))
    0
    (canonicalFreeLevel_isFreeCut (exactHEBool k)
      (exactHEBool_spaced k) (exactHEBool_downward k)
      (2 * a + 1))
    hCut

/-- The first odd vertex is nevertheless a LOWER E-coordinate in
a later real top-generation vertex. This is the precise sense in
which the printed phrase 'fully isolated' is false for L+. -/
theorem exactHEBool_odd_source_not_isolated
    (k : Nat) (hk : 0 < k) :
    exactHEBool k 1 (hPosition k 1 k) = true :=
  (exactHEBool_at_real_iff k 1 k 1 le_rfl).2
    (oddFake_not_E_isolated k hk).2

end SuccessorTree.V10

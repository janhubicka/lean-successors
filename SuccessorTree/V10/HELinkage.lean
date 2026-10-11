import SuccessorTree.V10.HExactE
import SuccessorTree.V10.HAgeProjection

/-!
# The E/irreducible-pair axiom for the exact H-construction

Definition 6.28(3) requires each ordered pair u<v participating in
an L-relation to satisfy E(u,v). For the exact H model this follows
from the binary generation gate, not from a new assumption.

All directed binary bits are included in HLinked; the proof uses
that an L-link forces a legal generation gate and that numerical
position order of a linked real pair forces its base first-index
order. The generated E-socle contains every lower legal position.

Together with exactHEBool_spaced and exactHEBool_downward, this
proves all THREE defining E axioms of the paper's partial structures
for the explicit finite-binary H model (on ordered H vertices).

This does not identify the manuscript's underdetermined one-way
L-copying clause with the exact-copying HBinary model or prove
forbidden-freeness; that separate age assertion is treated in
HAgeProjection under an exact-model hypothesis.
-/

namespace SuccessorTree.V10

/-- Two linked real H originals, listed in increasing numerical
position, are E-related. The opposite base-index ordering is
ruled out by the actual H generation gate. -/
theorem exactHEBool_of_linked_real_positions
    {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool)
    (k : Nat) (i j : Fin n) (q m : Nat)
    (hLinked : HLinked B k (.real i q) (.real j m))
    (hOrder : hPosition k i.val q < hPosition k j.val m) :
    exactHEBool k (hPosition k i.val q)
        (hPosition k j.val m) = true := by
  have hij : i < j :=
    linked_firstIndex_lt_of_position_lt B k i j q m
      hLinked hOrder
  rcases HLinked_gate B k i j q m hLinked with
    ⟨_, hq, hm, hallowed⟩ | ⟨hji, _, _, _⟩
  · exact (exactHEBool_at_real_iff k j.val m
      (hPosition k i.val q) hm).2
      (generatedE_of_allowedPair k i.val j.val q m
        (Fin.lt_def.mp hij) hq hallowed)
  · have hnot : ¬ j < i := not_lt.mpr (le_of_lt hij)
    exact False.elim (hnot hji)

/-- The complete numerical H binary model satisfies E3: ANY two
linked vertices, including either orientation of every binary
symbol, have an E-edge in their numerical order. Fake targets and
same-first-index pairs cannot be linked in L. -/
theorem exactHEBool_of_HLinked_increasing
    {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool)
    (k : Nat) {a b : HVertex n}
    (hLinked : HLinked B k a b)
    (hOrder : hVertexPosition k a < hVertexPosition k b) :
    exactHEBool k (hVertexPosition k a)
        (hVertexPosition k b) = true := by
  obtain ⟨i, j, q, m, ha, hb, _⟩ := HLinked_real B k hLinked
  subst a
  subst b
  exact exactHEBool_of_linked_real_positions B k i j q m
    hLinked hOrder

/-- The three literal E-axioms of Definition 6.28 hold together for
the exact L/E H model: spacing, downward E-socles and E-linkage for
each irreducible ordered L-pair. No new structural axiom is used. -/
theorem exactH_satisfies_E_axioms
    {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool)
    (k : Nat) :
    SpacedE (exactHEBool k) ∧
      DownwardE (exactHEBool k) ∧
      ∀ a b : HVertex n,
        hVertexPosition k a < hVertexPosition k b →
        HLinked B k a b →
        exactHEBool k (hVertexPosition k a)
            (hVertexPosition k b) = true :=
  ⟨exactHEBool_spaced k, exactHEBool_downward k,
    fun _ _ hOrder hLinked =>
      exactHEBool_of_HLinked_increasing B k hLinked hOrder⟩

end SuccessorTree.V10

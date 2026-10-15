import SuccessorTree.V10.HTopInducedEmbedding
import SuccessorTree.V10.HFiniteAge
import Mathlib.Tactic

/-!
# Countable numerical H: the induced top-generation base K copy

Use the SAME complete L-atomic functions as the verified finite
H constructor, but on all Nat coordinates. Top real vertices
iota(i,k) then form a strictly ordered induced copy of the
given countable base K, preserving absent and present directed
binary relations, unary and diagonal bits.

Any forbidden ordered finite L-pattern occurring in countable
H fits inside a large finite numeric H initial segment.
Its age preservation theorem then rules out such a copy.
No additional E relation is assigned to that forbidden witness.

The universal H+ to G+ map and Theorem 6.26 are separate.
-/

namespace SuccessorTree.V10

noncomputable def infiniteNumericHL
    {db du dd : Nat} (K : AgeTestModel db du dd) (k : Nat) :
    AgeTestModel db du dd :=
  { carrier := Set.univ
    binary := hNumericBinary K.binary k
    unary := hNumericSingleton K.unary k
    diagonal := hNumericSingleton K.diagonal k }

theorem infiniteNumericHL_top_induced_ordered_copy
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (k : Nat) :
    (∀ i : Nat, hPosition k i k ∈ (infiniteNumericHL K k).carrier) ∧
    Function.Injective (fun i : Nat => hPosition k i k) ∧
    StrictMono (fun i : Nat => hPosition k i k) ∧
    (∀ i j : Nat, i ≠ j → ∀ r : Fin db,
      (infiniteNumericHL K k).binary
        (hPosition k i k) (hPosition k j k) r = K.binary i j r) ∧
    (∀ i : Nat, ∀ r : Fin du,
      (infiniteNumericHL K k).unary
        (hPosition k i k) r = K.unary i r) ∧
    (∀ i : Nat, ∀ r : Fin dd,
      (infiniteNumericHL K k).diagonal
        (hPosition k i k) r = K.diagonal i r) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i
    trivial
  · intro i j heq
    exact (hPosition_injective_bounded k i k j k le_rfl le_rfl heq).1
  · intro i j hij
    exact hPosition_lt_of_block_lt k i j k k le_rfl hij
  · intro i j hij r
    exact hNumericBinary_top_induced_pair K.binary k i j r hij
  · intro i r
    change hNumericSingleton K.unary k (hPosition k i k) r = K.unary i r
    rw [hNumericSingleton_real K.unary k i k le_rfl]
  · intro i r
    change hNumericSingleton K.diagonal k (hPosition k i k) r =
      K.diagonal i r
    rw [hNumericSingleton_real K.diagonal k i k le_rfl]

theorem infiniteNumericHL_copy_has_finite_truncation
    {db du dd r : Nat}
    (K : AgeTestModel db du dd) (k : Nat)
    (F : ForbiddenAtomicPattern r db du dd)
    (f : Fin r → Nat)
    (hCopy : (infiniteNumericHL K k).Realizes F f) :
    ∃ N : Nat, (finiteNumericHL K k N).Realizes F f := by
  classical
  let N := (Finset.univ : Finset (Fin r)).sup f + 1
  have hN : ∀ a : Fin r, f a < N := by
    intro a
    have hb : f a ≤ (Finset.univ : Finset (Fin r)).sup f :=
      Finset.le_sup (Finset.mem_univ a)
    dsimp [N]
    omega
  obtain ⟨hMono,_hCarrier,hB,hU,hD⟩ := hCopy
  refine ⟨N,hMono,?_,hB,hU,hD⟩
  intro a
  exact hN a

theorem infiniteNumericHL_avoids_family
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids K)
    (k : Nat) :
    ∀ bad, bad ∈ family →
      bad.Avoids (infiniteNumericHL K k) := by
  intro bad hBad
  have hFinite : ∀ N : Nat,
      bad.Avoids (finiteNumericHL K k N) := by
    intro N
    exact bad.finiteNumericH_preserves_avoidance
      K hCarrier k N (hAvoid bad hBad)
  cases bad with
  | singleton F hNonNeutral =>
      rintro ⟨f,hCopy⟩
      obtain ⟨N,hCopyN⟩ :=
        infiniteNumericHL_copy_has_finite_truncation K k F f hCopy
      exact hFinite N ⟨f,hCopyN⟩
  | nontrivial r F hr hIrred =>
      rintro ⟨f,hCopy⟩
      obtain ⟨N,hCopyN⟩ :=
        infiniteNumericHL_copy_has_finite_truncation K k F f hCopy
      exact hFinite N ⟨f,hCopyN⟩

end SuccessorTree.V10
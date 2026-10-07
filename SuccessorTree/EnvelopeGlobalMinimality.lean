import SuccessorTree.EnvelopeMinimalityCore
import Mathlib.Tactic

/-!
# Global minimality of the interesting levels

This packages the local competing-envelope contradiction into the decreasing
induction used in Proposition 5.5.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Interesting levels of the final run which lie strictly above i. -/
def higherLevels (I : Set Nat) (i : Nat) : Set Nat :=
  {j | j ∈ I ∧ i < j}

/-- If every selected level is interesting relative to the already selected
higher levels, then every competing finite-prefix envelope represents every
selected level. -/
theorem algorithmLevels_subset_competitor
    (H : SMTree S) (X : Set T) (ell m : Nat)
    (I : Set Nat) (E : MMap H)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell)
    (hIbound : ∀ ⦃i : Nat⦄, i ∈ I → i ≤ ell)
    (hEnvelope : IsPrefixEnvelope E.map m X)
    (hInteresting : ∀ ⦃i : Nat⦄, i ∈ I →
      IsInterestingAt H (closure S (higherLevels I i) X) i) :
    ∀ ⦃i : Nat⦄, i ∈ I → RepresentedBefore H E.map m i := by
  have main :
      ∀ d : Nat, ∀ i : Nat, ell - i = d → i ∈ I →
        RepresentedBefore H E.map m i := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro i hdi hiI
        have hiell : i ≤ ell := hIbound hiI
        by_cases hieq : i = ell
        · subst i
          obtain ⟨x, hxX, hxlev⟩ := hTop
          exact representedBefore_of_node H E.map m ell
            hEnvelope hxX hxlev
        · have hilt : i < ell := lt_of_le_of_ne hiell hieq
          let J : Set Nat := higherLevels I i
          have hJrepresented :
              J ⊆ {q | ∃ k < m, H.levelMap E.map k = q} := by
            intro q hq
            rcases hq with ⟨hqI, hiq⟩
            have hqell : q ≤ ell := hIbound hqI
            have hsmall : ell - q < d := by
              rw [← hdi]
              omega
            have hqrep := ih (ell - q) hsmall q rfl hqI
            exact hqrep
          have hC :
              IsPrefixEnvelope E.map m (closure S J X) :=
            prefixEnvelope_closure H E.map m hEnvelope hJrepresented
          have hMeet : MeetClosed (closure S J X) :=
            closure_meetClosed S J X
          obtain ⟨x, hxX, hxlev⟩ := hTop
          have hxC : x ∈ closure S J X :=
            subset_closure S J X hxX
          have hHigh : ∃ c ∈ closure S J X, i < LevelTree.lev c :=
            ⟨x, hxC, by rw [hxlev]; exact hilt⟩
          exact representedBefore_of_interesting
            H E m i hC hMeet hHigh (hInteresting hiI)
  intro i hiI
  exact main (ell - i) i rfl hiI

/-- The target levels represented by a prefix of source height m. -/
def prefixLevels
    (H : SMTree S) (E : MMap H) (m : Nat) : Finset Nat :=
  (Finset.range m).image (H.levelMap E.map)

/-- Membership in the finite target-level set is exactly prefix
representability. -/
theorem mem_prefixLevels_iff
    (H : SMTree S) (E : MMap H) (m q : Nat) :
    q ∈ prefixLevels H E m ↔ RepresentedBefore H E.map m q := by
  simp [prefixLevels, RepresentedBefore]

/-- A prefix of height m represents exactly m different target levels. -/
theorem card_prefixLevels
    (H : SMTree S) (E : MMap H) (m : Nat) :
    (prefixLevels H E m).card = m := by
  rw [prefixLevels, Finset.card_image_of_injective
    (Finset.range m) (H.levelMap_strictMono E.map).injective]
  exact Finset.card_range m

/-- Hence any finite family of forced target levels has size at most the
height of every competing prefix envelope. -/
theorem card_le_competing_height
    (H : SMTree S) (E : MMap H) (m : Nat)
    (J : Finset Nat)
    (hJ : ∀ q ∈ J, RepresentedBefore H E.map m q) :
    J.card ≤ m := by
  have hsub : J ⊆ prefixLevels H E m := by
    intro q hq
    rw [mem_prefixLevels_iff]
    exact hJ q hq
  calc
    J.card ≤ (prefixLevels H E m).card := Finset.card_le_card hsub
    _ = m := card_prefixLevels H E m

end Envelope
end SMTree
end SuccessorTree

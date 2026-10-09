import SuccessorTree.V10.HGenerationRank

/-!
# Relation preservation under the lower-generation relocation

In the signature repair, an ordered irreducible lower configuration of r
vertices is moved from iota(j_a,n_a) to iota(j_a,a). This module proves
preservation of the complete directed binary pattern for that move
inside the explicit H age model.

Two statements are separate:
* between two lower vertices, the relocated gate a<b is automatic;
* between a lower vertex and a later original upper vertex, an old
  linked pair and the generation-rank bound imply that the relocated
  gate remains admissible, including the exceptional top tie.

These are not yet the full local-age or signature-generation lemmas:
the upper vertices of the manuscript's age-test structure are prescribed
by partial types and require a separate correspondence argument.
-/

namespace SuccessorTree.V10

/-- Complete directed relations between lower vertices are preserved by
the canonical relocation, assuming irreducibility (pairwise linkage)
and strictly increasing first indices. -/
theorem relocated_lower_pairs {n d : Nat}
    (B : Fin n → Fin n → Fin d → Bool)
    (k r : Nat) (hr : r ≤ k)
    (first : Fin r → Fin n) (generation : Fin r → Nat)
    (hfirst : StrictMono first)
    (hlinked : ∀ a b : Fin r, a < b →
      HLinked B k (.real (first a) (generation a))
        (.real (first b) (generation b)))
    (a b : Fin r) (hab : a < b) (s : Fin d) :
    HBinary B k
        (.real (first a) (generation a))
        (.real (first b) (generation b)) s =
      HBinary B k (.real (first a) a.val)
        (.real (first b) b.val) s ∧
    HBinary B k
        (.real (first b) (generation b))
        (.real (first a) (generation a)) s =
      HBinary B k (.real (first b) b.val)
        (.real (first a) a.val) s := by
  have hqa : a.val ≤ k := by
    have ha := a.isLt
    omega
  have hqb : b.val ≤ k := by
    have hb := b.isLt
    omega
  have habNat : a.val < b.val := Fin.lt_def.mp hab
  have hgate : HCrossAllowed k (first a) (first b) a.val b.val :=
    Or.inl ⟨hfirst hab, hqa, hqb, Or.inl habNat⟩
  have hgateRev := (HCrossAllowed_swap k (first a) (first b)
    a.val b.val).mp hgate
  have hcopy := HBinary_eq_base_of_link B k
    (first a) (first b) (generation a) (generation b)
    (hlinked a b hab) s
  constructor
  · calc
      HBinary B k (.real (first a) (generation a))
          (.real (first b) (generation b)) s =
          B (first a) (first b) s := hcopy.1
      _ = HBinary B k (.real (first a) a.val)
          (.real (first b) b.val) s := by
          simp [HBinary, hgate]
  · calc
      HBinary B k (.real (first b) (generation b))
          (.real (first a) (generation a)) s =
          B (first b) (first a) s := hcopy.2
      _ = HBinary B k (.real (first b) b.val)
          (.real (first a) a.val) s := by
          simp [HBinary, hgateRev]

/-- A later upper original, linked to an old lower original, retains
its full directed binary pattern after relocating that lower vertex
to generation a. The original gate may be a strict generation rise
or a top-generation tie; both cases are treated. -/
theorem relocated_lower_upper_pair {n d r : Nat}
    (B : Fin n → Fin n → Fin d → Bool)
    (k : Nat) (hr : r ≤ k)
    (a : Fin r) (first upper : Fin n)
    (oldGeneration upperGeneration : Nat)
    (hfirst : first < upper)
    (hRank : a.val ≤ oldGeneration)
    (hlinked : HLinked B k
      (.real first oldGeneration) (.real upper upperGeneration))
    (s : Fin d) :
    HBinary B k (.real first oldGeneration)
        (.real upper upperGeneration) s =
      HBinary B k (.real first a.val)
        (.real upper upperGeneration) s ∧
    HBinary B k (.real upper upperGeneration)
        (.real first oldGeneration) s =
      HBinary B k (.real upper upperGeneration)
        (.real first a.val) s := by
  have hg := linked_increasing_generation B k first upper
    oldGeneration upperGeneration hfirst hlinked
  have hsmall : a.val ≤ k := by
    have ha := a.isLt
    omega
  have hlt : a.val < upperGeneration := by
    rcases hg.2.2 with hstrict | ⟨_, htop⟩
    · exact lt_of_le_of_lt hRank hstrict
    · have ha := a.isLt
      omega
  have hgate : HCrossAllowed k first upper a.val upperGeneration :=
    Or.inl ⟨hfirst, hsmall, hg.2.1, Or.inl hlt⟩
  have hgateRev := (HCrossAllowed_swap k first upper
    a.val upperGeneration).mp hgate
  have hcopy := HBinary_eq_base_of_link B k
    first upper oldGeneration upperGeneration hlinked s
  constructor
  · calc
      HBinary B k (.real first oldGeneration)
          (.real upper upperGeneration) s =
          B first upper s := hcopy.1
      _ = HBinary B k (.real first a.val)
          (.real upper upperGeneration) s := by
          simp [HBinary, hgate]
  · calc
      HBinary B k (.real upper upperGeneration)
          (.real first oldGeneration) s =
          B upper first s := hcopy.2
      _ = HBinary B k (.real upper upperGeneration)
          (.real first a.val) s := by
          simp [HBinary, hgateRev]

/-- Unary and diagonal data do not depend on the generation coordinate.
Thus relocation automatically preserves every singleton atomic fact. -/
theorem relocated_singleton_data {n du dd : Nat}
    (U : Fin n → Fin du → Bool)
    (D : Fin n → Fin dd → Bool)
    (i : Fin n) (q m : Nat) :
    (∀ r : Fin du,
      HUnary U (.real i q) r = HUnary U (.real i m) r) ∧
    (∀ r : Fin dd,
      HDiagonal D (.real i q) r =
        HDiagonal D (.real i m) r) := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

end SuccessorTree.V10

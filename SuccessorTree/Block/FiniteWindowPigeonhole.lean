import SuccessorTree.Block.SeededPigeonhole
import SuccessorTree.HalesJewett.FiniteWindow

/-!
# Finite-window block pigeonhole

The uniform finite Hales--Jewett window lets a finite structural application
replace the global seeded-realisation interface by realization of only the
starred lines whose words lie in one bounded window.

This module adds no successor-tree axiom and makes no A4, fusion, persistence,
or envelope claim.
-/

namespace SuccessorTree.Block

universe u v w x y z

variable {Γ : Type u} {Approx : Type v} {Block : Type w}
  {κ : Type x} {ι : Type y} {Point : Type z}

/-- Realization data only for starred lines contained in the length-N window. -/
def HasWindowRealisation
    (N : Nat)
    (wordApprox : HalesJewett.WindowWord Γ N → Approx)
    (apply : Block → LineInput Γ → Approx) : Prop :=
  ∀ (L : StarLine Γ) (hL : L.word.length ≤ N),
    ∃ b : Block,
      apply b .base =
        wordApprox ⟨L.star, le_trans L.length_star_le_word_length hL⟩ ∧
      ∀ e : Γ,
        apply b (.letter e) =
          wordApprox ⟨L.eval e, by
            simpa using L.length_eval e ▸ hL⟩

/-- The one-block pigeonhole theorem using only a finite word window. -/
theorem windowPigeonhole
    [Fintype Γ] [Fintype κ]
    (N : Nat)
    (hHJ : HalesJewett.StarHJWindow Γ κ N)
    (wordApprox : HalesJewett.WindowWord Γ N → Approx)
    (apply : Block → LineInput Γ → Approx)
    (hRealise : HasWindowRealisation N wordApprox apply)
    (colour : Approx → κ) :
    ∃ b : Block, ∀ a : LineInput Γ,
      colour (apply b a) = colour (apply b .base) := by
  obtain ⟨L, hLen, hMono⟩ :=
    hHJ (fun w => colour (wordApprox w))
  obtain ⟨b, hBase, hLetter⟩ := hRealise L hLen
  refine ⟨b, ?_⟩
  intro a
  cases a with
  | base => rfl
  | letter e =>
      rw [hLetter e, hBase]
      exact hMono e

/-- One finite-window block works for an entire finite batch of profiles. -/
theorem finiteWindowProfilePigeonhole
    [Fintype Γ] [Fintype κ] [Fintype ι]
    (N : Nat)
    (hHJ : HalesJewett.StarHJWindow Γ (ι → κ) N)
    (wordApprox : HalesJewett.WindowWord Γ N → Approx)
    (apply : Block → LineInput Γ → Approx)
    (hRealise : HasWindowRealisation N wordApprox apply)
    (profile : ι → Approx → Point)
    (colour : Point → κ) :
    ∃ b : Block, ∀ i : ι, ∀ a : LineInput Γ,
      colour (profile i (apply b a)) =
        colour (profile i (apply b .base)) := by
  classical
  obtain ⟨b, hb⟩ :=
    windowPigeonhole N hHJ wordApprox apply hRealise
      (fun t i => colour (profile i t))
  refine ⟨b, ?_⟩
  intro i a
  exact congrFun (hb a) i

/-- Finite-window analogue of coveredFrontPigeonhole_of_parent.
The profile family and parent hierarchy are fixed independently of the window
line chosen by Hales--Jewett. -/
theorem coveredFrontWindowPigeonhole_of_parent
    [Fintype Γ] [Fintype κ] [Fintype ι]
    (N : Nat)
    (hHJ : HalesJewett.StarHJWindow Γ (ι → κ) N)
    (wordApprox : HalesJewett.WindowWord Γ N → Approx)
    (apply : Block → LineInput Γ → Approx)
    (hRealise : HasWindowRealisation N wordApprox apply)
    (profile : ι → Approx → Point)
    (front : Block → Set Point) (anchor : Block → Point)
    (root : ι) (level : ι → Nat) (parent : ι → ι)
    (hCover : ∀ b t, t ∈ front b →
      ∃ i : ι, ∃ a : LineInput Γ, profile i (apply b a) = t)
    (hRoot : ∀ b, profile root (apply b .base) = anchor b)
    (hParentLevel : ∀ i, i ≠ root → level (parent i) < level i)
    (hParentLink : ∀ b i, i ≠ root →
      ∃ a a' : LineInput Γ,
        profile i (apply b a) = profile (parent i) (apply b a'))
    (colour : Point → κ) :
    ∃ b : Block, ∀ t ∈ front b, colour t = colour (anchor b) := by
  classical
  obtain ⟨b, hb⟩ :=
    finiteWindowProfilePigeonhole
      N hHJ wordApprox apply hRealise profile colour
  have hAlign : ∀ i : ι,
      colour (profile i (apply b .base)) = colour (anchor b) := by
    intro i
    generalize hn : level i = n
    induction n using Nat.strong_induction_on generalizing i with
    | h n ih =>
        by_cases hir : i = root
        · subst i
          rw [hRoot b]
        · obtain ⟨a, a', hEq⟩ := hParentLink b i hir
          have hp : level (parent i) < n := by
            simpa [hn] using hParentLevel i hir
          calc
            colour (profile i (apply b .base)) =
                colour (profile i (apply b a)) := (hb i a).symm
            _ = colour (profile (parent i) (apply b a')) :=
              congrArg colour hEq
            _ = colour (profile (parent i) (apply b .base)) :=
              hb (parent i) a'
            _ = colour (anchor b) :=
              ih (level (parent i)) hp (parent i) rfl
  refine ⟨b, ?_⟩
  intro t ht
  obtain ⟨i, a, rfl⟩ := hCover b t ht
  exact (hb i a).trans (hAlign i)

end SuccessorTree.Block

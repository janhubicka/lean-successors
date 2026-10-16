import SuccessorTree.Counterexample.NowhereDense
import Mathlib.Tactic

/-!
# Almost-disjoint supports force a unique compatible marker

Purely abstract final step of the root-marker compatibility proof.
A common right multiple of an earlier map G and a marked candidate
forces a *fixed infinite* witness set into that candidate's support.
Two almost-disjoint supports therefore cannot both be compatible with G.
No special properties of the free ancestral tree are assumed here.
-/

namespace SuccessorTree.SMTree

universe u v w
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

/-- Any given map has at most one compatible element in a family of
marked maps with pairwise finite support intersection, provided common
right multiples force a fixed infinite support-witness set into the
marked support. -/
theorem compatible_marked_unique
    (H : SMTree S)
    {Index : Type w}
    (supports : Index → Set Nat)
    (marked : Index → MMap H)
    (witness : MMap H → Set Nat)
    (had : ∀ ⦃i j : Index⦄, i ≠ j →
      (supports i ∩ supports j).Finite)
    (hmarker : ∀ (G : MMap H) (i : Index),
      RightCompatible H G (marked i) →
      (witness G).Infinite ∧ witness G ⊆ supports i)
    (G : MMap H) (i j : Index)
    (hi : RightCompatible H G (marked i))
    (hj : RightCompatible H G (marked j)) :
    i = j := by
  by_contra hij
  obtain ⟨hinfinite, hsubi⟩ := hmarker G i hi
  obtain ⟨_, hsubj⟩ := hmarker G j hj
  have hfinite : (witness G).Finite :=
    (had hij).subset (by
      intro k hk
      exact ⟨hsubi hk, hsubj hk⟩)
  exact hinfinite hfinite

end SuccessorTree.SMTree

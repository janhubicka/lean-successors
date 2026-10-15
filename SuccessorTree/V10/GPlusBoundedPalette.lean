import SuccessorTree.V10.GPlusNeutralCapType
import SuccessorTree.RamseySpace.Finitization
import Mathlib.Tactic

/-!
# V10 final transfer: finite palette of bounded Kpt representing pairs

In Theorem 6.26, after the actual Algorithm 5.4 envelope covers a
finite set of G+ vertices, only finitely many bounded Kpt types can
occur. This module checks the purely FINITE combinatorial step:
genuine representing pairs (S,T) with level(T) <= b form a finite
type; hence their actual G+ images form a finite set, and
pointwise q-tuples of these images also form a finite set.

The proof uses the already checked concrete Kpt LevelTree finite
levels via the reusable SMTree.InitialNode Fintype instance, not
a new local-finiteness or representation assumption.

It does NOT assert that the existing envelope bound already
gives representatives with the required upper level. That is
the separate manuscript-geometry transfer still to be proved.
No finite-colouring Ramsey assembly is claimed here.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- A genuine representing pair whose larger admissible Kpt type
belongs to the specified bounded initial Kpt level segment. -/
abbrev BoundedGPlusRepresentingPair
    (family : List (NormalizedForbidden db du dd)) (b : Nat) :=
  {P : GPlusRepresentingPair family // LevelTree.lev P.upper ≤ b}

/-- Finite levels of the actual normalized Kpt LevelTree imply
finitely many genuine strict representing pairs at bounded height. -/
noncomputable instance boundedGPlusRepresentingPairFintype
    (family : List (NormalizedForbidden db du dd)) (b : Nat) :
    Fintype (BoundedGPlusRepresentingPair family b) := by
  classical
  let T := AdmissibleKptNode family
  let e : BoundedGPlusRepresentingPair family b →
      SuccessorTree.SMTree.InitialNode T b ×
        SuccessorTree.SMTree.InitialNode T b :=
    fun P =>
      (⟨P.val.lower,
        (LevelTree.level_le_of_le P.val.lower_lt_upper.le).trans P.property⟩,
       ⟨P.val.upper, P.property⟩)
  apply Fintype.ofInjective e
  intro P Q h
  have hL : P.val.lower = Q.val.lower :=
    congrArg
      (fun z : SuccessorTree.SMTree.InitialNode T b ×
          SuccessorTree.SMTree.InitialNode T b => z.1.val) h
  have hU : P.val.upper = Q.val.upper :=
    congrArg
      (fun z : SuccessorTree.SMTree.InitialNode T b ×
          SuccessorTree.SMTree.InitialNode T b => z.2.val) h
  rcases P with ⟨⟨pLow,pTop,hP⟩,pBound⟩
  rcases Q with ⟨⟨qLow,qTop,hQ⟩,qBound⟩
  change pLow = qLow at hL
  change pTop = qTop at hU
  subst qLow
  subst qTop
  rfl

/-- Genuine G+ vertices admitting a bounded Kpt pair representation.
This is the exact representation notion, not a bound merely on the
finite code's numerical size. -/
def boundedRepresentableGPlusVertices
    (family : List (NormalizedForbidden db du dd)) (b : Nat) :
    Set (FiniteGPlusVertex family) :=
  Set.range (fun P : BoundedGPlusRepresentingPair family b => P.val.vertex)

/-- Bounded Kpt-pair representable G+ vertices form a finite set.
No envelope or colouring hypothesis is hidden in the statement. -/
theorem boundedRepresentableGPlusVertices_finite
    (family : List (NormalizedForbidden db du dd)) (b : Nat) :
    (boundedRepresentableGPlusVertices family b).Finite := by
  classical
  change (Set.range
    (fun P : BoundedGPlusRepresentingPair family b => P.val.vertex)).Finite
  exact Set.finite_range _

/-- The q-point palette of G+ vertex tuples represented by actual
bounded Kpt pairs. Every candidate is a true map Fin q -> G+,
and the entire palette is a finite set even before imposing
injectivity, a prescribed finite induced A-type or order. -/
def boundedGPlusTuplePalette
    (family : List (NormalizedForbidden db du dd))
    (b q : Nat) : Set (Fin q → FiniteGPlusVertex family) :=
  Set.range (fun f : Fin q → BoundedGPlusRepresentingPair family b =>
    fun i => (f i).val.vertex)

/-- A literal finite palette, suitable for restricting any future
set of representable embeddings to a finite set of possibilities. -/
theorem boundedGPlusTuplePalette_finite
    (family : List (NormalizedForbidden db du dd)) (b q : Nat) :
    (boundedGPlusTuplePalette family b q).Finite := by
  classical
  change (Set.range
    (fun f : Fin q → BoundedGPlusRepresentingPair family b =>
      fun i => (f i).val.vertex)).Finite
  exact Set.finite_range _

end SuccessorTree.V10

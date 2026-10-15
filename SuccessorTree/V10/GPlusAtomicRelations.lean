import SuccessorTree.V10.GPlusFinitePrefix
import Mathlib.Tactic

/-!
# Definition 6.40: exact unary, directed-binary, diagonal and E atoms of G+

Vertices are the canonical finite codes of nonempty verified
enumerated partial L+ structures. For comparable vertices
A+ strictly below B+ in the finite-code prefix order, the
ordered pair (A+,B+) receives precisely the atoms of the
ordered pair (|A+|-1, |B+|-1) in the larger partial B+.
The REVERSE ordered pair uses the reverse bits of B+, and
the E relation uses the same two last coordinates.

For incomparable pairs there are NO binary or E tuples.
Unary and diagonal atoms on one G+ vertex are taken from
its last coordinate. The separate diagonal field retains
binary loops of the original finite language.

These are exactly the clauses (1)--(3) in Definition 6.40.
The next Lemma 6.41 proof uses irreducibility: every linked
pair of forbidden-copy vertices must be comparable, hence
all vertices of a forbidden copy lie on one prefix chain.
-/

namespace SuccessorTree.V10

/-- A finite G+ vertex has a nonempty carrier by construction,
so the last coordinate is always defined. -/
theorem finiteGPlusVertex_size_pos
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (C : FiniteGPlusVertex family) :
    0 < C.val.size := by
  obtain ⟨A,hCode,hPos,_hAvoid⟩ := C.property
  rw [hCode]
  exact hPos

/-- The coordinate in the source partial structure represented
by a given G+ node: its last ordinal. -/
def FiniteGPlusVertex.last
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (C : FiniteGPlusVertex family) : Fin C.val.size :=
  ⟨C.val.size-1,by have := finiteGPlusVertex_size_pos C; omega⟩

/-- Genuine strict prefix order on G+ vertices. Equal-size nodes
cannot be strictly comparable. -/
def FiniteGPlusVertex.IsProperPrefix
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (A B : FiniteGPlusVertex family) : Prop :=
  A.val.IsPrefix B.val ∧ A.val.size < B.val.size

theorem FiniteGPlusVertex.properPrefix_asymm
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {A B : FiniteGPlusVertex family}
    (h : A.IsProperPrefix B) :
    ¬ B.IsProperPrefix A := by
  intro h'
  have := h.2
  have := h'.2
  omega

/-- The smaller node's last coordinate, interpreted as a
coordinate inside the larger node's finite atomic table. -/
def FiniteGPlusVertex.lowerLastIn
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (A B : FiniteGPlusVertex family)
    (h : A.IsProperPrefix B) : Fin B.val.size :=
  ⟨A.val.size-1,by
    have hPositive := finiteGPlusVertex_size_pos A
    have hLt := h.2
    omega⟩

/-- Exactly the directed off-diagonal binary atoms of the
L-reduct of G+; incomparable or identical vertices carry no
binary off-diagonal fact. -/
noncomputable def finiteGPlusBinary
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (A B : FiniteGPlusVertex family)
    (a : Fin db) : Bool := by
  classical
  exact if h : A.IsProperPrefix B then
    B.val.binary (A.lowerLastIn B h) B.last a
  else if h : B.IsProperPrefix A then
    A.val.binary A.last (B.lowerLastIn A h) a
  else false

/-- Exactly the auxiliary E atoms between comparable G+ nodes,
using the same oriented two-last-coordinate convention. -/
noncomputable def finiteGPlusE
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (A B : FiniteGPlusVertex family) : Bool := by
  classical
  exact if h : A.IsProperPrefix B then
    B.val.eRelation (A.lowerLastIn B h) B.last
  else if h : B.IsProperPrefix A then
    A.val.eRelation A.last (B.lowerLastIn A h)
  else false

/-- One-vertex unary predicates come from the last coordinate. -/
def finiteGPlusUnary
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (A : FiniteGPlusVertex family)
    (a : Fin du) : Bool :=
  A.val.unary A.last a

/-- Unary representation of binary relation loops: diagonal
atoms stay distinct from directed off-diagonal relation bits. -/
def finiteGPlusDiagonal
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (A : FiniteGPlusVertex family)
    (a : Fin dd) : Bool :=
  A.val.diagonal A.last a

/-- The forward directed binary atom on a proper-prefix pair
agrees with the larger partial structure at its two last
coordinates, including false atoms. -/
theorem finiteGPlusBinary_forward
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (A B : FiniteGPlusVertex family)
    (a : Fin db)
    (h : A.IsProperPrefix B) :
    finiteGPlusBinary A B a =
      B.val.binary (A.lowerLastIn B h) B.last a := by
  simp [finiteGPlusBinary, h]

/-- The reverse directed atom is read from the SAME larger
finite code, with the two last coordinates reversed. -/
theorem finiteGPlusBinary_reverse
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (A B : FiniteGPlusVertex family)
    (a : Fin db)
    (h : A.IsProperPrefix B) :
    finiteGPlusBinary B A a =
      B.val.binary B.last (A.lowerLastIn B h) a := by
  have hNot : ¬ B.IsProperPrefix A := h.properPrefix_asymm
  simp [finiteGPlusBinary, hNot, h, FiniteGPlusVertex.lowerLastIn]

/-- The forward E atom is the exact E bit of the larger node's
last-coordinate pair. -/
theorem finiteGPlusE_forward
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (A B : FiniteGPlusVertex family)
    (h : A.IsProperPrefix B) :
    finiteGPlusE A B =
      B.val.eRelation (A.lowerLastIn B h) B.last := by
  simp [finiteGPlusE, h]

/-- As required by Definition 6.40, unrelated branches of the
G+ prefix tree have no directed binary atoms. -/
theorem finiteGPlusBinary_incomparable
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (A B : FiniteGPlusVertex family)
    (a : Fin db)
    (hAB : ¬ A.IsProperPrefix B)
    (hBA : ¬ B.IsProperPrefix A) :
    finiteGPlusBinary A B a = false := by
  simp [finiteGPlusBinary, hAB,hBA]

theorem finiteGPlusE_incomparable
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (A B : FiniteGPlusVertex family)
    (hAB : ¬ A.IsProperPrefix B)
    (hBA : ¬ B.IsProperPrefix A) :
    finiteGPlusE A B = false := by
  simp [finiteGPlusE,hAB,hBA]

/-- Any actual positive directed binary atom in G+ certifies
comparability of its vertices. This is the first implication
in the irreducibility argument of Lemma 6.41. -/
theorem finiteGPlusBinary_true_implies_comparable
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (A B : FiniteGPlusVertex family)
    (a : Fin db)
    (hTrue : finiteGPlusBinary A B a = true) :
    A.IsProperPrefix B ∨ B.IsProperPrefix A := by
  by_cases hAB : A.IsProperPrefix B
  · exact Or.inl hAB
  · by_cases hBA : B.IsProperPrefix A
    · exact Or.inr hBA
    · have hFalse := finiteGPlusBinary_incomparable A B a hAB hBA
      rw [hFalse] at hTrue
      cases hTrue

end SuccessorTree.V10

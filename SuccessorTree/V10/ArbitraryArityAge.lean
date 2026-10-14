import Mathlib.Tactic

/-!
# Finite relational signatures: arbitrary-arity induced L-age transport

The concrete normalized Kpt proof presently codes unary, directed binary
and diagonal information in Boolean tables. Its faithful general-language
adapter must preserve EVERY atomic relation of arbitrary finite arity,
including repeated coordinates and negative tuples.

This file introduces a signature-indexed Boolean atom table. Nullary
relations are included: their unique empty tuple is retained unchanged
by neutral extension. The source carrier remains separate from atomic
data, as in the original finite L-age tests.

The basic induced-embedding theorem below handles all arities at once.
The irreducible neutral-extension lemma is the exact general-arity
analogue of the neutral-dummy age argument used in the English M2 proof.
No `E` is introduced on arbitrary age witnesses.

This foundational representation is NOT an adapter of the existing
Kpt successor operation or M2/M3 to general signatures. The higher-arity
canonical parameter and retained-record laws remain to be formalized.
-/

namespace SuccessorTree.V10

universe u

/-- A relational signature with arities that may include zero.
Finiteness of the set of symbols will be assumed separately when needed. -/
structure AritySignature where
  Symbol : Type u
  arity : Symbol → Nat

/-- Complete Boolean tables for every ordered tuple of every relation
symbol, without restricting arity or forbidding repeated entries. -/
structure ArityAge (L : AritySignature.{u}) where
  carrier : Set Nat
  atom : (s : L.Symbol) → (Fin (L.arity s) → Nat) → Bool

/-- A finite enumerated forbidden pattern in the same relational language. -/
structure ArityPattern (L : AritySignature.{u}) (r : Nat) where
  atom : (s : L.Symbol) → (Fin (L.arity s) → Fin r) → Bool

/-- Full induced ordered realization: equality of Boolean atoms includes
all nonedges, repeated-coordinate tuples, and the nullary record. -/
def ArityAge.Realizes
    {L : AritySignature.{u}} {r : Nat}
    (A : ArityAge L) (P : ArityPattern L r)
    (e : Fin r → Nat) : Prop :=
  StrictMono e ∧
  (∀ a : Fin r, e a ∈ A.carrier) ∧
  ∀ (s : L.Symbol) (t : Fin (L.arity s) → Fin r),
    A.atom s (fun i => e (t i)) = P.atom s t

/-- Relative induced embedding, preserving BOTH true and false atoms
on every tuple made of actual carrier vertices. -/
structure ArityAge.InducedEmbeddingOnCarrier
    {L : AritySignature.{u}}
    (A B : ArityAge L) where
  toFun : Nat → Nat
  order : ∀ x y, x ∈ A.carrier → y ∈ A.carrier → x < y →
    toFun x < toFun y
  inside : ∀ x, x ∈ A.carrier → toFun x ∈ B.carrier
  atom : ∀ (s : L.Symbol) (t : Fin (L.arity s) → Nat),
    (∀ i, t i ∈ A.carrier) →
    B.atom s (fun i => toFun (t i)) = A.atom s t

/-- Literal induced realizations survive an induced embedding for
arbitrary finite arities; nothing special is assumed for binary relations. -/
theorem ArityAge.InducedEmbeddingOnCarrier.realizes
    {L : AritySignature.{u}} {r : Nat}
    {A B : ArityAge L}
    (H : A.InducedEmbeddingOnCarrier B)
    (P : ArityPattern L r) (e : Fin r → Nat)
    (h : A.Realizes P e) :
    B.Realizes P (fun a => H.toFun (e a)) := by
  rcases h with ⟨hOrder,hInside,hAtom⟩
  refine ⟨?_,?_,?_⟩
  · intro a b hab
    exact H.order (e a) (e b) (hInside a) (hInside b) (hOrder hab)
  · intro a
    exact H.inside (e a) (hInside a)
  · intro s t
    exact (H.atom s (fun i => e (t i))
      (fun i => hInside (t i))).trans (hAtom s t)

/-- The one explicit neutral filler model: all old-vertex tuples are
unchanged; any tuple containing a new vertex has no positive relation.
Nullary atoms have no vertices and are therefore copied unchanged. -/
def ArityAge.neutralExtension
    {L : AritySignature.{u}} (A : ArityAge L)
    (newCarrier : Set Nat) : ArityAge L where
  carrier := A.carrier ∪ newCarrier
  atom := fun s t =>
    if h : ∀ i, t i ∈ A.carrier then A.atom s t else false

/-- The old age is an induced substructure of its neutral extension;
this includes every negative tuple and the nullary interpretation. -/
def ArityAge.inducedIntoNeutralExtension
    {L : AritySignature.{u}} (A : ArityAge L)
    (newCarrier : Set Nat) :
    A.InducedEmbeddingOnCarrier (A.neutralExtension newCarrier) where
  toFun := id
  order := by
    intro x y _ _ hxy
    exact hxy
  inside := by
    intro x hx
    exact Or.inl hx
  atom := by
    intro s t ht
    simp [ArityAge.neutralExtension, ht]

/-- General finite-arity irreducibility: for every distinct pair of
vertices, some positive relation tuple contains both of them.
This implies the usual pairwise irreducibility even with repeated
vertices elsewhere in a tuple. -/
def ArityPattern.PairwiseIrreducible
    {L : AritySignature.{u}} {r : Nat}
    (P : ArityPattern L r) : Prop :=
  ∀ a b : Fin r, a ≠ b →
    ∃ (s : L.Symbol) (t : Fin (L.arity s) → Fin r)
      (i j : Fin (L.arity s)),
      P.atom s t = true ∧ t i = a ∧ t j = b

/-- A genuinely non-neutral singleton has a positive non-nullary atom.
Without this hypothesis, adding a neutral vertex could create a
forbidden singleton. The nullary interpretation is fixed separately. -/
def ArityPattern.NonNeutralSingleton
    {L : AritySignature.{u}}
    (P : ArityPattern L 1) : Prop :=
  ∃ (s : L.Symbol) (t : Fin (L.arity s) → Fin 1),
    0 < L.arity s ∧ P.atom s t = true

/-- Pairwise irreducibility rules out a forbidden nontrivial copy using
any dummy vertex of a neutral extension. No relation-arity bound is used.
The finite cardinality assumption supplies a second vertex for each
chosen vertex; no positivity of particular binary atoms is assumed. -/
theorem ArityAge.realizes_in_neutralExtension_of_irreducible
    {L : AritySignature.{u}} {r : Nat}
    (A : ArityAge L) (newCarrier : Set Nat)
    (P : ArityPattern L r)
    (hTwo : 2 ≤ r) (hIrred : P.PairwiseIrreducible)
    (e : Fin r → Nat)
    (hCopy : (A.neutralExtension newCarrier).Realizes P e) :
    A.Realizes P e := by
  have hAnother : ∀ a : Fin r, ∃ b : Fin r, a ≠ b := by
    intro a
    by_cases ha : a.val = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro heq
      have hh := congrArg Fin.val heq
      dsimp at hh
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro heq
      have hh := congrArg Fin.val heq
      dsimp at hh
      omega
  have hOld : ∀ a : Fin r, e a ∈ A.carrier := by
    intro a
    obtain ⟨b,hab⟩ := hAnother a
    obtain ⟨s,t,i,j,hPositive,hai,hbj⟩ := hIrred a b hab
    have hAtom := hCopy.2.2 s t
    have hOldA : e (t i) ∈ A.carrier := by
      by_contra hMissing
      have hNotAll : ¬ (∀ q, e (t q) ∈ A.carrier) := by
        intro hall
        exact hMissing (hall i)
      have hFalse :
          (A.neutralExtension newCarrier).atom s (fun q => e (t q)) =
            false := by
        simp [ArityAge.neutralExtension, hNotAll]
      rw [hFalse, hPositive] at hAtom
      cases hAtom
    simpa [hai] using hOldA
  refine ⟨hCopy.1,hOld,?_⟩
  intro s t
  have hAll : ∀ q, e (t q) ∈ A.carrier := by
    intro q
    exact hOld (t q)
  have hAtom := hCopy.2.2 s t
  simpa [ArityAge.neutralExtension, hAll] using hAtom

/-- A forbidden non-neutral singleton also cannot arise on a dummy:
its positive non-nullary atom certifies that its vertex is old. -/
theorem ArityAge.realizes_singleton_in_neutralExtension
    {L : AritySignature.{u}}
    (A : ArityAge L) (newCarrier : Set Nat)
    (P : ArityPattern L 1)
    (hNonNeutral : P.NonNeutralSingleton)
    (e : Fin 1 → Nat)
    (hCopy : (A.neutralExtension newCarrier).Realizes P e) :
    A.Realizes P e := by
  obtain ⟨s,t,hPos,hPositive⟩ := hNonNeutral
  let i : Fin (L.arity s) := ⟨0,hPos⟩
  have hSingle : t i = (0 : Fin 1) := Subsingleton.elim _ _
  have hOld0 : e (0 : Fin 1) ∈ A.carrier := by
    by_contra hMissing
    have hNotAll : ¬ (∀ q, e (t q) ∈ A.carrier) := by
      intro hall
      exact hMissing (by simpa only [hSingle] using hall i)
    have hAtom := hCopy.2.2 s t
    have hFalse :
        (A.neutralExtension newCarrier).atom s (fun q => e (t q)) =
          false := by
      simp [ArityAge.neutralExtension, hNotAll]
    rw [hFalse,hPositive] at hAtom
    cases hAtom
  have hOld : ∀ a : Fin 1, e a ∈ A.carrier := by
    intro a
    have ha : a = 0 := Subsingleton.elim _ _
    simpa [ha] using hOld0
  refine ⟨hCopy.1,hOld,?_⟩
  intro rel tuple
  have hAll : ∀ j, e (tuple j) ∈ A.carrier := by
    intro j
    exact hOld (tuple j)
  have hAtom := hCopy.2.2 rel tuple
  simpa [ArityAge.neutralExtension,hAll] using hAtom

end SuccessorTree.V10

import Mathlib

namespace SuccessorTree.BANANA

/-- Coordinate inclusion of the first split extension into a three-way split. -/
def splitLeftB {a b c : Type*} : a ⊕ b → a ⊕ (b ⊕ c)
  | Sum.inl i => Sum.inl i
  | Sum.inr i => Sum.inr (Sum.inl i)

/-- Coordinate inclusion of the second split extension into a three-way split. -/
def splitLeftC {a b c : Type*} : a ⊕ c → a ⊕ (b ⊕ c)
  | Sum.inl i => Sum.inl i
  | Sum.inr i => Sum.inr (Sum.inr i)

theorem splitLeftB_injective {a b c : Type*} :
    Function.Injective (splitLeftB : a ⊕ b → a ⊕ (b ⊕ c)) := by
  intro x y h
  cases x <;> cases y <;> simp [splitLeftB] at h ⊢ <;> assumption

theorem splitLeftC_injective {a b c : Type*} :
    Function.Injective (splitLeftC : a ⊕ c → a ⊕ (b ⊕ c)) := by
  intro x y h
  cases x <;> cases y <;> simp [splitLeftC] at h ⊢ <;> assumption

/-- The split amalgam used in the BANANA strong-amalgamation proof.
The mixed complement blocks are set to zero. -/
def splitAmalgam {K lA lB lC rA rB rC : Type*} [Zero K]
    (A : Matrix lA rA K)
    (B : Matrix (lA ⊕ lB) (rA ⊕ rB) K)
    (C : Matrix (lA ⊕ lC) (rA ⊕ rC) K) :
    Matrix (lA ⊕ (lB ⊕ lC)) (rA ⊕ (rB ⊕ rC)) K
  | Sum.inl i, Sum.inl j => A i j
  | Sum.inl i, Sum.inr (Sum.inl j) => B (Sum.inl i) (Sum.inr j)
  | Sum.inl i, Sum.inr (Sum.inr j) => C (Sum.inl i) (Sum.inr j)
  | Sum.inr (Sum.inl i), Sum.inl j => B (Sum.inr i) (Sum.inl j)
  | Sum.inr (Sum.inr i), Sum.inl j => C (Sum.inr i) (Sum.inl j)
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) => B (Sum.inr i) (Sum.inr j)
  | Sum.inr (Sum.inr i), Sum.inr (Sum.inr j) => C (Sum.inr i) (Sum.inr j)
  | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => 0
  | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => 0

/-- The first old pairing is recovered exactly on its coordinate copy. -/
theorem splitAmalgam_restrict_B {K lA lB lC rA rB rC : Type*} [Zero K]
    (A : Matrix lA rA K)
    (B : Matrix (lA ⊕ lB) (rA ⊕ rB) K)
    (C : Matrix (lA ⊕ lC) (rA ⊕ rC) K)
    (hB : ∀ i j, B (Sum.inl i) (Sum.inl j) = A i j)
    (i : lA ⊕ lB) (j : rA ⊕ rB) :
    splitAmalgam A B C (splitLeftB i) (splitLeftB j) = B i j := by
  cases i <;> cases j <;> simp [splitAmalgam, splitLeftB, hB]

/-- The second old pairing is recovered exactly on its coordinate copy. -/
theorem splitAmalgam_restrict_C {K lA lB lC rA rB rC : Type*} [Zero K]
    (A : Matrix lA rA K)
    (B : Matrix (lA ⊕ lB) (rA ⊕ rB) K)
    (C : Matrix (lA ⊕ lC) (rA ⊕ rC) K)
    (hC : ∀ i j, C (Sum.inl i) (Sum.inl j) = A i j)
    (i : lA ⊕ lC) (j : rA ⊕ rC) :
    splitAmalgam A B C (splitLeftC i) (splitLeftC j) = C i j := by
  cases i <;> cases j <;> simp [splitAmalgam, splitLeftC, hC]

/-- Extend a vector in the first split extension by zero on the second complement. -/
def includeSplitB {K a b c : Type*} [Zero K]
    (x : a ⊕ b → K) : a ⊕ (b ⊕ c) → K
  | Sum.inl i => x (Sum.inl i)
  | Sum.inr (Sum.inl i) => x (Sum.inr i)
  | Sum.inr (Sum.inr _) => 0

/-- Extend a vector in the second split extension by zero on the first complement. -/
def includeSplitC {K a b c : Type*} [Zero K]
    (x : a ⊕ c → K) : a ⊕ (b ⊕ c) → K
  | Sum.inl i => x (Sum.inl i)
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr i) => x (Sum.inr i)

theorem includeSplitB_injective {K a b c : Type*} [Zero K] :
    Function.Injective (includeSplitB : (a ⊕ b → K) → a ⊕ (b ⊕ c) → K) := by
  intro x y h
  funext i
  cases i with
  | inl i =>
      exact congrFun h (Sum.inl i)
  | inr i =>
      exact congrFun h (Sum.inr (Sum.inl i))

theorem includeSplitC_injective {K a b c : Type*} [Zero K] :
    Function.Injective (includeSplitC : (a ⊕ c → K) → a ⊕ (b ⊕ c) → K) := by
  intro x y h
  funext i
  cases i with
  | inl i =>
      exact congrFun h (Sum.inl i)
  | inr i =>
      exact congrFun h (Sum.inr (Sum.inr i))

/-- The two coordinate copies intersect precisely in the common base.
This is the "strong" part of the split amalgamation construction. -/
theorem includeSplitB_eq_includeSplitC_iff {K a b c : Type*} [Zero K]
    (x : a ⊕ b → K) (y : a ⊕ c → K) :
    includeSplitB x = includeSplitC y ↔
      ∃ z : a → K, x = Sum.elim z 0 ∧ y = Sum.elim z 0 := by
  constructor
  · intro h
    let z : a → K := fun i => x (Sum.inl i)
    refine ⟨z, ?_, ?_⟩
    · funext i
      cases i with
      | inl i => rfl
      | inr i =>
          have hi := congrFun h (Sum.inr (Sum.inl i))
          simpa [includeSplitB, includeSplitC] using hi
    · funext i
      cases i with
      | inl i =>
          have hi := congrFun h (Sum.inl i)
          simpa [z, includeSplitB, includeSplitC] using hi.symm
      | inr i =>
          have hi := congrFun h (Sum.inr (Sum.inr i))
          simpa [includeSplitB, includeSplitC] using hi.symm
  · rintro ⟨z, rfl, rfl⟩
    funext i
    cases i with
    | inl i => rfl
    | inr i =>
        cases i <;> simp [includeSplitB, includeSplitC]

end SuccessorTree.BANANA

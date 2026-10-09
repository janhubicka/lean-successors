import SuccessorTree.V10.OriginalPoolEnvelope

/-!
# Canonical parameters and the maintained v10 original pool

This is the quantitative version of Observation 6.47(3) used by the
v10 repair. Instead of *assuming* that the pool is parameter-closed,
we isolate the only concrete successor statement needed:

* every parameter on a selected crossing at level i is below the
  canonical type of the original vertex i;
* such a parameter can occur only when the free level of i is positive.

Therefore, if the pool contains every canonical type at selected positive
free levels, its downward prefixes are parameter-closed. The previous
OriginalPoolEnvelope theorem then applies to the actual universal
closure of the manuscript.

The two bullets are not yet proved for the concrete KFpt successor
operation. They are required **only on the downward prefixes of the chosen
pool**, not on every partial type in the entire tree. They are packaged as one explicit hypothesis so that they
cannot be hidden inside a general "closedness" assertion.
-/

namespace SuccessorTree.V10

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]

/-- Concrete obligation on the successor representation, corresponding
to the positive-free-level part of Observation 6.47(3). -/
def CanonicalParameterRule
    (S : STree T Label) (I : Set Nat) (V : Set T)
    (free : Nat → Nat) (principal : Nat → T) : Prop :=
  ∀ ⦃a : T⦄, a ∈ prefixesOf V → ∀ ⦃i : Nat⦄, i ∈ I →
    ∀ (hi : i < LevelTree.lev a)
    ⦃p : List T⦄ ⦃c : Label⦄,
    S.succ
        (LevelTree.ancestor a i (Nat.le_of_lt hi)) p c =
      some (LevelTree.ancestor a (i + 1) (Nat.succ_le_iff.mpr hi)) →
    ∀ ⦃x : T⦄, x ∈ p →
      0 < free i ∧ x ≤ principal i

/-- The exact decomposition statement suggested by the manuscript's
one-parameter successor operation: for types represented by V, the
chosen crossing has either no parameter or the canonical singleton. -/
def CanonicalSuccessorDecomposition
    (S : STree T Label) (I : Set Nat) (V : Set T)
    (free : Nat → Nat) (principal : Nat → T) : Prop :=
  ∀ ⦃a : T⦄, a ∈ prefixesOf V → ∀ ⦃i : Nat⦄, i ∈ I →
    ∀ (hi : i < LevelTree.lev a)
    ⦃p : List T⦄ ⦃c : Label⦄,
    S.succ
        (LevelTree.ancestor a i (Nat.le_of_lt hi)) p c =
      some (LevelTree.ancestor a (i + 1) (Nat.succ_le_iff.mpr hi)) →
    (free i = 0 ∧ p = []) ∨
      (0 < free i ∧ p = [principal i])

/-- Unique empty/singleton decomposition is sufficient for the weaker,
pool-relative canonical-parameter rule. No global assertion about all
partial types is needed. -/
theorem canonicalRule_of_decomposition
    (S : STree T Label) (I : Set Nat) (V : Set T)
    (free : Nat → Nat) (principal : Nat → T)
    (hDecomp : CanonicalSuccessorDecomposition S I V free principal) :
    CanonicalParameterRule S I V free principal := by
  intro a ha i hi hia p c hstep x hx
  rcases hDecomp ha hi hia hstep with ⟨_, hp⟩ | ⟨hf, hp⟩
  · rw [hp] at hx
    simp at hx
  · rw [hp] at hx
    simp only [List.mem_singleton] at hx
    exact ⟨hf, le_of_eq hx⟩

/-- The Observation 6.47(3) condition on the chosen stage pool implies
parameter closure for all prefixes of that pool. -/
theorem canonicalRule_parameterClosed
    (S : STree T Label) (I : Set Nat) (V : Set T)
    (free : Nat → Nat) (principal : Nat → T)
    (hRule : CanonicalParameterRule S I V free principal)
    (hPrincipal : ∀ i ∈ I, 0 < free i → principal i ∈ prefixesOf V) :
    SMTree.Envelope.ParameterClosedOver S (prefixesOf V) I := by
  intro a ha i hi hia p c hstep x hx
  obtain ⟨hfree, hbelow⟩ := hRule ha hi hia hstep hx
  obtain ⟨v, hv, hvabove⟩ := hPrincipal i hi hfree
  exact ⟨v, hv, hbelow.trans hvabove⟩

/-- A direct stage invariant for the manuscript's closure operator.
Neither meet iteration nor a finitary closure equality is assumed. -/
theorem closure_subset_pool_of_canonicalRule
    (S : STree T Label) (I : Set Nat) (X V : Set T)
    (free : Nat → Nat) (principal : Nat → T)
    (hX : X ⊆ prefixesOf V)
    (hRule : CanonicalParameterRule S I V free principal)
    (hPrincipal : ∀ i ∈ I, 0 < free i → principal i ∈ V) :
    SMTree.Envelope.closure S I X ⊆ prefixesOf V := by
  have hparam : SMTree.Envelope.ParameterClosedOver S (prefixesOf V) I :=
    canonicalRule_parameterClosed S I V free principal hRule (by
      intro i hi hf
      exact ⟨principal i, hPrincipal i hi hf, le_rfl⟩)
  exact closure_subset_original_pool S I X V hX hparam

/-- The positive-meet provenance asserted in the reconstructed v10 proof.
The only unfinished concrete input is CanonicalParameterRule for KFpt. -/
theorem closure_positiveMeet_of_canonicalRule
    (S : STree T Label) (I : Set Nat) (X V : Set T)
    (free : Nat → Nat) (principal : Nat → T)
    (hX : X ⊆ prefixesOf V)
    (hRule : CanonicalParameterRule S I V free principal)
    (hPrincipal : ∀ i ∈ I, 0 < free i → principal i ∈ V)
    {a b : T}
    (ha : a ∈ SMTree.Envelope.closure S I X)
    (hb : b ∈ SMTree.Envelope.closure S I X)
    (hcommon : ∃ c : T, c ≤ a ∧ c ≤ b)
    (hleft : LevelTree.meet a b ≠ a)
    (hright : LevelTree.meet a b ≠ b) :
    ∃ p ∈ V, ∃ q ∈ V,
      (∃ c : T, c ≤ p ∧ c ≤ q) ∧
      LevelTree.meet a b = LevelTree.meet p q := by
  have hparam : SMTree.Envelope.ParameterClosedOver S (prefixesOf V) I :=
    canonicalRule_parameterClosed S I V free principal hRule (by
      intro i hi hf
      exact ⟨principal i, hPrincipal i hi hf, le_rfl⟩)
  exact closure_meet_has_originals S I X V hX hparam
    ha hb hcommon hleft hright

/-- The stage invariant follows directly from the manuscript's proposed
empty/singleton parameter description on the represented prefix pool. -/
theorem closure_subset_pool_of_decomposition
    (S : STree T Label) (I : Set Nat) (X V : Set T)
    (free : Nat → Nat) (principal : Nat → T)
    (hX : X ⊆ prefixesOf V)
    (hDecomp : CanonicalSuccessorDecomposition S I V free principal)
    (hPrincipal : ∀ i ∈ I, 0 < free i → principal i ∈ V) :
    SMTree.Envelope.closure S I X ⊆ prefixesOf V := by
  exact closure_subset_pool_of_canonicalRule S I X V free principal hX
    (canonicalRule_of_decomposition S I V free principal hDecomp) hPrincipal

end SuccessorTree.V10

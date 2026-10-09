import SuccessorTree.V10.CanonicalParameters

/-!
# Conditional exact parameter-closure criterion on a represented pool

Under the explicit empty/singleton crossing decomposition of a finite
ambient partial structure C, parameter-closedness of the represented
pool is equivalent to containing the canonical parameter whenever a
selected level with positive free index is actually crossed by that pool.

This is the full logical form of Observation 6.47(3), including
its qualification that the level lies below some member of Z.
The remaining obligation is to verify the crossing decomposition
for the actual KFpt successor; no additional axiom is introduced.
-/

namespace SuccessorTree.V10

universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]

/-- A chosen stage pool has a represented node strictly above level i. -/
def CrossesPool (V : Set T) (i : Nat) : Prop :=
  ∃ a ∈ prefixesOf V, i < LevelTree.lev a

/-- The exact empty/singleton successor-decomposition obligation can be
posed on any collection Z of partial types supported by a fixed ambient
structure C; no prefix-closure assumption on Z is required. -/
def CanonicalSuccessorDecompositionOn
    (S : STree T Label) (I : Set Nat) (Z : Set T)
    (free : Nat → Nat) (principal : Nat → T) : Prop :=
  ∀ ⦃a : T⦄, a ∈ Z → ∀ ⦃i : Nat⦄, i ∈ I →
    ∀ (hi : i < LevelTree.lev a)
    ⦃p : List T⦄ ⦃c : Label⦄,
    S.succ
        (LevelTree.ancestor a i (Nat.le_of_lt hi)) p c =
      some (LevelTree.ancestor a (i + 1) (Nat.succ_le_iff.mpr hi)) →
    (free i = 0 ∧ p = []) ∨
      (0 < free i ∧ p = [principal i])

/-- The literal iff in Observation 6.47(3) for *any* supported Z:
parameter closure requires the canonical type at each selected positive
free level which is below at least one node of Z. This theorem is
conditional on exact canonical decomposition, not a proof that every
abstract STree has this property. -/
theorem parameterClosed_iff_canonicalPrincipalOn
    (S : STree T Label) (I : Set Nat) (Z : Set T)
    (free : Nat → Nat) (principal : Nat → T)
    (hDecomp : CanonicalSuccessorDecompositionOn S I Z free principal) :
    SMTree.Envelope.ParameterClosedOver S Z I ↔
      ∀ i ∈ I, (∃ a ∈ Z, i < LevelTree.lev a) →
        0 < free i → principal i ∈ Z := by
  constructor
  · intro hClosed i hi hcross hfree
    obtain ⟨a, ha, hia⟩ := hcross
    let x := LevelTree.ancestor a i (Nat.le_of_lt hia)
    let y := LevelTree.ancestor a (i + 1) (Nat.succ_le_iff.mpr hia)
    have hxa : x ≤ a := LevelTree.ancestor_le a i (Nat.le_of_lt hia)
    have hya : y ≤ a :=
      LevelTree.ancestor_le a (i + 1) (Nat.succ_le_iff.mpr hia)
    have hxy : x ≤ y := by
      rcases LevelTree.comparable_below hxa hya with h | h
      · exact h
      · have hlev := LevelTree.level_le_of_le h
        have hxl : LevelTree.lev x = i := by
          simp [x, LevelTree.level_ancestor]
        have hyl : LevelTree.lev y = i + 1 := by
          simp [y, LevelTree.level_ancestor]
        omega
    have hyl : LevelTree.lev y = LevelTree.lev x + 1 := by
      simp [x, y, LevelTree.level_ancestor]
    have hcov : x ⋖ y := LevelTree.covBy_of_le_level_succ hxy hyl
    obtain ⟨p, c, hsucc⟩ := S.s3 hcov
    have hstep :
      S.succ (LevelTree.ancestor a i (Nat.le_of_lt hia)) p c =
        some (LevelTree.ancestor a (i + 1) (Nat.succ_le_iff.mpr hia)) := hsucc
    rcases hDecomp ha hi hia hstep with ⟨hf0, _⟩ | ⟨_, hp⟩
    · omega
    · have hx : principal i ∈ p := by
        rw [hp]
        simp
      exact hClosed ha hi hia hstep hx
  · intro hPrincipal
    intro a ha i hi hia p c hstep x hx
    rcases hDecomp ha hi hia hstep with ⟨_, hp⟩ | ⟨hf, hp⟩
    · rw [hp] at hx
      simp at hx
    · rw [hp] at hx
      simp only [List.mem_singleton] at hx
      rw [hx]
      exact hPrincipal i hi ⟨a, ha, hia⟩ hf

/-- The pool-prefix theorem is a convenient specialization of the general
conditional iff. It is kept as a stable interface for the envelope proof. -/
theorem parameterClosed_iff_canonicalPrincipal
    (S : STree T Label) (I : Set Nat) (V : Set T)
    (free : Nat → Nat) (principal : Nat → T)
    (hDecomp : CanonicalSuccessorDecomposition S I V free principal) :
    SMTree.Envelope.ParameterClosedOver S (prefixesOf V) I ↔
      ∀ i ∈ I, CrossesPool V i → 0 < free i →
        principal i ∈ prefixesOf V := by
  change SMTree.Envelope.ParameterClosedOver S (prefixesOf V) I ↔
    ∀ i ∈ I, (∃ a ∈ prefixesOf V, i < LevelTree.lev a) →
      0 < free i → principal i ∈ prefixesOf V
  exact parameterClosed_iff_canonicalPrincipalOn S I (prefixesOf V)
    free principal hDecomp

end SuccessorTree.V10

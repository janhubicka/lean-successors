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

/-- Observation 6.47(3) on downward prefixes, conditional only on
the exact empty/singleton crossing decomposition. -/
theorem parameterClosed_iff_canonicalPrincipal
    (S : STree T Label) (I : Set Nat) (V : Set T)
    (free : Nat → Nat) (principal : Nat → T)
    (hDecomp : CanonicalSuccessorDecomposition S I V free principal) :
    SMTree.Envelope.ParameterClosedOver S (prefixesOf V) I ↔
      ∀ i ∈ I, CrossesPool V i → 0 < free i →
        principal i ∈ prefixesOf V := by
  constructor
  · intro hClosed i hi hcross hfree
    obtain ⟨a, ha, hia⟩ := hcross
    let x := LevelTree.ancestor a i (Nat.le_of_lt hia)
    let y := LevelTree.ancestor a (i + 1) (Nat.succ_le_iff.mpr hia)
    have hxa : x ≤ a :=
      LevelTree.ancestor_le a i (Nat.le_of_lt hia)
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
    have hRule := canonicalRule_of_decomposition
      S I V free principal hDecomp
    obtain ⟨hfree, hbelow⟩ := hRule ha hi hia hstep hx
    obtain ⟨v, hv, hprincipal⟩ :=
      hPrincipal i hi ⟨a, ha, hia⟩ hfree
    exact ⟨v, hv, hbelow.trans hprincipal⟩

end SuccessorTree.V10

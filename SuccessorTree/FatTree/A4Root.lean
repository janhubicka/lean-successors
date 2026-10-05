import SuccessorTree.ShapeSplit

/-!
# The root-level dichotomy for fat-tree A4

M3 supplies immediate successors at every positive level.  At level zero
there are two possibilities.  If some admissible one-row map moves the root
level, shape splitting followed by canonical extension produces a genuine
one-level letter skipping zero.  Otherwise every one-row root approximation
is the identity.  This removes the need for a global pruning hypothesis in
fat-tree A4.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

variable (H : SMTree S)

/-- Moving a root-level one-row approximation produces a genuine one-level
letter at level zero. -/
theorem exists_rootLetter_of_topLevel_pos
    (g : AM H 0 1) (hg : 0 < g.topLevel H) :
    Nonempty (OneLevelLetter H 0) := by
  obtain ⟨G, hGfix, hGtop, hGle⟩ :=
    exists_truncate_moving_level H
      (g.representative H) 0 1
      g.representative_fixesBelow
      (by omega) (by omega)
  let C : MMap H := H.canonicalExtension G 0
  have hformula :
      ∀ k : Nat, H.levelMap C.map k = k + 1 := by
    intro k
    have h :=
      H.canonicalExtension_level_tail G 0 k
    change H.levelMap C.map (0 + k) =
      H.levelMap G.map 0 + k at h
    rw [hGtop] at h
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hskip : C.map.SkipsOnly 0 := by
    unfold ShapeMap.SkipsOnly
    rw [← H.range_levelMap C.map]
    ext k
    constructor
    · rintro ⟨j, hj⟩
      have hf := hformula j
      rw [hj] at hf
      change k ≠ 0
      omega
    · intro hk
      change k ≠ 0 at hk
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      refine ⟨k - 1, ?_⟩
      rw [hformula]
      omega
  exact ⟨⟨C, hskip⟩⟩

/-- If no level-zero letter exists, every admissible one-row approximation
based at the root is the identity approximation. -/
theorem rootRow_eq_id1_of_no_rootLetter
    (hno : ¬ Nonempty (OneLevelLetter H 0))
    (g : AM H 0 1) :
    g = AM.id1 H 0 := by
  apply AM.eq_id1_of_topLevel_le H
  by_contra htop
  have hpos : 0 < g.topLevel H := by omega
  exact hno (H.exists_rootLetter_of_topLevel_pos g hpos)

/-- Equivalently, a nontrivial root row forces a level-zero letter. -/
theorem nontrivial_rootRow_implies_rootLetter
    (g : AM H 0 1)
    (hne : g ≠ AM.id1 H 0) :
    Nonempty (OneLevelLetter H 0) := by
  by_contra hno
  exact hne (H.rootRow_eq_id1_of_no_rootLetter hno g)

end SMTree
end SuccessorTree

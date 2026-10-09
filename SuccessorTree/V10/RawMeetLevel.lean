import SuccessorTree.V10.RawTypeMeet
import SuccessorTree.V10.CommonSocleType

/-!
# Exact level of a concrete partial-type meet

This closes the local finite-record bridge from a first directed-binary
difference to the MEET LEVEL, without assuming any abstract tree meet.

Let two vertices v,w come from the same ambient partial structure,
have the same full level-zero root type, and let d+1 be below both
E free levels. If the incoming/outgoing binary traces agree before d
but differ at d, then their *greatest common complete L+ prefix*
has level exactly d.

All unary, diagonal, socle-internal and E atoms are part of the
raw finite records and of the greatest-prefix universal property.

This still does not assert that every raw finite record is a node of
the forbidden-free Kpt tree. That final admissible-family/prefix-closed
representation step is explicitly separate.
-/

namespace SuccessorTree.V10

/-- Under a first binary difference below both free cuts, the unique
greatest common raw partial-type prefix has cut exactly d. -/
theorem rawPartialType_meet_level_of_first_binary_difference
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v w d : Nat)
    (hv : d + 1 ≤ A.freeLevel v)
    (hw : d + 1 ≤ A.freeLevel w)
    (hroot : A.partialTypeAt 0 v = A.partialTypeAt 0 w)
    (hBefore : SameAmbientCrossType A v w d)
    (hDiff :
      (∃ r : Fin db, A.L.binary d v r ≠ A.L.binary d w r) ∨
      (∃ r : Fin db, A.L.binary v d r ≠ A.L.binary w d r)) :
    ∃ m : RawPartialTypeNode db du dd,
      m.1 = d ∧
      RawPartialTypePrefix m (A.rawTypeAtFree v) ∧
      RawPartialTypePrefix m (A.rawTypeAtFree w) ∧
      (∀ q : RawPartialTypeNode db du dd,
        RawPartialTypePrefix q (A.rawTypeAtFree v) →
        RawPartialTypePrefix q (A.rawTypeAtFree w) →
        RawPartialTypePrefix q m) := by
  obtain ⟨hEqD, hDiffNext⟩ :=
    sameAmbient_first_fullType_difference
      A v w d hv hw hroot hBefore hDiff
  obtain ⟨m, hmV, hmW, hGreatest⟩ :=
    rawPartialTypes_have_greatest_common_prefix A v w hroot
  let candidate : RawPartialTypeNode db du dd :=
    ⟨d, A.partialTypeAt d v⟩
  have hCandidateV :
      RawPartialTypePrefix candidate (A.rawTypeAtFree v) :=
    rawPartialType_prefix_of_cut A v d (by omega)
  have hCandidateW :
      RawPartialTypePrefix candidate (A.rawTypeAtFree w) := by
    have hdw : d ≤ A.freeLevel w := by omega
    refine ⟨hdw, ?_⟩
    calc
      A.partialTypeAt d v = A.partialTypeAt d w := hEqD
      _ = (A.partialTypeAt (A.freeLevel w) w).restrict
            hdw :=
        (A.partialTypeAt_restrict d (A.freeLevel w) w hdw).symm
  obtain ⟨hdm, _⟩ :=
    hGreatest candidate hCandidateV hCandidateW
  have hmd : m.1 ≤ d := by
    by_contra hnot
    have hlt : d + 1 ≤ m.1 := by omega
    obtain ⟨hMv, hMvEq⟩ := hmV
    obtain ⟨hMw, hMwEq⟩ := hmW
    have hMTypeV : m.2 = A.partialTypeAt m.1 v := by
      calc
        m.2 = (A.partialTypeAt (A.freeLevel v) v).restrict
            hMv := hMvEq
        _ = A.partialTypeAt m.1 v :=
            A.partialTypeAt_restrict m.1 (A.freeLevel v) v hMv
    have hMTypeW : m.2 = A.partialTypeAt m.1 w := by
      calc
        m.2 = (A.partialTypeAt (A.freeLevel w) w).restrict
            hMw := hMwEq
        _ = A.partialTypeAt m.1 w :=
            A.partialTypeAt_restrict m.1 (A.freeLevel w) w hMw
    have hEqM : A.partialTypeAt m.1 v =
        A.partialTypeAt m.1 w :=
      hMTypeV.symm.trans hMTypeW
    exact hDiffNext (fullPartialType_eq_at_smaller A v w
      (d + 1) m.1 hlt hEqM)
  change d ≤ m.1 at hdm
  exact ⟨m, Nat.le_antisymm hmd hdm, hmV, hmW, hGreatest⟩

end SuccessorTree.V10

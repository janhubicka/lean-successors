import SuccessorTree.V10.M2TwoTypeFreeAge
import Mathlib.Tactic

namespace SuccessorTree.V10

/-- The first distinguished vertex carries exactly the complete first L type. -/
theorem twoTypeFreeAge_first_type {n db du dd : Nat}
    (T U : PartialTypeWithE n db du dd) :
    RelationalPrefixType.ofAgeModel (twoTypeFreeAge T U) n n = T.lReduct := by
  apply RelationalPrefixType.eq_of_atoms
  · intro a b t
    cases a with
    | none =>
      cases b with
      | none => simp [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex]
      | some j =>
        have hj : j.val < n := j.isLt
        have hn : n ≠ n + 1 := by omega
        have hjne : j.val ≠ n + 1 := by omega
        simp [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex, hj, hn, hjne]
    | some i =>
      have hi : i.val < n := i.isLt
      have hine : i.val ≠ n + 1 := by omega
      cases b with
      | none =>
        have hn : n ≠ n + 1 := by omega
        simp [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex, hi, hine, hn]
      | some j =>
        have hj : j.val < n := j.isLt
        have hjne : j.val ≠ n + 1 := by omega
        simp [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex, hi, hj, hine, hjne]
  · intro a t
    cases a with
    | none =>
      have hn : n ≠ n + 1 := by omega
      simp [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex, hn]
    | some i =>
      have hi : i.val < n := i.isLt
      have hine : i.val ≠ n + 1 := by omega
      simp [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex, hi, hine]
  · intro a t
    cases a with
    | none =>
      have hn : n ≠ n + 1 := by omega
      simp [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex, hn]
    | some i =>
      have hi : i.val < n := i.isLt
      have hine : i.val ≠ n + 1 := by omega
      simp [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex, hi, hine]

/-- The second distinguished vertex carries the complete second L type;
all ordinary-ordinary atoms agree because the two inputs are compatible. -/
theorem twoTypeFreeAge_second_type {n db du dd : Nat}
    (T U : PartialTypeWithE n db du dd)
    (hComp : SameOrdinaryAtCut T U) :
    RelationalPrefixType.ofAgeModel (twoTypeFreeAge T U) n (n+1) = U.lReduct := by
  apply RelationalPrefixType.eq_of_atoms
  · intro a b t
    cases a with
    | none =>
      cases b with
      | none =>
        simp [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex]
      | some j =>
        have hj : j.val < n := j.isLt
        have hjne : j.val ≠ n := by omega
        simp [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex, hj, hjne]
    | some i =>
      have hi : i.val < n := i.isLt
      have hine : i.val ≠ n+1 := by omega
      have hine0 : i.val ≠ n := by omega
      cases b with
      | none =>
        simp [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex, hi, hine, hine0]
      | some j =>
        have hj : j.val < n := j.isLt
        have hjne : j.val ≠ n+1 := by omega
        simpa [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex, hi, hj, hine, hjne]
          using (hComp.1 i j t)
  · intro a t
    cases a with
    | none =>
      simp [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex]
    | some i =>
      have hi : i.val < n := i.isLt
      have hine : i.val ≠ n+1 := by omega
      simpa [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex, hi, hine]
        using (hComp.2.1 i t)
  · intro a t
    cases a with
    | none =>
      simp [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex]
    | some i =>
      have hi : i.val < n := i.isLt
      have hine : i.val ≠ n+1 := by omega
      simpa [RelationalPrefixType.ofAgeModel, prefixVertexIndex, twoTypeFreeAge, typeAgeIndex, hi, hine]
        using (hComp.2.2.1 i t)

end SuccessorTree.V10
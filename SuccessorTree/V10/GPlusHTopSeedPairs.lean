import SuccessorTree.V10.HTopRootStrictPrefix
import SuccessorTree.V10.HTopGenerationSeeds
import SuccessorTree.V10.GPlusRepresentingPairs
import Mathlib.Tactic

/-!
# V10 Definition 6.43: the actual numerical HTop seeds represent G+ vertices

The concrete HTopGenerationSeeds construction has ONE genuine original
Kpt type U at root c, together with its ancestors at selected real
top-generation coordinates d_i=hPosition k i k.

If each d_i+1 lies under U's genuine free E cut (verified at the
numerical top root by HTopRootStrictPrefix), the strict pair
  (ancestor U d_i, U)
is an ACTUAL Kpt representing pair with BOTH endpoints in the literal
Algorithm 5.4 seed set.

Its G+ vertex is exactly the full on-carrier code of the initial
H+ partial structure on d_i+1 vertices. This equality contains every
directed binary, unary, diagonal and auxiliary E atom including false
values; it does not assume any E relation on the original L-only
forbidden-age test witness.

This proves the exact missing GEOMETRIC SEED REPRESENTATION needed
to apply the already checked AlgorithmRun-to-G+ coverage theorem.
The numerical bound and finite palette remain independently checked;
the next step must reconcile the precise finite approximant domain
and the final colouring stabilization.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- For a selected top coordinate strictly inside the genuine root
free cut, BOTH Kpt endpoints of its G+ representing pair are literally
members of the actual HTopGenerationSeeds. The represented vertex is
the exact finite H+ initial code through that coordinate. -/
theorem numericHTopSeed_represents_GPlus_prefix
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat)
    (hAvoidH : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N))
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (hStrict : ∀ i : Nat, i ∈ blocks →
      hPosition k i k + 1 ≤ (finiteNumericH K k N).freeLevel c.val)
    (i : Nat) (hi : i ∈ blocks) :
    let A := finiteNumericH K k N
    let d := hPosition k i k
    let X := numericHTopGenerationSeeds family K k N
      hAvoidH c blocks hWithin
    ∃ (hSize : d+1 ≤ A.size) (P : GPlusRepresentingPair family),
      P.lower ∈ X ∧ P.upper ∈ X ∧
      P.vertex.val =
        FinitePartialCode.ofEnumerated (A.initialSegment (d+1) hSize) := by
  classical
  let A := finiteNumericH K k N
  let d := hPosition k i k
  let U : AdmissibleKptNode family := A.kptOriginal family hAvoidH c
  let m := A.freeLevel c.val
  have hStrictRoot : d+1 ≤ m := hStrict i hi
  have hdRoot : d ≤ m := by omega
  have hRootLevel : LevelTree.lev U = m := rfl
  have hdU : d ≤ LevelTree.lev U := by
    rw [hRootLevel]
    exact hdRoot
  let S := LevelTree.ancestor U d hdU
  have hSLe : S ≤ U := LevelTree.ancestor_le U d hdU
  have hSLevel : LevelTree.lev S = d :=
    LevelTree.level_ancestor U d hdU
  have hUStrict : d < LevelTree.lev U := by
    rw [hRootLevel]
    omega
  have hNe : S ≠ U := by
    intro hEq
    have hh := congrArg LevelTree.lev hEq
    rw [hSLevel] at hh
    omega
  let P : GPlusRepresentingPair family :=
    ⟨S,U,lt_of_le_of_ne hSLe hNe⟩
  have hCut : P.cut = d+1 := by
    change LevelTree.lev S+1 = d+1
    rw [hSLevel]
  have hPU : P.representedNode ≤ U :=
    admissibleKptAncestor_le U P.cut P.cut_le_upper
  have hRaw :
      P.representedNode.1 =
      (⟨P.cut, A.partialTypeAt P.cut c.val⟩ :
        RawPartialTypeNode db du dd) :=
    kpt_prefix_raw_eq_ambient A family hAvoidH c P.representedNode hPU
  have hSize : d+1 ≤ A.size := by
    have hFree : m ≤ c.val := A.freeLevel_le c.val
    have hc : c.val < A.size := c.isLt
    omega
  have hUpperSeed :
      U ∈ numericHTopGenerationSeeds
        family K k N hAvoidH c blocks hWithin := by
    unfold numericHTopGenerationSeeds
    exact Finset.mem_insert_self _ _
  have hLowerSeed :
      S ∈ numericHTopGenerationSeeds
        family K k N hAvoidH c blocks hWithin := by
    unfold numericHTopGenerationSeeds
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨(⟨i,hi⟩ : {j : Nat // j ∈ blocks}), by simp, ?_⟩
    rfl
  dsimp only
  refine ⟨hSize,P,hLowerSeed,hUpperSeed,?_⟩
  calc
    P.vertex.val =
        RawPartialTypeNode.ordinaryCode P.representedNode.1 :=
      P.vertex_code
    _ = RawPartialTypeNode.ordinaryCode
        (⟨d+1,A.partialTypeAt (d+1) c.val⟩ :
          RawPartialTypeNode db du dd) := by
      rw [hRaw,hCut]
    _ = FinitePartialCode.ofEnumerated
          (A.initialSegment (d+1) hSize) :=
      (A.initialSegment_code_eq_ordinaryCode (d+1) c.val hSize).symm

end SuccessorTree.V10

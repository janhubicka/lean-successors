import SuccessorTree.V10.PrescribedMatchingFinite
import SuccessorTree.V10.PrescribedB3Spacing
import Mathlib.Tactic

/-!
# The manuscript's corrected B3 is exactly the finite L-age test

The repaired B3 is a condition on the prescribed partial function f
alone. Its witnesses are finite ordered L-structures with the ordinary
initial socle of some f(S0) and upper types in the L-reducts of f[S].
No auxiliary E condition is imposed on those L-age witnesses.

This module identifies the precise Boolean L-socle encoded by an
admissible f(S0) record, proves it coincides with ANY genuine ambient
partial-structure witness of that record, and derives the conditional
witness-based CommonSocleAgeTest used by the already constructed finite
prescribed insertion. Thus the corrected source condition really
discharges the remaining *finite* B3 premise.

The global choice-independent prescribed Kpt ShapeMap, plus the separate
M2/M3 uses of B3, still require proofs.
-/

namespace SuccessorTree.V10

/-- Every full L+ record at level ell+1 determines a finite ordinary
L-socle on 0,...,ell, independently of its type vertex and of E. -/
def prescribedOrdinarySocle
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell+1) db du dd) :
    AgeTestModel db du dd where
  carrier := {x | x ≤ ell}
  binary := fun x y t =>
    if hx : x ≤ ell then
      if hy : y ≤ ell then
        Q.lReduct.binary
          (some (⟨x, by omega⟩ : Fin (ell+1)))
          (some (⟨y, by omega⟩ : Fin (ell+1))) t
      else false
    else false
  unary := fun x t =>
    if hx : x ≤ ell then
      Q.lReduct.unary (some (⟨x, by omega⟩ : Fin (ell+1))) t
    else false
  diagonal := fun x t =>
    if hx : x ≤ ell then
      Q.lReduct.diagonal (some (⟨x, by omega⟩ : Fin (ell+1))) t
    else false

/-- Literal B3 in the repaired lemma: a bounded finite L-witness whose
first ell+1 vertices induce the ordinary L-socle of some f(S0), and whose
upper L-types are in f[S], cannot introduce a new forbidden copy only
using ell. Its stated input is the prescribed f, not a chosen E-witness. -/
def PrescribedBoringData.CorrectedB3
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd)) : Prop :=
  ∀ S0, S0 ∈ F.source →
    CommonSocleAgeTest family
      (prescribedOrdinarySocle (F.target S0)) ell
      F.PrescribedUpperLType

/-- Being the same induced L-socle through ell is transitive. The upper
vertices and E-values outside that initial socle are irrelevant. -/
theorem SameInitialL.trans
    {db du dd : Nat}
    {A B C : AgeTestModel db du dd} {ell : Nat}
    (hAB : SameInitialL A B ell)
    (hBC : SameInitialL B C ell) :
    SameInitialL A C ell := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hAB.1 x hx).trans (hBC.1 x hx)
  · intro x y hx hy t
    exact (hAB.2.1 x y hx hy t).trans (hBC.2.1 x y hx hy t)
  · intro x hx t
    exact (hAB.2.2.1 x hx t).trans (hBC.2.2.1 x hx t)
  · intro x hx t
    exact (hAB.2.2.2 x hx t).trans (hBC.2.2.2 x hx t)

/-- If a genuine finite partial structure W realizes Q through ell+1,
its ordinary L-socle is exactly the socle decoded from Q, including
carrier membership, all directed positive/negative binary atoms and
all singleton unary/diagonal values. -/
theorem prescribedOrdinarySocle_matches_witness
    {ell db du dd : Nat}
    (W : EnumeratedPartialStructure db du dd)
    (w : Nat) (Q : PartialTypeWithE (ell+1) db du dd)
    (hSize : ell < W.size)
    (hQ : Q = W.partialTypeAt (ell+1) w) :
    SameInitialL W.L (prescribedOrdinarySocle Q) ell := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    constructor
    · intro _
      change x ≤ ell
      exact hx
    · intro _
      exact (W.carrier_iff x).2 (by omega)
  · intro x y hx hy t
    have hh : W.L.binary x y t =
        (W.partialTypeAt (ell+1) w).lReduct.binary
          (some (⟨x,by omega⟩ : Fin (ell+1)))
          (some (⟨y,by omega⟩ : Fin (ell+1))) t := rfl
    rw [←hQ] at hh
    simpa [prescribedOrdinarySocle,hx,hy] using hh
  · intro x hx t
    have hh : W.L.unary x t =
        (W.partialTypeAt (ell+1) w).lReduct.unary
          (some (⟨x,by omega⟩ : Fin (ell+1))) t := rfl
    rw [←hQ] at hh
    simpa [prescribedOrdinarySocle,hx] using hh
  · intro x hx t
    have hh : W.L.diagonal x t =
        (W.partialTypeAt (ell+1) w).lReduct.diagonal
          (some (⟨x,by omega⟩ : Fin (ell+1))) t := rfl
    rw [←hQ] at hh
    simpa [prescribedOrdinarySocle,hx] using hh

/-- The corrected finite L-age B3 condition implies the witness-based
finite test used by the prescribed insertion proof. This does not require
anything about E on arbitrary L-age witnesses. -/
theorem PrescribedBoringData.correctedB3_to_witness_test
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (S0 : PartialTypeWithE ell db du dd)
    (hS0 : S0 ∈ F.source)
    (W : EnumeratedPartialStructure db du dd)
    (w : Nat)
    (hSize : ell < W.size)
    (hQ : F.target S0 = W.partialTypeAt (ell+1) w) :
    CommonSocleAgeTest family W.L ell
      F.PrescribedUpperLType := by
  have hSocle := prescribedOrdinarySocle_matches_witness W w
      (F.target S0) hSize hQ
  intro V hFinite hSame hUpper hDelete bad hBad
  have hMatched : SameInitialL V
      (prescribedOrdinarySocle (F.target S0)) ell :=
    hSame.trans hSocle
  exact hB3 S0 hS0 V hFinite hMatched hUpper hDelete bad hBad

/-- The source-level B3 hypothesis can now be used DIRECTLY to obtain
the forbidden-free finite matching-socle insertion. The earlier witness-
dependent hB3 assumption is discharged from admissibility of f(S0). -/
theorem PrescribedBoringData.matching_insertion_of_correctedB3
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (A : EnumeratedPartialStructure db du dd)
    (base : Nat)
    (S0 : PartialTypeWithE ell db du dd)
    (hS0 : S0 ∈ F.source)
    (hComp : SameOrdinaryAtCut S0 (A.partialTypeAt ell base))
    (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hTargetAd : IsAdmissibleRawType family
      (⟨ell+1,F.target S0⟩ : RawPartialTypeNode db du dd)) :
    ∃ B : EnumeratedPartialStructure db du dd,
      (∀ bad, bad ∈ family → bad.Avoids B.L) ∧
      IsLInsertion A B ell ∧
      (∀ u, u < A.size →
        B.freeLevel (insertAddress ell u) =
          if A.freeLevel u < ell then A.freeLevel u
          else A.freeLevel u + 1) := by
  apply F.matching_prescribed_insertion_exists family A base S0
    hS0 hComp hell hellPos hAvoidA hTargetAd
  intro W w hQ _
  have hE : W.E ell w = true := by
    have he := admissible_level_succ_has_last_E
      family ell (F.target S0) hTargetAd
    rw [hQ] at he
    change W.E ell w = true at he
    exact he
  have hSize : ell < W.size := (W.E_inside ell w hE).1
  exact F.correctedB3_to_witness_test family hB3 S0 hS0
    W w hSize hQ

end SuccessorTree.V10

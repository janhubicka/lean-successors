import SuccessorTree.V10.M3TotalPrescription
import SuccessorTree.V10.M3CanonicalCloneLetter
import Mathlib.Tactic

/-!
# Corrected finite L-age B3 for the ACTUAL total M3 prescription

The total M3 source function was built by selecting a genuine finite
forbidden-free partial structure A,v for each admissible level-ell
source. The actual gated insertion B copies the old ordinary n into
new coordinate ell.

Its ordinary output socle has exactly the lower clone L-atoms.
For every prescribed upper type, the complete terminal Sigma letter
repeats the earlier n-th letter, and B1 retains the old n-to-type
pairs. Thus each prescribed upper L-type copies BOTH directed
(ell,t) pairs from (n,t), including false atoms.

The independently verified finite irreducible clone projection
applies to ANY bounded finite ordered L-witness, with NO E
structure on that witness. The old clone cut may depend on the
source socle. This proves the actual corrected B3 premise needed
by the already checked prescribed boring extension.
-/

namespace SuccessorTree.V10

/-- Every old ordinary singleton in the first ell+1 coordinates of
a genuine extracted type has exactly its ambient L data. -/
theorem prescribedSocle_extracted_unary
    {db du dd : Nat}
    (B : EnumeratedPartialStructure db du dd)
    (ell v x : Nat) (hx : x ≤ ell) (t : Fin du) :
    (prescribedOrdinarySocle (B.partialTypeAt (ell+1) v)).unary x t =
      B.L.unary x t := by
  simp [prescribedOrdinarySocle, hx,
    RelationalPrefixType.ofAgeModel, prefixVertexIndex]

theorem prescribedSocle_extracted_diagonal
    {db du dd : Nat}
    (B : EnumeratedPartialStructure db du dd)
    (ell v x : Nat) (hx : x ≤ ell) (t : Fin dd) :
    (prescribedOrdinarySocle (B.partialTypeAt (ell+1) v)).diagonal x t =
      B.L.diagonal x t := by
  simp [prescribedOrdinarySocle, hx,
    RelationalPrefixType.ofAgeModel, prefixVertexIndex]

theorem prescribedSocle_extracted_binary
    {db du dd : Nat}
    (B : EnumeratedPartialStructure db du dd)
    (ell v x y : Nat) (hx : x ≤ ell) (hy : y ≤ ell)
    (t : Fin db) :
    (prescribedOrdinarySocle (B.partialTypeAt (ell+1) v)).binary x y t =
      B.L.binary x y t := by
  simp [prescribedOrdinarySocle, hx, hy,
    RelationalPrefixType.ofAgeModel, prefixVertexIndex]

/-- The actual finite M3 output has the full lower ordinary clone
column with the unique free cut of the old vertex n. This is a
finite L-only statement, not an E-age assumption. -/
theorem m3FiniteTarget_lower_clone
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell)
    (T : PartialTypeWithE ell db du dd)
    (hT : IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd)) :
    let W := chooseM3Witness family T hT
    MiddleCloneInitialL
      (prescribedOrdinarySocle (m3FiniteTarget family n hn T hT))
      n ell (W.A.freeLevel n) := by
  let W := chooseM3Witness family T hT
  let B := middleCloneInsertPartial W.A ell n W.ell_le_size hn
  let q := insertAddress ell W.v
  let Q := B.partialTypeAt (ell+1) q
  have hQ : m3FiniteTarget family n hn T hT = Q := rfl
  have hLinked : MiddleCloneLinkedLData B.L n ell (W.A.freeLevel n) :=
    middleCloneInsertPartial_linkedLData W.A ell n W.ell_le_size hn
  rw [hQ]
  refine {
    n_before := hLinked.n_before
    cut_le_source := hLinked.cut_before_source
    source_in_carrier := ?_
    same_unary := ?_
    same_diagonal := ?_
    no_lower_links := ?_
    copy_lower := ?_ }
  · change n ≤ ell
    omega
  · intro t
    calc
      (prescribedOrdinarySocle Q).unary ell t = B.L.unary ell t :=
        prescribedSocle_extracted_unary B ell q ell le_rfl t
      _ = B.L.unary n t := hLinked.same_unary t
      _ = (prescribedOrdinarySocle Q).unary n t :=
        (prescribedSocle_extracted_unary B ell q n
          (Nat.le_of_lt hn) t).symm
  · intro t
    calc
      (prescribedOrdinarySocle Q).diagonal ell t =
          B.L.diagonal ell t :=
        prescribedSocle_extracted_diagonal B ell q ell le_rfl t
      _ = B.L.diagonal n t := hLinked.same_diagonal t
      _ = (prescribedOrdinarySocle Q).diagonal n t :=
        (prescribedSocle_extracted_diagonal B ell q n
          (Nat.le_of_lt hn) t).symm
  · intro x hdx hxe t
    have hxle : x ≤ ell := Nat.le_of_lt hxe
    obtain ⟨hOut,hIn⟩ := hLinked.no_lower_links x hdx hxe t
    constructor
    · calc
        (prescribedOrdinarySocle Q).binary ell x t =
            B.L.binary ell x t :=
          prescribedSocle_extracted_binary B ell q ell x le_rfl hxle t
        _ = false := hOut
    · calc
        (prescribedOrdinarySocle Q).binary x ell t =
            B.L.binary x ell t :=
          prescribedSocle_extracted_binary B ell q x ell hxle le_rfl t
        _ = false := hIn
  · intro x hx t
    have hxle : x ≤ ell := by
      have hCut := hLinked.cut_before_source
      omega
    obtain ⟨hOut,hIn⟩ := hLinked.copy_lower x hx t
    constructor
    · calc
        (prescribedOrdinarySocle Q).binary ell x t =
            B.L.binary ell x t :=
          prescribedSocle_extracted_binary B ell q ell x le_rfl hxle t
        _ = B.L.binary n x t := hOut
        _ = (prescribedOrdinarySocle Q).binary n x t :=
          (prescribedSocle_extracted_binary B ell q n x
            (Nat.le_of_lt hn) hxle t).symm
    · calc
        (prescribedOrdinarySocle Q).binary x ell t =
            B.L.binary x ell t :=
          prescribedSocle_extracted_binary B ell q x ell hxle le_rfl t
        _ = B.L.binary x n t := hIn
        _ = (prescribedOrdinarySocle Q).binary x n t :=
          (prescribedSocle_extracted_binary B ell q x n hxle
            (Nat.le_of_lt hn) t).symm

/-- The actual selected M3 target repeats the old nth terminal
letter in its COMPLETE L+ record, not just in its L-reduct. -/
theorem m3FiniteTarget_terminalLetter
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell)
    (T : PartialTypeWithE ell db du dd)
    (hT : IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd)) :
    (m3FiniteTarget family n hn T hT).terminalLetter =
      earlierTerminalLetter T n hn := by
  let W := chooseM3Witness family T hT
  have hRecord : T = W.A.partialTypeAt ell W.v :=
    record_eq_of_rawTypeAtFree T W.A W.v W.raw_eq
  have hOld : earlierTerminalLetter T n hn =
      (W.A.partialTypeAt (n+1) W.v).terminalLetter := by
    unfold earlierTerminalLetter
    rw [hRecord]
    rw [W.A.partialTypeAt_restrict (n+1) ell W.v
      (Nat.succ_le_of_lt hn)]
  change ((middleCloneInsertPartial W.A ell n W.ell_le_size hn)
    .partialTypeAt (ell+1) (insertAddress ell W.v)).terminalLetter =
      earlierTerminalLetter T n hn
  exact (middleCloneInsertPartial_terminalLetter_eq W.A ell n
    W.ell_le_size hn W.v W.hv W.freeLevel_eq).trans hOld.symm

/-- The selected total target, on any admissible source, is exactly
the actual chosen finite M3 insertion. Its value outside the
admissible source is irrelevant. -/
theorem m3TotalBoringData_target_eq
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell)
    (T : PartialTypeWithE ell db du dd)
    (hT : T ∈ (m3TotalBoringData family ell n hn).source) :
    (m3TotalBoringData family ell n hn).target T =
      m3FiniteTarget family n hn T hT := by
  change IsAdmissibleRawType family
    (⟨ell,T⟩ : RawPartialTypeNode db du dd) at hT
  change (if hh : IsAdmissibleRawType family
    (⟨ell,T⟩ : RawPartialTypeNode db du dd) then
      m3FiniteTarget family n hn T hh
    else m3UnusedTarget ell db du dd) =
    m3FiniteTarget family n hn T hT
  rw [dif_pos hT]

/-- The actual total M3 prescribed source satisfies the manuscript's
CORRECTED B3 over arbitrary finite ordered L-age witnesses.
This does not add E to those witnesses or postulate age avoidance.
The irreducible clone projection is the proof. -/
theorem m3TotalBoringData_correctedB3
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell) :
    (m3TotalBoringData family ell n hn).CorrectedB3 family := by
  let F := m3TotalBoringData family ell n hn
  have hUpper : F.MiddleCloneUpperL n hn := by
    intro T hT t
    have hOld : (F.target T).restrict (Nat.le_succ ell) = T :=
      F.extendsSource T hT
    have hLetter : (F.target T).terminalLetter =
        earlierTerminalLetter T n hn := by
      rw [m3TotalBoringData_target_eq family n hn T hT]
      exact m3FiniteTarget_terminalLetter family n hn T hT
    exact m3_terminalLetter_copies_upper_pairs T (F.target T)
      n hn hOld hLetter t
  have hLower : ∀ T, T ∈ F.source →
      ∃ d : Nat, MiddleCloneInitialL
        (prescribedOrdinarySocle (F.target T)) n ell d := by
    intro T hT
    let W := chooseM3Witness family T hT
    refine ⟨W.A.freeLevel n, ?_⟩
    rw [m3TotalBoringData_target_eq family n hn T hT]
    exact m3FiniteTarget_lower_clone family n hn T hT
  intro S0 hS0
  obtain ⟨d,hData⟩ := hLower S0 hS0
  intro W hFinite hSocle hPrescribed hDelete
  have hClone : MiddleCloneLData W n ell d :=
    F.middleCloneLData_of_age_witness n d hn
      (prescribedOrdinarySocle (F.target S0)) W
      hData hUpper hSocle hPrescribed
  exact hClone.avoidance_of_deletion family hDelete

end SuccessorTree.V10

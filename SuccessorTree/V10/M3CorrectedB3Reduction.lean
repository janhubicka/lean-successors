import SuccessorTree.V10.M3CloneProjection
import SuccessorTree.V10.PrescribedCorrectedB3
import Mathlib.Tactic

/-!
# Reduction of corrected M3-B3 to literal clone atoms

The earlier finite projection argument is an L-only statement about a
genuine middle duplicate. Here we separate the two pieces of data
provided by the proposed M3 prescription:

* the common ordinary L-socle has a duplicate of old n at ell, with
  lower links copied only below a cut d <= n;
* every prescribed upper type copies both directed terminal pairs
  (ell,t) from the earlier ordinary coordinate (n,t).

Together these imply the corrected finite common-socle age test B3:
any forbidden copy involving ell can be projected to the old n and
therefore already appears after deleting ell. The argument imposes
NO auxiliary E predicate on the arbitrary finite L-age witness.

This is not yet a proof for the specific manuscript M3 function:
the canonical successor -> two concrete clone identities is a
separate, explicitly open adapter.
-/

namespace SuccessorTree.V10

/-- Lower L-atoms of a duplicate inserted at ell in a named ordinary
output socle. Both directed binary values, including absent edges,
are recorded. The argument d is its source free cut and n < ell. -/
structure MiddleCloneInitialL
    {db du dd : Nat}
    (D : AgeTestModel db du dd) (n ell d : Nat) : Prop where
  n_before : n < ell
  cut_le_source : d ≤ n
  source_in_carrier : n ∈ D.carrier
  same_unary : ∀ t : Fin du, D.unary ell t = D.unary n t
  same_diagonal : ∀ t : Fin dd, D.diagonal ell t = D.diagonal n t
  no_lower_links : ∀ x, d ≤ x → x < ell → ∀ t : Fin db,
    D.binary ell x t = false ∧ D.binary x ell t = false
  copy_lower : ∀ x, x < d → ∀ t : Fin db,
    D.binary ell x t = D.binary n x t ∧
    D.binary x ell t = D.binary x n t

/-- The exact two directed pairs from the new ordinary duplicate ell
to the distinguished upper vertex t equal the original pairs from n
to t. No E atom is used in this condition or in the B3 witness. -/
def PrescribedBoringData.MiddleCloneUpperL
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (n : Nat) (hn : n < ell) : Prop :=
  ∀ T, T ∈ F.source → ∀ t : Fin db,
    (F.target T).lReduct.binary (some (Fin.last ell)) none t =
      (F.target T).lReduct.binary
        (some (⟨n, Nat.lt_succ_of_lt hn⟩ : Fin (ell+1))) none t ∧
    (F.target T).lReduct.binary none (some (Fin.last ell)) t =
      (F.target T).lReduct.binary none
        (some (⟨n, Nat.lt_succ_of_lt hn⟩ : Fin (ell+1))) t

/-- The literal common socle and all prescribed upper L-types yield
the complete clone projection interface on an arbitrary finite age
witness. No E axiom, spacing or partial-structure completion enters. -/
theorem PrescribedBoringData.middleCloneLData_of_age_witness
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (n d : Nat) (hn : n < ell)
    (D W : AgeTestModel db du dd)
    (hLower : MiddleCloneInitialL D n ell d)
    (hUpperPair : F.MiddleCloneUpperL n hn)
    (hSocle : SameInitialL W D ell)
    (hUpper : UpperTypesPrescribed W ell F.PrescribedUpperLType) :
    MiddleCloneLData W n ell d := by
  have hnLe : n ≤ ell := Nat.le_of_lt hn
  refine {
    n_before := hLower.n_before
    cut_before_source := hLower.cut_le_source
    source_in_carrier := (hSocle.1 n hnLe).2 hLower.source_in_carrier
    same_unary := ?_
    same_diagonal := ?_
    no_lower_links := ?_
    copy_lower := ?_
    copy_upper := ?_ }
  · intro t
    calc
      W.unary ell t = D.unary ell t :=
        hSocle.2.2.1 ell (le_refl ell) t
      _ = D.unary n t := hLower.same_unary t
      _ = W.unary n t := (hSocle.2.2.1 n hnLe t).symm
  · intro t
    calc
      W.diagonal ell t = D.diagonal ell t :=
        hSocle.2.2.2 ell (le_refl ell) t
      _ = D.diagonal n t := hLower.same_diagonal t
      _ = W.diagonal n t := (hSocle.2.2.2 n hnLe t).symm
  · intro x hx hxb t
    have hXLe : x ≤ ell := Nat.le_of_lt hxb
    obtain ⟨h1,h2⟩ := hLower.no_lower_links x hx hxb t
    constructor
    · calc
        W.binary ell x t = D.binary ell x t :=
          hSocle.2.1 ell x (le_refl ell) hXLe t
        _ = false := h1
    · calc
        W.binary x ell t = D.binary x ell t :=
          hSocle.2.1 x ell hXLe (le_refl ell) t
        _ = false := h2
  · intro x hx t
    have hXLe : x ≤ ell := by
      have hd := hLower.cut_le_source
      omega
    obtain ⟨h1,h2⟩ := hLower.copy_lower x hx t
    constructor
    · calc
        W.binary ell x t = D.binary ell x t :=
          hSocle.2.1 ell x (le_refl ell) hXLe t
        _ = D.binary n x t := h1
        _ = W.binary n x t :=
          (hSocle.2.1 n x hnLe hXLe t).symm
    · calc
        W.binary x ell t = D.binary x ell t :=
          hSocle.2.1 x ell hXLe (le_refl ell) t
        _ = D.binary x n t := h2
        _ = W.binary x n t :=
          (hSocle.2.1 x n hXLe hnLe t).symm
  · intro x hx hAbove t
    have hType : F.PrescribedUpperLType
        (RelationalPrefixType.ofAgeModel W (ell+1) x) :=
      hUpper x hx hAbove
    obtain ⟨T,hT,hEq⟩ := hType
    obtain ⟨hTo,hFrom⟩ := hUpperPair T hT t
    have hNewTo :=
      congrArg (fun R : RelationalPrefixType (ell+1) db du dd =>
        R.binary (some (Fin.last ell)) none t) hEq
    have hOldTo :=
      congrArg (fun R : RelationalPrefixType (ell+1) db du dd =>
        R.binary (some (⟨n, Nat.lt_succ_of_lt hn⟩ : Fin (ell+1))) none t) hEq
    have hNewFrom :=
      congrArg (fun R : RelationalPrefixType (ell+1) db du dd =>
        R.binary none (some (Fin.last ell)) t) hEq
    have hOldFrom :=
      congrArg (fun R : RelationalPrefixType (ell+1) db du dd =>
        R.binary none (some (⟨n, Nat.lt_succ_of_lt hn⟩ : Fin (ell+1))) t) hEq
    change W.binary ell x t =
      (F.target T).lReduct.binary (some (Fin.last ell)) none t at hNewTo
    change W.binary n x t =
      (F.target T).lReduct.binary
        (some (⟨n, Nat.lt_succ_of_lt hn⟩ : Fin (ell+1))) none t at hOldTo
    change W.binary x ell t =
      (F.target T).lReduct.binary none (some (Fin.last ell)) t at hNewFrom
    change W.binary x n t =
      (F.target T).lReduct.binary none
        (some (⟨n, Nat.lt_succ_of_lt hn⟩ : Fin (ell+1))) t at hOldFrom
    exact ⟨hNewTo.trans (hTo.trans hOldTo.symm),
      hNewFrom.trans (hFrom.trans hOldFrom.symm)⟩

/-- The finite L-only B3 test follows uniformly whenever the
prescribed output socle and each upper prescribed terminal pair obey
the two clone identities. This is the precise remaining adapter
interface for the M3 application of the boring-extension lemma. -/
theorem PrescribedBoringData.correctedB3_of_middle_clone
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (n d : Nat) (hn : n < ell)
    (hLower : ∀ S0, S0 ∈ F.source →
      MiddleCloneInitialL
        (prescribedOrdinarySocle (F.target S0)) n ell d)
    (hUpper : F.MiddleCloneUpperL n hn) :
    F.CorrectedB3 family := by
  intro S0 hS0
  intro W hFinite hSame hPrescribed hDeletion
  have hClone : MiddleCloneLData W n ell d :=
    F.middleCloneLData_of_age_witness n d hn
      (prescribedOrdinarySocle (F.target S0)) W
      (hLower S0 hS0) hUpper hSame hPrescribed
  exact hClone.avoidance_of_deletion family hDeletion

end SuccessorTree.V10

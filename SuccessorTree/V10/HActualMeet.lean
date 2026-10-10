import SuccessorTree.V10.KptMeetConverse
import SuccessorTree.V10.HIncidentTrace
import SuccessorTree.V10.MeetProvenance

/-!
# Charge actual Kpt meets in one exact numerical H realization

The ambient object is a genuine finite enumerated partial structure. The
only H-specific interface consists of equalities of its binary and E atoms
with the numerical construction, on its carrier. It contains no assumption
about roots, traces, first differences, free cuts, meets or their charges.

The actual Kpt meet supplies the first binary difference and both E-socle
memberships. These memberships recover the real originals and their positive
generations. The numerical theorem then charges the meet. Finally the same
result is transferred to arbitrary represented prefixes by the proved
nontrivial-prefix meet theorem.

This file does not yet construct the forbidden-free H realization from K,
nor identify the original manuscript's one-way L clause with exact copying.
-/

namespace SuccessorTree.V10

/-- Equality of the complete incident tuple is equality in BOTH directions. -/
theorem bidirectionalBits_eq_iff
    {db : Nat} (B C : Nat → Nat → Fin db → Bool) (x v y w : Nat) :
    bidirectionalBits B x v = bidirectionalBits C y w ↔
      B x v = C y w ∧ B v x = C w y := by
  constructor
  · intro h
    constructor
    · funext a
      have h' := congrFun h (⟨a.val, by have := a.isLt; omega⟩ : Fin (db + db))
      simpa only [bidirectionalBits_left] using h'
    · funext a
      have h' := congrFun h (⟨db + a.val, by have := a.isLt; omega⟩ : Fin (db + db))
      simpa only [bidirectionalBits_right] using h'
  · rintro ⟨hForward, hReverse⟩
    funext s
    by_cases hs : s.val < db
    · simp only [bidirectionalBits, dite_eq_left hs, hForward]
    · simp only [bidirectionalBits, dite_eq_right hs, hReverse]

/-- Local equalities of actual atoms, not a new tree or Ramsey axiom.
Singleton data remain arbitrary: the common meet handles them exactly. -/
structure NumericHOn {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (B : Nat → Nat → Fin db → Bool) (k : Nat) : Prop where
  binary : ∀ x y, x < A.size → y < A.size →
    A.L.binary x y = hNumericBinary B k x y
  e : ∀ x y, x < A.size → y < A.size →
    A.E x y = exactHEBool k x y

/-- Both directed tuples agree with their numerical interpretation. -/
theorem NumericHOn.incident
    {db du dd : Nat} {A : EnumeratedPartialStructure db du dd}
    {B : Nat → Nat → Fin db → Bool} {k : Nat}
    (hH : NumericHOn A B k) (x y : Nat)
    (hx : x < A.size) (hy : y < A.size) :
    bidirectionalBits A.L.binary x y =
      bidirectionalBits (hNumericBinary B k) x y :=
  (bidirectionalBits_eq_iff A.L.binary (hNumericBinary B k) x y x y).2
    ⟨hH.binary x y hx hy, hH.binary y x hy hx⟩

/-- A genuine nontrivial meet gives numerical first-difference data.
Both E memberships and all preceding equalities are conclusions. -/
theorem NumericHOn.nontrivial_meet_data
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (B : Nat → Nat → Fin db → Bool) (k : Nat)
    (hH : NumericHOn A B k) (v w : Nat)
    (hvA : v < A.size) (hwA : w < A.size)
    (hAdV : IsAdmissibleRawType family (A.rawTypeAtFree v))
    (hAdW : IsAdmissibleRawType family (A.rawTypeAtFree w))
    (hCommon : ∃ c : AdmissibleKptNode family,
      c ≤ (⟨A.rawTypeAtFree v, hAdV⟩ : AdmissibleKptNode family) ∧
      c ≤ (⟨A.rawTypeAtFree w, hAdW⟩ : AdmissibleKptNode family))
    (hStrictV : LevelTree.meet
      (⟨A.rawTypeAtFree v, hAdV⟩ : AdmissibleKptNode family)
      (⟨A.rawTypeAtFree w, hAdW⟩ : AdmissibleKptNode family) ≠
      (⟨A.rawTypeAtFree v, hAdV⟩ : AdmissibleKptNode family))
    (hStrictW : LevelTree.meet
      (⟨A.rawTypeAtFree v, hAdV⟩ : AdmissibleKptNode family)
      (⟨A.rawTypeAtFree w, hAdW⟩ : AdmissibleKptNode family) ≠
      (⟨A.rawTypeAtFree w, hAdW⟩ : AdmissibleKptNode family)) :
    ∃ d : Nat,
      LevelTree.lev (LevelTree.meet
        (⟨A.rawTypeAtFree v, hAdV⟩ : AdmissibleKptNode family)
        (⟨A.rawTypeAtFree w, hAdW⟩ : AdmissibleKptNode family)) = d ∧
      exactHEBool k d v = true ∧ exactHEBool k d w = true ∧
      (∀ x < d, bidirectionalBits (hNumericBinary B k) x v =
        bidirectionalBits (hNumericBinary B k) x w) ∧
      bidirectionalBits (hNumericBinary B k) d v ≠
        bidirectionalBits (hNumericBinary B k) d w := by
  obtain ⟨d, hLev, hv, hw, hBefore, hDiff⟩ :=
    admissibleKpt_nontrivial_meet_recovers_binary family A v w
      hAdV hAdW hCommon hStrictV hStrictW
  have hdv : d < v := lt_of_lt_of_le (by omega) (A.freeLevel_le v)
  have hdA : d < A.size := lt_trans hdv hvA
  have hEv : exactHEBool k d v = true := by
    rw [← hH.e d v hdA hvA]
    exact (A.E_iff_freeLevel d v).2 (by omega)
  have hEw : exactHEBool k d w = true := by
    rw [← hH.e d w hdA hwA]
    exact (A.E_iff_freeLevel d w).2 (by omega)
  refine ⟨d, hLev, hEv, hEw, ?_, ?_⟩
  · intro x hx
    have hxA : x < A.size := lt_trans hx hdA
    have hAt : bidirectionalBits A.L.binary x v =
        bidirectionalBits A.L.binary x w := by
      apply (bidirectionalBits_eq_iff A.L.binary A.L.binary x v x w).2
      exact ⟨funext (hBefore.1 ⟨x, hx⟩), funext (hBefore.2 ⟨x, hx⟩)⟩
    exact (hH.incident x v hxA hvA).symm.trans
      (hAt.trans (hH.incident x w hxA hwA))
  · intro hNum
    have hAt := (hH.incident d v hdA hvA).trans
      (hNum.trans (hH.incident d w hdA hwA).symm)
    obtain ⟨hForward, hReverse⟩ :=
      (bidirectionalBits_eq_iff A.L.binary A.L.binary d v d w).1 hAt
    rcases hDiff with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ha (congrFun hForward a)
    · exact ha (congrFun hReverse a)

/-- A nonempty generated E-socle forces positive source generation for k>0. -/
theorem generatedE_positive_source_generation
    (k i n d : Nat) (hk : 0 < k) (h : generatedE k i n d) : 0 < n := by
  obtain ⟨u, q, _, _, hgate, _⟩ := h
  rcases hgate with h | ⟨h, htop⟩ <;> omega

/-- The charge includes the representation and positive generations of
BOTH originals. They are recovered from the meet, not assumed. -/
def NumericHMeetCharge {db : Nat}
    (B : Nat → Nat → Fin db → Bool) (k v w p r : Nat) : Prop :=
  ∃ i j n m : Nat,
    v = hPosition k i n ∧ w = hPosition k j m ∧
    0 < n ∧ 0 < m ∧ n ≤ k ∧ m ≤ k ∧ p < i ∧ p < j ∧
    ((r = m ∧ m < n ∧ p + 1 < j ∧
        FirstBinaryNeighbour (bidirectionalBits B) i p) ∨
     (r = n ∧ n < m ∧ p + 1 < i ∧
        FirstBinaryNeighbour (bidirectionalBits B) j p))

/-- Convert the actual meet data to the charged positive-generation formula. -/
theorem numericHMeetCharge_of_data
    {db : Nat} (B : Nat → Nat → Fin db → Bool)
    (k v w p r : Nat) (hk : 0 < k) (hr : 0 < r) (hrk : r ≤ k)
    (hEv : exactHEBool k (hPosition k p r) v = true)
    (hEw : exactHEBool k (hPosition k p r) w = true)
    (hBefore : ∀ x < hPosition k p r,
      bidirectionalBits (hNumericBinary B k) x v =
        bidirectionalBits (hNumericBinary B k) x w)
    (hDiff : bidirectionalBits (hNumericBinary B k) (hPosition k p r) v ≠
      bidirectionalBits (hNumericBinary B k) (hPosition k p r) w) :
    NumericHMeetCharge B k v w p r := by
  obtain ⟨i, n, hnk, hv, hinI⟩ :=
    (exactHEBool_true_iff k (hPosition k p r) v).1 hEv
  obtain ⟨j, m, hmk, hw, hinJ⟩ :=
    (exactHEBool_true_iff k (hPosition k p r) w).1 hEw
  have hn := generatedE_positive_source_generation k i n _ hk hinI
  have hm := generatedE_positive_source_generation k j m _ hk hinJ
  refine ⟨i, j, n, m, hv, hw, hn, hm, hnk, hmk, ?_⟩
  exact hNumericBinary_first_positive_disagreement B k i j m n p r
    hm hn hmk hnk hr hrk hinI hinJ
    (by simpa only [hv, hw] using hBefore)
    (by simpa only [hv, hw] using hDiff)

/-- Charge a nontrivial actual meet of ANY two represented prefixes.
No common-root equality, first-disagreement data, positive original
generation or free-level bound is supplied as an assumption. -/
theorem NumericHOn.prefix_meet_charge
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (B : Nat → Nat → Fin db → Bool) (k : Nat) (hk : 0 < k)
    (hH : NumericHOn A B k) (v w : Nat)
    (hvA : v < A.size) (hwA : w < A.size)
    (hAdV : IsAdmissibleRawType family (A.rawTypeAtFree v))
    (hAdW : IsAdmissibleRawType family (A.rawTypeAtFree w))
    (s t : AdmissibleKptNode family)
    (hs : s ≤ (⟨A.rawTypeAtFree v, hAdV⟩ : AdmissibleKptNode family))
    (ht : t ≤ (⟨A.rawTypeAtFree w, hAdW⟩ : AdmissibleKptNode family))
    (hCommon : ∃ c : AdmissibleKptNode family, c ≤ s ∧ c ≤ t)
    (hStrictS : LevelTree.meet s t ≠ s)
    (hStrictT : LevelTree.meet s t ≠ t)
    (p r : Nat) (hr : 0 < r) (hrk : r ≤ k)
    (hMeet : LevelTree.lev (LevelTree.meet s t) = hPosition k p r) :
    NumericHMeetCharge B k v w p r := by
  let a : AdmissibleKptNode family := ⟨A.rawTypeAtFree v, hAdV⟩
  let b : AdmissibleKptNode family := ⟨A.rawTypeAtFree w, hAdW⟩
  have hOrigMeet : LevelTree.meet a b = LevelTree.meet s t :=
    meet_eq_of_nontrivial_prefixes hCommon hs ht hStrictS hStrictT
  have hOrigCommon : ∃ c : AdmissibleKptNode family, c ≤ a ∧ c ≤ b := by
    obtain ⟨c, hcs, hct⟩ := hCommon
    exact ⟨c, hcs.trans hs, hct.trans ht⟩
  have hOrigStrictA : LevelTree.meet a b ≠ a := by
    rw [hOrigMeet]
    exact ne_of_lt (lt_of_lt_of_le
      (lt_of_le_of_ne (LevelTree.meet_le_left hCommon) hStrictS) hs)
  have hOrigStrictB : LevelTree.meet a b ≠ b := by
    rw [hOrigMeet]
    exact ne_of_lt (lt_of_lt_of_le
      (lt_of_le_of_ne (LevelTree.meet_le_right hCommon) hStrictT) ht)
  obtain ⟨d, hLev, hEv, hEw, hBefore, hDiff⟩ :=
    NumericHOn.nontrivial_meet_data family A B k hH v w hvA hwA
      hAdV hAdW hOrigCommon hOrigStrictA hOrigStrictB
  have hd : d = hPosition k p r := by
    change LevelTree.lev (LevelTree.meet a b) = d at hLev
    rw [hOrigMeet] at hLev
    exact hLev.symm.trans hMeet
  rw [hd] at hEv hEw hBefore hDiff
  exact numericHMeetCharge_of_data B k v w p r hk hr hrk hEv hEw hBefore hDiff

end SuccessorTree.V10

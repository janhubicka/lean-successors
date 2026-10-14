import SuccessorTree.V10.I3WitnessLowerRelocation
import SuccessorTree.V10.I3WitnessCrossRelocation
import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# The full forbidden-copy relocation at an actual I3 age witness

Let W be a finite L-only age witness with initial socle equal to the
numerical H model through the tested coordinate ell. A nontrivial
irreducible forbidden pattern P has an ordered induced copy e in W,
with exactly r initial vertices at or below ell, ending at ell.

Suppose those r lower vertices have their actual real H coordinates,
strictly increasing first indices and generation-rank bounds,
and each upper witness vertex realizes the complete crossing type
of one named *later real* original of H. These are precisely the
concrete geometric facts to be recovered from the manuscript's
actual I3 construction.

If the last lower generation exceeded r-1, relocate each lower
vertex iota(first(a),generation(a)) to iota(first(a),a), without
moving any upper witness vertex. The lower-zone and lower--upper
lemmas verify all directed L atoms; upper--upper atoms are literally
unchanged. The relocated map is strictly increasing, remains in
the carrier and avoids ell. This would give an induced forbidden
copy in W without ell, contradicting its avoidance.

Thus the last lower generation is exactly r-1. This proves the
geometric relocation CONTRADICTION after actual coordinates and
upper original types have been extracted. It does not assume an
abstract relation-preservation hypothesis or use auxiliary E on W.
-/

namespace SuccessorTree.V10

/-- The full lower-generation equality in Lemma 6.53, from the
literal finite I3 age witness plus exact numeric representations
of the lower and upper original vertices.

No extra copy or relocation-homomorphism hypothesis is assumed.
The remaining manuscript interface is to obtain the coordinate
and named-original premises directly from its specific I3 witness. -/
theorem numericI3_forbidden_copy_forces_last_lower_rank
    {db du dd t : Nat}
    (K : AgeTestModel db du dd)
    (k N ell r : Nat) (hr : 0 < r) (hrt : r < t) (hrk : r ≤ k)
    (W : AgeTestModel db du dd)
    (hSocle : SameInitialL W (finiteNumericHL K k N) ell)
    (P : ForbiddenAtomicPattern t db du dd)
    (hIrred : P.Irreducible)
    (e : Fin t → Nat) (hCopy : W.Realizes P e)
    (hDelete : ¬ ∃ f : Fin t → Nat,
      (W.withoutVertex ell).Realizes P f)
    (first generation : Fin r → Nat)
    (hFirst : StrictMono first)
    (hRep : ∀ a : Fin r,
      generation a ≤ k ∧
      e ⟨a.val, Nat.lt_trans a.isLt hrt⟩ =
        hPosition k (first a) (generation a))
    (hRank : ∀ a : Fin r, a.val ≤ generation a)
    (hLast : e ⟨r-1, by omega⟩ = ell)
    (hUpper : ∀ b : Fin t, r ≤ b.val →
      ∃ j m : Nat, m ≤ k ∧ ell < hPosition k j m ∧
        RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (ell+1)
            (hPosition k j m)) :
    generation ⟨r-1, by omega⟩ = r-1 := by
  classical
  let last : Fin r := ⟨r-1, by omega⟩
  let lo (a : Fin r) : Fin t := ⟨a.val, Nat.lt_trans a.isLt hrt⟩
  let old (a : Fin r) : Nat :=
    hPosition k (first a) (generation a)
  let young (a : Fin r) : Nat := hPosition k (first a) a.val
  have hOldEq (a : Fin r) : old a = e (lo a) := (hRep a).2.symm
  have hLastAt : e (lo last) = ell := by
    simpa only [lo,last] using hLast
  have hLastBound : r-1 ≤ generation last := by
    simpa only [last] using (hRank last)
  by_contra hneq
  have hneqLast : generation last ≠ r-1 := by
    simpa only [last] using hneq
  have hGap : r-1 < generation last := by omega
  have hEllCarrier : ell ∈ W.carrier := by
    rw [←hLastAt]
    exact hCopy.2.1 (lo last)
  have hBefore (a : Fin r) : old a ≤ ell := by
    have hIndex : lo a ≤ lo last := Fin.le_def.mpr (by
      dsimp [lo,last]
      have ha := a.isLt
      omega)
    calc
      old a = e (lo a) := hOldEq a
      _ ≤ e (lo last) := hCopy.1.monotone hIndex
      _ = ell := hLastAt
  have hLinked : ∀ a b : Fin r, a < b →
      ∃ bit : Fin db,
        W.binary (old a) (old b) bit = true ∨
        W.binary (old b) (old a) bit = true := by
    intro a b hab
    have hNE : lo a ≠ lo b := by
      intro h
      have heq := congrArg Fin.val h
      exact (Nat.ne_of_lt (Fin.lt_def.mp hab)) heq
    obtain ⟨bit,hP⟩ := hIrred (lo a) (lo b) hNE
    refine ⟨bit,?_⟩
    rcases hP with hAB | hBA
    · exact Or.inl (by
        rw [hOldEq a,hOldEq b]
        exact (hCopy.2.2.1 (lo a) (lo b) hNE bit).trans hAB)
    · exact Or.inr (by
        rw [hOldEq b,hOldEq a]
        exact (hCopy.2.2.1 (lo b) (lo a) hNE.symm bit).trans hBA)
  have hLastPos : ell = hPosition k
      (first last) (generation last) := by
    calc
      ell = e (lo last) := hLastAt.symm
      _ = old last := (hOldEq last).symm
      _ = hPosition k (first last) (generation last) := rfl
  have hLowerZone := numericI3_lower_zone_relocation
    K k N ell r hr hrk W hSocle hEllCarrier
    first generation hFirst
    (fun a => ⟨(hRep a).1,hBefore a⟩)
    hLastPos hGap hLinked
  obtain ⟨hYoung,hYoungOrder,hLowerBinary,hLowerUnary,hLowerDiagonal⟩ :=
    hLowerZone
  have hAbove (b : Fin t) (hb : r ≤ b.val) : ell < e b := by
    have hlt : lo last < b := Fin.lt_def.mpr (by
      dsimp [lo,last]
      omega)
    calc
      ell = e (lo last) := hLastAt.symm
      _ < e b := hCopy.1 hlt
  have hLowerUpper : ∀ a : Fin r, ∀ b : Fin t,
      r ≤ b.val → ∀ bit : Fin db,
        W.binary (old a) (e b) bit =
          W.binary (young a) (e b) bit ∧
        W.binary (e b) (old a) bit =
          W.binary (e b) (young a) bit := by
    intro a b hb bit
    obtain ⟨j,m,hm,hOrigAfter,hType⟩ := hUpper b hb
    have hNE : lo a ≠ b := by
      intro h
      have hh := congrArg Fin.val h
      dsimp [lo] at hh
      have := a.isLt
      omega
    have hCopyLink : ∃ t0 : Fin db,
        W.binary (old a) (e b) t0 = true ∨
        W.binary (e b) (old a) t0 = true := by
      obtain ⟨t0,hL⟩ := hIrred (lo a) b hNE
      refine ⟨t0,?_⟩
      rcases hL with hAB | hBA
      · exact Or.inl (by
          rw [hOldEq a]
          exact (hCopy.2.2.1 (lo a) b hNE t0).trans hAB)
      · exact Or.inr (by
          rw [hOldEq a]
          exact (hCopy.2.2.1 b (lo a) hNE.symm t0).trans hBA)
    have hak : a.val < k := by
      have ha := a.isLt
      omega
    obtain ⟨_hij,_ham,hBits⟩ :=
      numericI3_witness_lower_upper_relocation
        K k N ell (e b)
        (first a) j (generation a) m a.val W
        (hRep a).1 hm (hBefore a) hOrigAfter hType
        (hRank a) hak hCopyLink
    exact hBits bit
  let relocated : Fin t → Nat := fun b =>
    if hb : b.val < r then young ⟨b.val,hb⟩ else e b
  have hRelocLower (a : Fin r) :
      relocated (lo a) = young a := by
    simp [relocated,lo,a.isLt,young]
  have hRelocUpper (b : Fin t) (hb : r ≤ b.val) :
      relocated b = e b := by
    simp only [relocated, dite_eq_right (Nat.not_lt.mpr hb)]
  have hRelocAtLower (b : Fin t) (hb : b.val < r) :
      relocated b = young ⟨b.val,hb⟩ := by
    simp [relocated,hb]
  have hRelocIn (b : Fin t) : relocated b ∈ W.carrier := by
    by_cases hb : b.val < r
    · let a : Fin r := ⟨b.val,hb⟩
      have hbEq : b = lo a := Fin.ext rfl
      rw [hbEq,hRelocLower]
      exact (hYoung a).2
    · rw [hRelocUpper b (Nat.le_of_not_gt hb)]
      exact hCopy.2.1 b
  have hRelocMono : StrictMono relocated := by
    intro a b hab
    by_cases ha : a.val < r
    · by_cases hb : b.val < r
      · let aa : Fin r := ⟨a.val,ha⟩
        let bb : Fin r := ⟨b.val,hb⟩
        have hlt : aa < bb := Fin.lt_def.mpr (Fin.lt_def.mp hab)
        have hh := hYoungOrder hlt
        simpa only [relocated, dite_eq_left ha, dite_eq_left hb] using hh
      · have hrel : relocated a < ell := by
          rw [hRelocAtLower a ha]
          exact (hYoung ⟨a.val,ha⟩).1
        rw [hRelocUpper b (Nat.le_of_not_gt hb)]
        exact lt_trans hrel (hAbove b (Nat.le_of_not_gt hb))
    · have hb : ¬ b.val < r := by
        have := Fin.lt_def.mp hab
        omega
      rw [hRelocUpper a (Nat.le_of_not_gt ha),
        hRelocUpper b (Nat.le_of_not_gt hb)]
      exact hCopy.1 hab
  have hRelocBinary : ∀ a b : Fin t, a ≠ b → ∀ bit : Fin db,
      W.binary (relocated a) (relocated b) bit =
        P.binary a b bit := by
    intro a b hne bit
    by_cases ha : a.val < r
    · by_cases hb : b.val < r
      · let aa : Fin r := ⟨a.val,ha⟩
        let bb : Fin r := ⟨b.val,hb⟩
        have hne' : aa ≠ bb := by
          intro hab
          have heq : aa.val = bb.val :=
            congrArg (fun z : Fin r => z.val) hab
          have hSame : a = b := Fin.ext (by
            exact heq)
          exact hne hSame
        have heq := hLowerBinary aa bb hne' bit
        have hOldA : old aa = e a := by
          have : lo aa = a := Fin.ext rfl
          simpa only [this] using hOldEq aa
        have hOldB : old bb = e b := by
          have : lo bb = b := Fin.ext rfl
          simpa only [this] using hOldEq bb
        calc
          W.binary (relocated a) (relocated b) bit =
              W.binary (young aa) (young bb) bit := by
                rw [hRelocAtLower a ha, hRelocAtLower b hb]
          _ = W.binary (old aa) (old bb) bit := heq.symm
          _ = W.binary (e a) (e b) bit := by rw [hOldA,hOldB]
          _ = P.binary a b bit := hCopy.2.2.1 a b hne bit
      · let aa : Fin r := ⟨a.val,ha⟩
        have hOldA : old aa = e a := by
          have : lo aa = a := Fin.ext rfl
          simpa only [this] using hOldEq aa
        have hEq := (hLowerUpper aa b (Nat.le_of_not_gt hb) bit).1
        calc
          W.binary (relocated a) (relocated b) bit =
              W.binary (young aa) (e b) bit := by
                rw [hRelocAtLower a ha,
                  hRelocUpper b (Nat.le_of_not_gt hb)]
          _ = W.binary (old aa) (e b) bit := hEq.symm
          _ = W.binary (e a) (e b) bit := by rw [hOldA]
          _ = P.binary a b bit := hCopy.2.2.1 a b hne bit
    · by_cases hb : b.val < r
      · let bb : Fin r := ⟨b.val,hb⟩
        have hOldB : old bb = e b := by
          have : lo bb = b := Fin.ext rfl
          simpa only [this] using hOldEq bb
        have hEq := (hLowerUpper bb a (Nat.le_of_not_gt ha) bit).2
        calc
          W.binary (relocated a) (relocated b) bit =
              W.binary (e a) (young bb) bit := by
                rw [hRelocUpper a (Nat.le_of_not_gt ha),
                  hRelocAtLower b hb]
          _ = W.binary (e a) (old bb) bit := hEq.symm
          _ = W.binary (e a) (e b) bit := by rw [hOldB]
          _ = P.binary a b bit := hCopy.2.2.1 a b hne bit
      · rw [hRelocUpper a (Nat.le_of_not_gt ha),
            hRelocUpper b (Nat.le_of_not_gt hb)]
        exact hCopy.2.2.1 a b hne bit
  have hRelocUnary : ∀ a : Fin t, ∀ bit : Fin du,
      W.unary (relocated a) bit = P.unary a bit := by
    intro a bit
    by_cases ha : a.val < r
    · let aa : Fin r := ⟨a.val,ha⟩
      have hOldA : old aa = e a := by
        have : lo aa = a := Fin.ext rfl
        simpa only [this] using hOldEq aa
      calc
        W.unary (relocated a) bit = W.unary (young aa) bit := by
          rw [hRelocAtLower a ha]
        _ = W.unary (old aa) bit := (hLowerUnary aa bit).symm
        _ = W.unary (e a) bit := by rw [hOldA]
        _ = P.unary a bit := hCopy.2.2.2.1 a bit
    · rw [hRelocUpper a (Nat.le_of_not_gt ha)]
      exact hCopy.2.2.2.1 a bit
  have hRelocDiagonal : ∀ a : Fin t, ∀ bit : Fin dd,
      W.diagonal (relocated a) bit = P.diagonal a bit := by
    intro a bit
    by_cases ha : a.val < r
    · let aa : Fin r := ⟨a.val,ha⟩
      have hOldA : old aa = e a := by
        have : lo aa = a := Fin.ext rfl
        simpa only [this] using hOldEq aa
      calc
        W.diagonal (relocated a) bit =
            W.diagonal (young aa) bit := by
          rw [hRelocAtLower a ha]
        _ = W.diagonal (old aa) bit :=
          (hLowerDiagonal aa bit).symm
        _ = W.diagonal (e a) bit := by rw [hOldA]
        _ = P.diagonal a bit := hCopy.2.2.2.2 a bit
    · rw [hRelocUpper a (Nat.le_of_not_gt ha)]
      exact hCopy.2.2.2.2 a bit
  have hRelocCopy : W.Realizes P relocated :=
    ⟨hRelocMono,hRelocIn,hRelocBinary,
      hRelocUnary,hRelocDiagonal⟩
  have hAway : ∀ a : Fin t, relocated a ≠ ell := by
    intro a
    by_cases ha : a.val < r
    · have hlt : relocated a < ell := by
        rw [hRelocAtLower a ha]
        exact (hYoung ⟨a.val,ha⟩).1
      exact ne_of_lt hlt
    · have hh := hAbove a (Nat.le_of_not_gt ha)
      rw [hRelocUpper a (Nat.le_of_not_gt ha)]
      omega
  have hRestricted : (W.withoutVertex ell).Realizes P relocated :=
    AgeTestModel.realizes_restrictCarrier W
      (fun x => x ≠ ell) P relocated hRelocCopy hAway
  exact hDelete ⟨relocated,hRestricted⟩

end SuccessorTree.V10

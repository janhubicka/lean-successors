import SuccessorTree.V10.I3NumericRelocation
import SuccessorTree.V10.HFinitePartial
import SuccessorTree.V10.RelationalTypeReduct
import Mathlib.Tactic

/-!
# I3 witness lower--upper relocation from its actual named original

The paper's finite I3 witness is an L-only structure W. One upper
vertex w has exactly the full induced L type over the tested
coordinate ell of an original H vertex iota(j,m).

Let an old lower vertex be the actual H vertex iota(i,q), at or below
ell. A positive directed relation from that vertex to w shows that
the two original H vertices are linked. Since the original upper
position is >ell, the exact H numerical generator theorem derives
i<j and its generation gate, without assuming those facts.

If a is the lower vertex's rank with a<=q and a<k, its relocation
to iota(i,a) lies earlier in the same initial socle. The numerical
relation relocation lemma then shows EVERY directed true and false
L bit from this relocated vertex to w agrees with the old one.
Both binary orientations are included.

This is the actual lower--upper atomic zone needed by Lemma 6.53.
It does not yet assemble the whole induced forbidden copy.
-/

namespace SuccessorTree.V10

/-- A named upper original's complete L-type, together with one
positive lower--upper relation and the actual H numerical
representation of the lower vertex, DERIVES the first-index order
and preserves ALL its incident directed Boolean atoms after
lowering the lower vertex's generation to its rank.

No E relation on W, no abstract linked-pair assumption, and no
positive-only copying are used. -/
theorem numericI3_witness_lower_upper_relocation
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N ell w i j q m a : Nat)
    (W : AgeTestModel db du dd)
    (hq : q ≤ k) (hm : m ≤ k)
    (hBelow : hPosition k i q ≤ ell)
    (hOrigAfter : ell < hPosition k j m)
    (hType :
      RelationalPrefixType.ofAgeModel W (ell+1) w =
      RelationalPrefixType.ofAgeModel
        (finiteNumericHL K k N) (ell+1) (hPosition k j m))
    (ha : a ≤ q) (hak : a < k)
    (hLink : ∃ t : Fin db,
      W.binary (hPosition k i q) w t = true ∨
      W.binary w (hPosition k i q) t = true) :
    i < j ∧ a < m ∧
    ∀ t : Fin db,
      W.binary (hPosition k i q) w t =
        W.binary (hPosition k i a) w t ∧
      W.binary w (hPosition k i q) t =
        W.binary w (hPosition k i a) t := by
  let old := hPosition k i q
  let young := hPosition k i a
  let upper := hPosition k j m
  have hOldBound : old < ell+1 := by
    dsimp [old]
    omega
  have hYoungBeforeOld : young ≤ old := by
    dsimp [young,old,hPosition]
    omega
  have hYoungBound : young < ell+1 := by omega
  let io : Fin (ell+1) := ⟨old,hOldBound⟩
  let iy : Fin (ell+1) := ⟨young,hYoungBound⟩
  have hOldForward : ∀ t : Fin db,
      W.binary old w t = hNumericBinary K.binary k old upper t := by
    intro t
    have h := congrArg
      (fun T : RelationalPrefixType (ell+1) db du dd =>
        T.binary (some io) none t) hType
    exact h
  have hOldReverse : ∀ t : Fin db,
      W.binary w old t = hNumericBinary K.binary k upper old t := by
    intro t
    have h := congrArg
      (fun T : RelationalPrefixType (ell+1) db du dd =>
        T.binary none (some io) t) hType
    exact h
  have hYoungForward : ∀ t : Fin db,
      W.binary young w t = hNumericBinary K.binary k young upper t := by
    intro t
    have h := congrArg
      (fun T : RelationalPrefixType (ell+1) db du dd =>
        T.binary (some iy) none t) hType
    exact h
  have hYoungReverse : ∀ t : Fin db,
      W.binary w young t = hNumericBinary K.binary k upper young t := by
    intro t
    have h := congrArg
      (fun T : RelationalPrefixType (ell+1) db du dd =>
        T.binary none (some iy) t) hType
    exact h
  have hNumericalLink : ∃ t : Fin db,
      hNumericBinary K.binary k old upper t = true ∨
      hNumericBinary K.binary k upper old t = true := by
    obtain ⟨t,hForward | hReverse⟩ := hLink
    · exact ⟨t,Or.inl ((hOldForward t).symm.trans hForward)⟩
    · exact ⟨t,Or.inr ((hOldReverse t).symm.trans hReverse)⟩
  have hNumericalOrder : old < upper := by
    dsimp [old,upper]
    omega
  obtain ⟨i',j',q',m',hij',hq',hm',_hgate,hFirstPos,hUpperPos⟩ :=
    hNumericBinary_linked_generators K.binary k old upper
      hNumericalOrder hNumericalLink
  have hI : i = i' := by
    exact (hPosition_injective_bounded k i q i' q'
      hq hq' (by
        calc
          hPosition k i q = old := rfl
          _ = hPosition k i' q' := hFirstPos)).1
  have hJ : j = j' := by
    exact (hPosition_injective_bounded k j m j' m'
      hm hm' (by
        calc
          hPosition k j m = upper := rfl
          _ = hPosition k j' m' := hUpperPos)).1
  have hij : i < j := by
    calc
      i = i' := hI
      _ < j' := hij'
      _ = j := hJ.symm
  obtain ⟨ham,hRel⟩ :=
    numericH_linked_lower_upper_relocation
      K.binary k i j q m a hij hq hm ha hak hNumericalLink
  refine ⟨hij,ham,?_⟩
  intro t
  constructor
  · calc
      W.binary old w t = hNumericBinary K.binary k old upper t :=
        hOldForward t
      _ = hNumericBinary K.binary k young upper t := (hRel t).1
      _ = W.binary young w t := (hYoungForward t).symm
  · calc
      W.binary w old t = hNumericBinary K.binary k upper old t :=
        hOldReverse t
      _ = hNumericBinary K.binary k upper young t := (hRel t).2
      _ = W.binary w young t := (hYoungReverse t).symm

end SuccessorTree.V10

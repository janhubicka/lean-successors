import SuccessorTree.V10.HFinitePartial

/-!
# Forbidden-free age of the finite exact numerical H construction

The base K is enumerated on Nat, as in the manuscript after the allowed
neutral extension. Every nontrivial irreducible ordered copy in H consists
of real vertices. Its first indices are strictly increasing and preserve
ALL L atoms, not just the positive atoms used to find the generation gate.
A forbidden non-neutral singleton likewise cannot be fake.

This proves avoidance for the actual finiteNumericH constructor. It does
not assume an age theorem for H or the conclusion of the meet calculation.
-/

namespace SuccessorTree.V10

/-- An incident pair makes each endpoint real, in either orientation. -/
theorem hNumericBinary_incident_real
    {db : Nat} (B : Nat → Nat → Fin db → Bool) (k x y : Nat)
    (h : ∃ a, hNumericBinary B k x y a = true ∨
      hNumericBinary B k y x a = true) :
    ∃ i g : Nat, g ≤ k ∧ x = hPosition k i g := by
  obtain ⟨a, ha | ha⟩ := h
  · obtain ⟨i, j, q, m, _, hq, hm, _, hdir⟩ :=
      (hNumericBinary_true_iff B k x y a).1 ha
    rcases hdir with ⟨hx, _, _⟩ | ⟨hx, _, _⟩
    · exact ⟨i, q, hq, hx⟩
    · exact ⟨j, m, hm, hx⟩
  · obtain ⟨i, j, q, m, _, hq, hm, _, hdir⟩ :=
      (hNumericBinary_true_iff B k y x a).1 ha
    rcases hdir with ⟨_, hx, _⟩ | ⟨_, hx, _⟩
    · exact ⟨j, m, hm, hx⟩
    · exact ⟨i, q, hq, hx⟩

/-- For a represented increasing linked pair, the base order and the
complete copied directed tuples follow from the unique generators. -/
theorem hNumericBinary_real_linked_copies
    {db : Nat} (B : Nat → Nat → Fin db → Bool)
    (k i j q m : Nat) (hq : q ≤ k) (hm : m ≤ k)
    (hpos : hPosition k i q < hPosition k j m)
    (hLink : ∃ a, hNumericBinary B k (hPosition k i q) (hPosition k j m) a = true ∨
      hNumericBinary B k (hPosition k j m) (hPosition k i q) a = true) :
    i < j ∧
      hNumericBinary B k (hPosition k i q) (hPosition k j m) = B i j ∧
      hNumericBinary B k (hPosition k j m) (hPosition k i q) = B j i := by
  obtain ⟨i', j', q', m', hij, hq', hm', hgate, hx, hy⟩ :=
    hNumericBinary_linked_generators B k _ _ hpos hLink
  obtain ⟨hi, hqEq⟩ := hPosition_injective_bounded k i q i' q' hq hq' hx
  obtain ⟨hj, hmEq⟩ := hPosition_injective_bounded k j m j' m' hm hm' hy
  subst i'
  subst j'
  subst q'
  subst m'
  refine ⟨hij, ?_, ?_⟩
  · have h := hNumericBinary_forward_matches_bundledTrace B k i j q m hij hq hm
    simpa [bundledTrace, traceBit, hij, hgate] using h
  · have h := hNumericBinary_reverse_matches_bundledTrace B k i j q m hij hq hm
    simpa [bundledTrace, traceBit, hij, hgate] using h

/-- Every nontrivial irreducible ordered copy in the CONSTRUCTED numerical
H L-reduct projects to an ordered induced copy in the Nat-enumerated base. -/
theorem finiteNumericHL_irreducible_copy_projects
    {r db du dd : Nat} (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (k N : Nat) (F : ForbiddenAtomicPattern r db du dd)
    (hr : 1 < r) (hIrred : F.Irreducible)
    (f : Fin r → Nat) (hCopy : (finiteNumericHL K k N).Realizes F f) :
    ∃ g : Fin r → Nat, K.Realizes F g := by
  classical
  have hLink : ∀ a b : Fin r, a ≠ b →
      ∃ t, hNumericBinary K.binary k (f a) (f b) t = true ∨
        hNumericBinary K.binary k (f b) (f a) t = true := by
    intro a b hab
    obtain ⟨t, ht⟩ := hIrred a b hab
    refine ⟨t, ?_⟩
    have hab' := hCopy.2.2.1 a b hab t
    have hba' := hCopy.2.2.1 b a hab.symm t
    change hNumericBinary K.binary k (f a) (f b) t = F.binary a b t at hab'
    change hNumericBinary K.binary k (f b) (f a) t = F.binary b a t at hba'
    simpa only [hab', hba'] using ht
  have hReal : ∀ a : Fin r, ∃ i g : Nat, g ≤ k ∧ f a = hPosition k i g := by
    intro a
    let zero : Fin r := ⟨0, by omega⟩
    let one : Fin r := ⟨1, hr⟩
    obtain ⟨b, hab⟩ : ∃ b : Fin r, a ≠ b := by
      by_cases ha : a = zero
      · refine ⟨one, ?_⟩
        intro h
        have hv := congrArg Fin.val (ha.symm.trans h)
        norm_num [zero, one] at hv
      · exact ⟨zero, ha⟩
    exact hNumericBinary_incident_real K.binary k (f a) (f b) (hLink a b hab)
  choose g generation hgen hrepr using hReal
  have hPair (a b : Fin r) (hab : a < b) :
      g a < g b ∧
      hNumericBinary K.binary k (f a) (f b) = K.binary (g a) (g b) ∧
      hNumericBinary K.binary k (f b) (f a) = K.binary (g b) (g a) := by
    have hpos := hCopy.1 hab
    have hL := hLink a b (ne_of_lt hab)
    rw [hrepr a, hrepr b] at hpos hL ⊢
    exact hNumericBinary_real_linked_copies K.binary k (g a) (g b)
      (generation a) (generation b) (hgen a) (hgen b) hpos hL
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact (hPair a b hab).1
  · intro a
    exact hCarrier (g a)
  · intro a b hab t
    have h := hCopy.2.2.1 a b hab t
    change hNumericBinary K.binary k (f a) (f b) t = F.binary a b t at h
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · rw [(hPair a b hlt).2.1] at h
      exact h
    · rw [(hPair b a hgt).2.2] at h
      exact h
  · intro a t
    have h := hCopy.2.2.2.1 a t
    change hNumericSingleton K.unary k (f a) t = F.unary a t at h
    rw [hrepr a, hNumericSingleton_real K.unary k (g a) (generation a) (hgen a)] at h
    exact h
  · intro a t
    have h := hCopy.2.2.2.2 a t
    change hNumericSingleton K.diagonal k (f a) t = F.diagonal a t at h
    rw [hrepr a, hNumericSingleton_real K.diagonal k (g a) (generation a) (hgen a)] at h
    exact h

/-- A non-neutral forbidden singleton has a real original; unary and
all diagonal facts of its induced copy are preserved together. -/
theorem finiteNumericHL_singleton_copy_projects
    {db du dd : Nat} (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (k N : Nat) (F : ForbiddenAtomicPattern 1 db du dd)
    (hNonNeutral : F.NonNeutralSingleton)
    (f : Fin 1 → Nat) (hCopy : (finiteNumericHL K k N).Realizes F f) :
    ∃ g : Fin 1 → Nat, K.Realizes F g := by
  have hReal : ∃ i g : Nat, g ≤ k ∧ f 0 = hPosition k i g := by
    by_contra hn
    have hU := hNumericSingleton_no_real K.unary k (f 0) hn
    have hD := hNumericSingleton_no_real K.diagonal k (f 0) hn
    rcases hNonNeutral with ⟨t, ht⟩ | ⟨t, ht⟩
    · have h := hCopy.2.2.2.1 0 t
      change hNumericSingleton K.unary k (f 0) t = F.unary 0 t at h
      rw [hU, ht] at h
      contradiction
    · have h := hCopy.2.2.2.2 0 t
      change hNumericSingleton K.diagonal k (f 0) t = F.diagonal 0 t at h
      rw [hD, ht] at h
      contradiction
  obtain ⟨i, g, hg, hp⟩ := hReal
  refine ⟨fun _ => i, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have heq : a = b := Subsingleton.elim _ _
    exact False.elim ((ne_of_lt hab) heq)
  · intro a
    exact hCarrier i
  · intro a b hab t
    exact False.elim (hab (Subsingleton.elim _ _))
  · intro a t
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    have h := hCopy.2.2.2.1 0 t
    change hNumericSingleton K.unary k (f 0) t = F.unary 0 t at h
    rw [hp, hNumericSingleton_real K.unary k i g hg] at h
    exact h
  · intro a t
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    have h := hCopy.2.2.2.2 0 t
    change hNumericSingleton K.diagonal k (f 0) t = F.diagonal 0 t at h
    rw [hp, hNumericSingleton_real K.diagonal k i g hg] at h
    exact h

/-- Actual numerical H preserves every normalized forbidden pattern. -/
theorem NormalizedForbidden.finiteNumericH_preserves_avoidance
    {db du dd : Nat} (bad : NormalizedForbidden db du dd)
    (K : AgeTestModel db du dd) (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (k N : Nat) (hAvoid : bad.Avoids K) :
    bad.Avoids (finiteNumericHL K k N) := by
  cases bad with
  | singleton F hNonNeutral =>
    rintro ⟨f, hCopy⟩
    exact hAvoid (finiteNumericHL_singleton_copy_projects K hCarrier k N F hNonNeutral f hCopy)
  | nontrivial r F hr hIrred =>
    rintro ⟨f, hCopy⟩
    exact hAvoid (finiteNumericHL_irreducible_copy_projects K hCarrier k N F hr hIrred f hCopy)

/-- The full age certificate is obtained from K; no H-avoidance premise. -/
theorem finiteNumericH_avoids_family
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (k N : Nat) (hAvoid : ∀ bad, bad ∈ family → bad.Avoids K) :
    ∀ bad, bad ∈ family → bad.Avoids (finiteNumericHL K k N) := by
  intro bad hbad
  exact bad.finiteNumericH_preserves_avoidance K hCarrier k N (hAvoid bad hbad)

/-- An actual H original whose admissibility is derived entirely from K. -/
noncomputable def forbiddenFreeHOriginal
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (k N : Nat) (hAvoid : ∀ bad, bad ∈ family → bad.Avoids K)
    (v : Nat) (hv : v < N) : AdmissibleKptNode family :=
  finiteNumericHOriginal family K k N
    (finiteNumericH_avoids_family family K hCarrier k N hAvoid) v hv

/-- Lemma 6.49 for the exact normalized H construction and arbitrary
represented prefixes. No numerical trace, E-cut, H-age or meet-charge
hypothesis is required; only the forbidden-free base and actual geometry. -/
theorem forbiddenFreeH_prefix_meet_charge
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (k N : Nat) (hk : 0 < k)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids K)
    (v w : Nat) (hv : v < N) (hw : w < N)
    (s t : AdmissibleKptNode family)
    (hs : s ≤ forbiddenFreeHOriginal family K hCarrier k N hAvoid v hv)
    (ht : t ≤ forbiddenFreeHOriginal family K hCarrier k N hAvoid w hw)
    (hCommon : ∃ c : AdmissibleKptNode family, c ≤ s ∧ c ≤ t)
    (hStrictS : LevelTree.meet s t ≠ s)
    (hStrictT : LevelTree.meet s t ≠ t)
    (p r : Nat) (hr : 0 < r) (hrk : r ≤ k)
    (hMeet : LevelTree.lev (LevelTree.meet s t) = hPosition k p r) :
    NumericHMeetCharge K.binary k v w p r :=
  finiteNumericH_prefix_meet_charge family K k N hk
    (finiteNumericH_avoids_family family K hCarrier k N hAvoid)
    v w hv hw s t hs ht hCommon hStrictS hStrictT p r hr hrk hMeet

end SuccessorTree.V10

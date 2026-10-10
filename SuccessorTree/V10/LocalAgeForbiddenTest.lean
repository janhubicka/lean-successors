import SuccessorTree.V10.LocalAgePartialInsertion
import Mathlib.Tactic

/-!
# The forbidden-copy reduction in the common-socle local-age lemma

Assume one coordinate ell has been inserted in a forbidden-free source.
Copies avoiding ell already pull back to the source. For a nontrivial
irreducible copy containing ell, restrict the target L-structure to the
initial socle together with just the upper vertices of that copy. Every
upper vertex is linked to ell, hence its type is one of the prescribed
crossings. Deleting ell from this restricted witness still avoids the
forbidden family.

Therefore the manuscript's three-clause local age-test hypothesis excludes
the copy. This formalizes the forbidden-age half of Lemma 6.51 independently
of the later proof that the insertion acts as one global ShapeMap.
-/

namespace SuccessorTree.V10

/-- Keep arbitrary selected vertices while retaining every atomic relation. -/
def AgeTestModel.restrictCarrier
    {db du dd : Nat}
    (L : AgeTestModel db du dd) (P : Nat → Prop) :
    AgeTestModel db du dd :=
  { carrier := {x | x ∈ L.carrier ∧ P x}
    binary := L.binary
    unary := L.unary
    diagonal := L.diagonal }

/-- A realization whose image lies in the restricted carrier is unchanged. -/
theorem AgeTestModel.realizes_restrictCarrier
    {r db du dd : Nat}
    (L : AgeTestModel db du dd) (P : Nat → Prop)
    (F : ForbiddenAtomicPattern r db du dd)
    (f : Fin r → Nat) (h : L.Realizes F f)
    (hP : ∀ a, P (f a)) :
    (L.restrictCarrier P).Realizes F f := by
  obtain ⟨hMono, hIn, hB, hU, hD⟩ := h
  exact ⟨hMono, fun a => ⟨hIn a, hP a⟩, hB, hU, hD⟩

/-- Conversely every restricted realization is a realization upstairs. -/
theorem AgeTestModel.realizes_of_restrictCarrier
    {r db du dd : Nat}
    (L : AgeTestModel db du dd) (P : Nat → Prop)
    (F : ForbiddenAtomicPattern r db du dd)
    (f : Fin r → Nat)
    (h : (L.restrictCarrier P).Realizes F f) :
    L.Realizes F f := by
  obtain ⟨hMono, hIn, hB, hU, hD⟩ := h
  exact ⟨hMono, fun a => (hIn a).1, hB, hU, hD⟩

/-- Delete one vertex only at the carrier level. Atomic data stay unchanged. -/
def AgeTestModel.withoutVertex
    {db du dd : Nat}
    (L : AgeTestModel db du dd) (ell : Nat) :
    AgeTestModel db du dd :=
  L.restrictCarrier (fun x => x ≠ ell)

/-- Every forbidden copy in a carrier restriction avoiding the inserted
coordinate would pull back to the original source. -/
theorem IsLInsertion.restricted_without_inserted_avoids
    {db du dd : Nat}
    {A B : EnumeratedPartialStructure db du dd} {ell : Nat}
    (h : IsLInsertion A B ell)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (P : Nat → Prop) :
    ∀ bad, bad ∈ family →
      bad.Avoids ((B.L.restrictCarrier P).withoutVertex ell) := by
  intro bad hbad
  cases bad with
  | singleton F hNeutral =>
      rintro ⟨f, hf⟩
      have hRestricted :
          (B.L.restrictCarrier P).Realizes F f :=
        AgeTestModel.realizes_of_restrictCarrier
          (B.L.restrictCarrier P) (fun x => x ≠ ell) F f hf
      have hB : B.L.Realizes F f :=
        AgeTestModel.realizes_of_restrictCarrier B.L P F f hRestricted
      have hAway : ∀ a, f a ≠ ell := by
        intro a
        exact (hf.2.1 a).2
      exact (hAvoid (.singleton F hNeutral) hbad)
        ⟨_, h.realizes_away_projects F f hB hAway⟩
  | nontrivial r F hr hIrred =>
      rintro ⟨f, hf⟩
      have hRestricted :
          (B.L.restrictCarrier P).Realizes F f :=
        AgeTestModel.realizes_of_restrictCarrier
          (B.L.restrictCarrier P) (fun x => x ≠ ell) F f hf
      have hB : B.L.Realizes F f :=
        AgeTestModel.realizes_of_restrictCarrier B.L P F f hRestricted
      have hAway : ∀ a, f a ≠ ell := by
        intro a
        exact (hf.2.1 a).2
      exact (hAvoid (.nontrivial r F hr hIrred) hbad)
        ⟨_, h.realizes_away_projects F f hB hAway⟩

/-- Literal equality of the L-structure on the initial common socle. -/
def SameInitialL
    {db du dd : Nat}
    (A B : AgeTestModel db du dd) (ell : Nat) : Prop :=
  (∀ x, x ≤ ell → (x ∈ A.carrier ↔ x ∈ B.carrier)) ∧
  (∀ x y, x ≤ ell → y ≤ ell → ∀ t : Fin db,
    A.binary x y t = B.binary x y t) ∧
  (∀ x, x ≤ ell → ∀ t : Fin du,
    A.unary x t = B.unary x t) ∧
  (∀ x, x ≤ ell → ∀ t : Fin dd,
    A.diagonal x t = B.diagonal x t)

/-- Restricting the carrier by a predicate true on the whole initial socle
does not change that socle. -/
theorem SameInitialL.restrictCarrier
    {db du dd : Nat}
    {A B : AgeTestModel db du dd} {ell : Nat}
    (h : SameInitialL A B ell)
    (P : Nat → Prop) (hP : ∀ x, x ≤ ell → P x) :
    SameInitialL (A.restrictCarrier P) B ell := by
  rcases h with ⟨hC, hB, hU, hD⟩
  refine ⟨?_, hB, hU, hD⟩
  intro x hx
  simp [AgeTestModel.restrictCarrier, hP x hx, hC x hx]

/-- Every upper carrier vertex has one of the prescribed L-types through
the newly inserted coordinate. -/
def UpperTypesPrescribed
    {db du dd : Nat}
    (A : AgeTestModel db du dd) (ell : Nat)
    (Prescribed : RelationalPrefixType (ell + 1) db du dd → Prop) : Prop :=
  ∀ x, x ∈ A.carrier → ell < x →
    Prescribed (RelationalPrefixType.ofAgeModel A (ell + 1) x)

/-- The exact three-clause age-test assumption from Lemma 6.51, phrased
with a predicate for the finite set of prescribed upper crossing types. -/
def CommonSocleAgeTest
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (D : AgeTestModel db du dd) (ell : Nat)
    (Prescribed : RelationalPrefixType (ell + 1) db du dd → Prop) : Prop :=
  ∀ W : AgeTestModel db du dd,
    SameInitialL W D ell →
    UpperTypesPrescribed W ell Prescribed →
    (∀ bad, bad ∈ family → bad.Avoids (W.withoutVertex ell)) →
    ∀ bad, bad ∈ family → bad.Avoids W

/-- Restriction to the common socle and upper vertices of one forbidden copy. -/
def forbiddenWitnessCarrier
    {r : Nat} (ell : Nat) (e : Fin r → Nat) (x : Nat) : Prop :=
  x ≤ ell ∨ ∃ a : Fin r, e a = x ∧ ell < x

/-- A nontrivial irreducible forbidden copy containing ell gives precisely
the finite age witness to which the three-clause test applies. -/
theorem localAgeTest_excludes_nontrivial_inserted_copy
    {r db du dd : Nat}
    {A B : EnumeratedPartialStructure db du dd}
    (family : List (NormalizedForbidden db du dd))
    (D : AgeTestModel db du dd)
    (ell : Nat)
    (Prescribed : RelationalPrefixType (ell + 1) db du dd → Prop)
    (hInsert : IsLInsertion A B ell)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hSocle : SameInitialL B.L D ell)
    (hUpper : ∀ x, x < B.size → ell < x →
      (∃ t : Fin db,
        B.L.binary ell x t = true ∨ B.L.binary x ell t = true) →
      Prescribed (RelationalPrefixType.ofAgeModel B.L (ell + 1) x))
    (hAgeTest : CommonSocleAgeTest family D ell Prescribed)
    (F : ForbiddenAtomicPattern r db du dd)
    (hr : 1 < r) (hIrred : F.Irreducible)
    (hFmem : NormalizedForbidden.nontrivial r F hr hIrred ∈ family)
    (e : Fin r → Nat) (hCopy : B.L.Realizes F e)
    (hContains : ∃ a, e a = ell) :
    False := by
  classical
  let P := forbiddenWitnessCarrier ell e
  let W := B.L.restrictCarrier P
  have hPinitial : ∀ x, x ≤ ell → P x := by
    intro x hx
    exact Or.inl hx
  have hSocleW : SameInitialL W D ell := by
    exact hSocle.restrictCarrier P hPinitial
  obtain ⟨aell, haell⟩ := hContains
  have hUpperW : UpperTypesPrescribed W ell Prescribed := by
    intro x hxW hx
    have hxB : x ∈ B.L.carrier := hxW.1
    have hxSize : x < B.size := (B.carrier_iff x).1 hxB
    rcases hxW.2 with hlow | ⟨a, hea, _⟩
    · omega
    · have hane : aell ≠ a := by
        intro hEq
        subst a
        omega
      obtain ⟨t, ht⟩ := hIrred aell a hane
      have hBinary0 := hCopy.2.2.1 aell a hane t
      have hBinary1 := hCopy.2.2.1 a aell hane.symm t
      have hLinked :
          ∃ t : Fin db,
            B.L.binary ell x t = true ∨
              B.L.binary x ell t = true := by
        refine ⟨t, ?_⟩
        rw [haell, hea] at hBinary0 hBinary1
        simpa only [hBinary0, hBinary1] using ht
      have hp := hUpper x hxSize hx hLinked
      simpa [W, AgeTestModel.restrictCarrier] using hp
  have hDeleteAvoid :
      ∀ bad, bad ∈ family → bad.Avoids (W.withoutVertex ell) := by
    exact hInsert.restricted_without_inserted_avoids
      family hAvoid P
  have hWAvoid :
      ∀ bad, bad ∈ family → bad.Avoids W :=
    hAgeTest W hSocleW hUpperW hDeleteAvoid
  have hCopyW : W.Realizes F e := by
    apply AgeTestModel.realizes_restrictCarrier B.L P F e hCopy
    intro a
    by_cases hle : e a ≤ ell
    · exact Or.inl hle
    · exact Or.inr ⟨a, rfl, by omega⟩
  exact (hWAvoid (.nontrivial r F hr hIrred) hFmem) ⟨e, hCopyW⟩

/-- If the inserted singleton itself realizes no forbidden singleton, the
three-clause age test excludes ALL forbidden patterns in the target. -/
theorem localAgeTest_preserves_avoidance
    {db du dd : Nat}
    {A B : EnumeratedPartialStructure db du dd}
    (family : List (NormalizedForbidden db du dd))
    (D : AgeTestModel db du dd)
    (ell : Nat)
    (Prescribed : RelationalPrefixType (ell + 1) db du dd → Prop)
    (hInsert : IsLInsertion A B ell)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hSocle : SameInitialL B.L D ell)
    (hUpper : ∀ x, x < B.size → ell < x →
      (∃ t : Fin db,
        B.L.binary ell x t = true ∨ B.L.binary x ell t = true) →
      Prescribed (RelationalPrefixType.ofAgeModel B.L (ell + 1) x))
    (hInsertedSingleton : ∀ F hNeutral,
      NormalizedForbidden.singleton F hNeutral ∈ family →
      ¬ (B.L.Realizes F (fun _ => ell)))
    (hAgeTest : CommonSocleAgeTest family D ell Prescribed) :
    ∀ bad, bad ∈ family → bad.Avoids B.L := by
  intro bad hbad
  cases bad with
  | singleton F hNeutral =>
      rintro ⟨e, he⟩
      by_cases hAt : e 0 = ell
      · have heq : e = fun _ => ell := by
          funext a
          have ha : a = 0 := Subsingleton.elim _ _
          simpa [ha] using hAt
        exact hInsertedSingleton F hNeutral hbad (by simpa [heq] using he)
      · have hAway : ∀ a, e a ≠ ell := by
          intro a
          have ha : a = 0 := Subsingleton.elim _ _
          simpa [ha] using hAt
        exact (hAvoid (.singleton F hNeutral) hbad)
          ⟨_, hInsert.realizes_away_projects F e he hAway⟩
  | nontrivial r F hr hIrred =>
      rintro ⟨e, he⟩
      by_cases hContains : ∃ a, e a = ell
      · exact localAgeTest_excludes_nontrivial_inserted_copy
          family D ell Prescribed hInsert hAvoid hSocle hUpper hAgeTest
          F hr hIrred hbad e he hContains
      · have hAway : ∀ a, e a ≠ ell := by
          intro a ha
          exact hContains ⟨a, ha⟩
        exact (hAvoid (.nontrivial r F hr hIrred) hbad)
          ⟨_, hInsert.realizes_away_projects F e he hAway⟩

end SuccessorTree.V10

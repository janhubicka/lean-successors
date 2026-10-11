import Mathlib.Tactic

/-!
# Signature collisions and the lower/upper splice

Observation 6.52 of the v10 manuscript argues that two distinct age-change
levels cannot have the same forbidden-copy signature. The combinatorial
heart of that argument is an *ordered splice*: keep the lower vertices
of the first witness and the upper vertices of the second.

This module proves the splice at the level of finite unary, diagonal and
directed-binary atomic data. Its cross-pair hypothesis states the precise
piece of information that must come from the chosen originals: the complete
type of each prescribed upper vertex through the smaller tested level,
including the *new* coordinate. Both orientations and absent relations are
included. The actual KFpt type-to-original correspondence, and therefore
the unqualified manuscript signature-uniqueness lemma, remain open.

The proof makes no use of the auxiliary E predicate on the age-test
structure, as forbidden configurations are L-structures.
-/

namespace SuccessorTree.V10

/-- For a common signature, use the earlier witness on bottom entries and
the later witness on original-labelled entries. -/
def signatureSplice {r M : Nat}
    (signature : Fin r → Option (Fin M))
    (earlier later : Fin r → Nat) (i : Fin r) : Nat :=
  if signature i = none then earlier i else later i

/-- A common cut signature gives an increasing splice avoiding the later
tested level. The fact that bottom entries form an initial segment is
*derived* from the earlier witness's increasing enumeration. -/
theorem signatureSplice_order_avoids
    {r M : Nat} (signature : Fin r → Option (Fin M))
    (earlier later : Fin r → Nat) (ell0 ell1 : Nat)
    (hLevels : ell0 < ell1)
    (hEarlier : StrictMono earlier) (hLater : StrictMono later)
    (hCutEarlier : ∀ i, signature i = none ↔ earlier i ≤ ell0)
    (hCutLater : ∀ i, signature i = none ↔ later i ≤ ell1) :
    StrictMono (signatureSplice signature earlier later) ∧
      ∀ i, signatureSplice signature earlier later i ≠ ell1 := by
  have hOrder : StrictMono (signatureSplice signature earlier later) := by
    intro a b hab
    by_cases ha : signature a = none
    · by_cases hb : signature b = none
      · simpa [signatureSplice, ha, hb] using hEarlier hab
      · have hle : earlier a ≤ ell0 := (hCutEarlier a).mp ha
        have hgt : ell1 < later b := by
          by_contra h
          exact hb ((hCutLater b).mpr (by omega))
        simp only [signatureSplice, if_pos ha, if_neg hb]
        omega
    · by_cases hb : signature b = none
      · have hgt : ell0 < earlier a := by
          by_contra h
          exact ha ((hCutEarlier a).mpr (by omega))
        have hle : earlier b ≤ ell0 := (hCutEarlier b).mp hb
        have hmono := hEarlier hab
        omega
      · simpa [signatureSplice, ha, hb] using hLater hab
  refine ⟨hOrder, ?_⟩
  intro a
  by_cases ha : signature a = none
  · have hle : earlier a ≤ ell0 := (hCutEarlier a).mp ha
    have hne : earlier a ≠ ell1 := by omega
    simpa [signatureSplice, ha] using hne
  · have hgt : ell1 < later a := by
      by_contra h
      exact ha ((hCutLater a).mpr (by omega))
    have hne : later a ≠ ell1 := by omega
    simpa [signatureSplice, ha] using hne

/-- Whole directed-binary pattern of the splice. Lower--lower relations
come from the common initial socle, upper--upper from the later copy,
and lower--upper from the complete prescribed upper types.

The cross hypothesis is stated for BOTH orientations. Merely knowing
the types below ell0 (instead of through ell0+1) is insufficient. -/
theorem signatureSplice_binary
    {r M d : Nat} (signature : Fin r → Option (Fin M))
    (earlier later : Fin r → Nat)
    (B0 B1 : Nat → Nat → Fin d → Bool)
    (pattern : Fin r → Fin r → Fin d → Bool)
    (hOld : ∀ a b : Fin r, a ≠ b → ∀ t,
      B0 (earlier a) (earlier b) t = pattern a b t)
    (hNew : ∀ a b : Fin r, a ≠ b → ∀ t,
      B1 (later a) (later b) t = pattern a b t)
    (hCommon : ∀ a b : Fin r, a ≠ b →
      signature a = none → signature b = none → ∀ t,
      B1 (earlier a) (earlier b) t =
        B0 (earlier a) (earlier b) t)
    (hCross : ∀ a b : Fin r, a ≠ b →
      signature a = none → signature b ≠ none → ∀ t,
      B1 (earlier a) (later b) t =
          B0 (earlier a) (earlier b) t ∧
      B1 (later b) (earlier a) t =
          B0 (earlier b) (earlier a) t) :
    ∀ a b : Fin r, a ≠ b → ∀ t,
      B1 (signatureSplice signature earlier later a)
          (signatureSplice signature earlier later b) t =
        pattern a b t := by
  intro a b hab t
  by_cases ha : signature a = none
  · by_cases hb : signature b = none
    · have h := (hCommon a b hab ha hb t).trans (hOld a b hab t)
      simpa [signatureSplice, ha, hb] using h
    · have h := ((hCross a b hab ha hb t).1).trans (hOld a b hab t)
      simpa [signatureSplice, ha, hb] using h
  · by_cases hb : signature b = none
    · have h := ((hCross b a hab.symm hb ha t).2).trans (hOld a b hab t)
      simpa [signatureSplice, ha, hb] using h
    · simpa [signatureSplice, ha, hb] using hNew a b hab t

/-- The same lower/upper splice argument for arbitrary singleton bits.
This is used separately for unary symbols and for diagonal binary facts. -/
theorem signatureSplice_singleton
    {r M d : Nat} (signature : Fin r → Option (Fin M))
    (earlier later : Fin r → Nat)
    (R0 R1 : Nat → Fin d → Bool)
    (pattern : Fin r → Fin d → Bool)
    (hOld : ∀ a t, R0 (earlier a) t = pattern a t)
    (hNew : ∀ a t, R1 (later a) t = pattern a t)
    (hCommon : ∀ a t, signature a = none →
      R1 (earlier a) t = R0 (earlier a) t) :
    ∀ a t,
      R1 (signatureSplice signature earlier later a) t =
        pattern a t := by
  intro a t
  by_cases ha : signature a = none
  · have h := (hCommon a t ha).trans (hOld a t)
    simpa [signatureSplice, ha] using h
  · simpa [signatureSplice, ha] using hNew a t

/-- The precise finite-model consequence of a collision of signatures:
an induced, increasingly enumerated forbidden pattern in the later
age-test structure which does NOT use the later tested vertex.

All atom-agreement assumptions are explicit and may not be silently
replaced by one-way substructure containment. No E relations are needed. -/
theorem signatureSplice_inducedCopy
    {r M db du dd : Nat}
    (signature : Fin r → Option (Fin M))
    (earlier later : Fin r → Nat) (ell0 ell1 : Nat)
    (B0 B1 : Nat → Nat → Fin db → Bool)
    (U0 U1 : Nat → Fin du → Bool)
    (D0 D1 : Nat → Fin dd → Bool)
    (FB : Fin r → Fin r → Fin db → Bool)
    (FU : Fin r → Fin du → Bool)
    (FD : Fin r → Fin dd → Bool)
    (hLevels : ell0 < ell1)
    (hEarlier : StrictMono earlier) (hLater : StrictMono later)
    (hCutEarlier : ∀ i, signature i = none ↔ earlier i ≤ ell0)
    (hCutLater : ∀ i, signature i = none ↔ later i ≤ ell1)
    (hB0 : ∀ a b : Fin r, a ≠ b → ∀ t,
      B0 (earlier a) (earlier b) t = FB a b t)
    (hB1 : ∀ a b : Fin r, a ≠ b → ∀ t,
      B1 (later a) (later b) t = FB a b t)
    (hCommonB : ∀ a b : Fin r, a ≠ b →
      signature a = none → signature b = none → ∀ t,
      B1 (earlier a) (earlier b) t =
        B0 (earlier a) (earlier b) t)
    (hCrossB : ∀ a b : Fin r, a ≠ b →
      signature a = none → signature b ≠ none → ∀ t,
      B1 (earlier a) (later b) t =
          B0 (earlier a) (earlier b) t ∧
      B1 (later b) (earlier a) t =
          B0 (earlier b) (earlier a) t)
    (hU0 : ∀ a t, U0 (earlier a) t = FU a t)
    (hU1 : ∀ a t, U1 (later a) t = FU a t)
    (hCommonU : ∀ a t, signature a = none →
      U1 (earlier a) t = U0 (earlier a) t)
    (hD0 : ∀ a t, D0 (earlier a) t = FD a t)
    (hD1 : ∀ a t, D1 (later a) t = FD a t)
    (hCommonD : ∀ a t, signature a = none →
      D1 (earlier a) t = D0 (earlier a) t) :
    ∃ f : Fin r → Nat,
      StrictMono f ∧ (∀ a, f a ≠ ell1) ∧
      (∀ a b : Fin r, a ≠ b → ∀ t,
        B1 (f a) (f b) t = FB a b t) ∧
      (∀ a t, U1 (f a) t = FU a t) ∧
      (∀ a t, D1 (f a) t = FD a t) := by
  let f := signatureSplice signature earlier later
  obtain ⟨hOrder, hAvoid⟩ :=
    signatureSplice_order_avoids signature earlier later ell0 ell1
      hLevels hEarlier hLater hCutEarlier hCutLater
  refine ⟨f, hOrder, hAvoid, ?_, ?_, ?_⟩
  · exact signatureSplice_binary signature earlier later
      B0 B1 FB hB0 hB1 hCommonB hCrossB
  · exact signatureSplice_singleton signature earlier later
      U0 U1 FU hU0 hU1 hCommonU
  · exact signatureSplice_singleton signature earlier later
      D0 D1 FD hD0 hD1 hCommonD

end SuccessorTree.V10

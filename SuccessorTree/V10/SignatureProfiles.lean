import SuccessorTree.V10.SignatureSplice

/-!
# Where the v10 signature-spliced copy lives, and why its cross pairs agree

This is a separate interface for the two genuinely missing pieces in
Observation 6.52. An age-test witness is not a total structure on the natural
numbers: the splice must use vertices of its actual finite domain. Moreover,
knowing the *name* of an original is not enough unless its prescribed
upper type includes every lower--upper binary atom through the tested
coordinate, in both directions.

The lemma signatureSplice_in_laterDomain discharges the membership issue
from the fact that an age-test structure contains its initial socle. The
profile lemma reduces cross-atom equality to the two witnesses realizing
the same complete relation profile for every signature original.

The remaining hard adapter is to construct these profiles from concrete
KFpt partial types. No full signature-uniqueness theorem is asserted here.
-/

namespace SuccessorTree.V10

/-- A hybrid lower/upper witness really belongs to the later finite
age-test structure: earlier lower vertices lie in its initial socle,
and later upper vertices were already in that structure. -/
theorem signatureSplice_in_laterDomain
    {r M : Nat} (signature : Fin r → Option (Fin M))
    (earlier later : Fin r → Nat) (ell0 ell1 : Nat)
    (laterDomain : Set Nat)
    (hLevels : ell0 < ell1)
    (hCutEarlier : ∀ i, signature i = none ↔ earlier i ≤ ell0)
    (hSocle : ∀ v, v ≤ ell1 → v ∈ laterDomain)
    (hUpper : ∀ i, signature i ≠ none → later i ∈ laterDomain) :
    ∀ i, signatureSplice signature earlier later i ∈ laterDomain := by
  intro i
  by_cases h : signature i = none
  · have hlow : earlier i ≤ ell1 :=
      le_trans ((hCutEarlier i).mp h) (Nat.le_of_lt hLevels)
    simpa [signatureSplice, h] using hSocle (earlier i) hlow
  · simpa [signatureSplice, h] using hUpper i h

/-- If both witnesses prescribe the same complete profile for a named
upper original, the two ordered orientations of every cross pair agree.
This is exactly the missing age-test-to-original bridge, with the profile
hypotheses exposed rather than asserted to follow from equal signatures. -/
theorem signatureSplice_cross_of_sharedProfiles
    {r M d : Nat}
    (signature : Fin r → Option (Fin M))
    (earlier later : Fin r → Nat)
    (B0 B1 : Nat → Nat → Fin d → Bool)
    (outgoing incoming : Fin M → Nat → Fin d → Bool)
    (hOld : ∀ a b : Fin r, a ≠ b →
      signature a = none → ∀ v : Fin M,
      signature b = some v → ∀ t : Fin d,
        B0 (earlier a) (earlier b) t =
          outgoing v (earlier a) t ∧
        B0 (earlier b) (earlier a) t =
          incoming v (earlier a) t)
    (hNew : ∀ a b : Fin r, a ≠ b →
      signature a = none → ∀ v : Fin M,
      signature b = some v → ∀ t : Fin d,
        B1 (earlier a) (later b) t =
          outgoing v (earlier a) t ∧
        B1 (later b) (earlier a) t =
          incoming v (earlier a) t) :
    ∀ a b : Fin r, a ≠ b →
      signature a = none → signature b ≠ none → ∀ t : Fin d,
        B1 (earlier a) (later b) t =
          B0 (earlier a) (earlier b) t ∧
        B1 (later b) (earlier a) t =
          B0 (earlier b) (earlier a) t := by
  intro a b hab ha hb t
  cases h : signature b with
  | none =>
      exact False.elim (hb h)
  | some v =>
      obtain ⟨h0, h0'⟩ := hOld a b hab ha v h t
      obtain ⟨h1, h1'⟩ := hNew a b hab ha v h t
      exact ⟨h1.trans h0.symm, h1'.trans h0'.symm⟩

end SuccessorTree.V10

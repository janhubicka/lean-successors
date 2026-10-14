import SuccessorTree.V10.ActualCrossingSignature
import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# Signatures selected from genuine finite L-age witnesses

Observation 6.52 uses signatures whose non-bottom values are names
of ambient original vertices, NOT merely abstract partial types.
The checked signature splice already shows distinct selected levels
cannot have the same signature once both age witnesses have the
complete prescribed original types.

The missing paper-to-Lean bridge is to obtain the original labels
from each actual I3 age witness. This module formalizes the safe
intermediate step: given those original-labelled upper types, CHOOSE
one original at each actual upper copy position, obtain the signature
with its cut and full-type equations as theorems, and apply the
checked ambient splice. Thus no manual signature-type equalities
are assumptions of the final collision lemma below.

This remains conditional on proving that the actual I3 age witnesses
carry such original labels, and on their common initial socles.
It does not prove the final generation recurrence or upper bound.
-/

namespace SuccessorTree.V10

/-- Original-labelled upper vertices of one finite age witness give the
paper's signature: bottom below the cut and a genuine original above. -/
noncomputable def chosenAgeSignature
    {r M db du dd : Nat}
    (C W : AgeTestModel db du dd)
    (original : Fin M → Nat)
    (ell : Nat) (e : Fin r → Nat)
    (hOriginal : ∀ a : Fin r, ell < e a →
      ∃ v : Fin M,
        RelationalPrefixType.ofAgeModel W (ell + 1) (e a) =
          RelationalPrefixType.ofAgeModel C (ell + 1) (original v)) :
    Fin r → Option (Fin M) :=
  fun a =>
    if h : ell < e a then some (Classical.choose (hOriginal a h))
    else none

/-- Bottom entries are exactly the earlier part of the copy.
No assumption that the bottom entries form an initial segment is needed:
that follows later from strict monotonicity of the embedding. -/
theorem chosenAgeSignature_none_iff
    {r M db du dd : Nat}
    (C W : AgeTestModel db du dd)
    (original : Fin M → Nat)
    (ell : Nat) (e : Fin r → Nat)
    (hOriginal : ∀ a : Fin r, ell < e a →
      ∃ v : Fin M,
        RelationalPrefixType.ofAgeModel W (ell + 1) (e a) =
          RelationalPrefixType.ofAgeModel C (ell + 1) (original v))
    (a : Fin r) :
    chosenAgeSignature C W original ell e hOriginal a = none ↔ e a ≤ ell := by
  classical
  by_cases h : ell < e a
  · simp [chosenAgeSignature, h]
  · have hle : e a ≤ ell := Nat.le_of_not_gt h
    simp [chosenAgeSignature, h, hle]

/-- Every non-bottom chosen label already carries the exact full
induced L-type through the tested cut, including absent atoms. -/
theorem chosenAgeSignature_some_type
    {r M db du dd : Nat}
    (C W : AgeTestModel db du dd)
    (original : Fin M → Nat)
    (ell : Nat) (e : Fin r → Nat)
    (hOriginal : ∀ a : Fin r, ell < e a →
      ∃ v : Fin M,
        RelationalPrefixType.ofAgeModel W (ell + 1) (e a) =
          RelationalPrefixType.ofAgeModel C (ell + 1) (original v))
    (a : Fin r) (v : Fin M)
    (hSome : chosenAgeSignature C W original ell e hOriginal a = some v) :
    RelationalPrefixType.ofAgeModel W (ell + 1) (e a) =
      RelationalPrefixType.ofAgeModel C (ell + 1) (original v) := by
  classical
  have hUpper : ell < e a := by
    by_contra h
    have hle : e a ≤ ell := Nat.le_of_not_gt h
    have hNone := (chosenAgeSignature_none_iff
      C W original ell e hOriginal a).2 hle
    rw [hNone] at hSome
    cases hSome
  have hV : Classical.choose (hOriginal a hUpper) = v := by
    have hSome' : some (Classical.choose (hOriginal a hUpper)) = some v := by
      simpa [chosenAgeSignature, hUpper] using hSome
    exact Option.some.inj hSome'
  calc
    RelationalPrefixType.ofAgeModel W (ell + 1) (e a) =
        RelationalPrefixType.ofAgeModel C (ell + 1)
          (original (Classical.choose (hOriginal a hUpper))) :=
      Classical.choose_spec (hOriginal a hUpper)
    _ = RelationalPrefixType.ofAgeModel C (ell + 1) (original v) := by
      rw [hV]

/-- Two ordered forbidden-copy age witnesses at distinct tested levels
cannot share their CHOSEN ambient-original signature.

Compared with the previous splice endpoint, all signature-cut and
signature-to-full-type equations are derived from the literal
choice of an original at every upper copy vertex. The remaining
premises are exactly the ambient common socles, original-labelled
upper types, and absence of a forbidden copy after deletion of
the later tested coordinate. -/
theorem chosenAgeSignature_distinct_of_ambient_age_witnesses
    {r M db du dd : Nat}
    (P : ForbiddenAtomicPattern r db du dd)
    (C A0 A1 : AgeTestModel db du dd)
    (original : Fin M → Nat)
    (e0 e1 : Fin r → Nat) (ell0 ell1 : Nat)
    (hLevels : ell0 < ell1)
    (hOld : A0.Realizes P e0)
    (hNew : A1.Realizes P e1)
    (hCInitial : ∀ x, x ≤ ell1 → x ∈ C.carrier)
    (hSocle0 : SameInitialL A0 C ell0)
    (hSocle1 : SameInitialL A1 C ell1)
    (hOriginal0 : ∀ a : Fin r, ell0 < e0 a →
      ∃ v : Fin M,
        RelationalPrefixType.ofAgeModel A0 (ell0 + 1) (e0 a) =
          RelationalPrefixType.ofAgeModel C (ell0 + 1) (original v))
    (hOriginal1 : ∀ a : Fin r, ell1 < e1 a →
      ∃ v : Fin M,
        RelationalPrefixType.ofAgeModel A1 (ell1 + 1) (e1 a) =
          RelationalPrefixType.ofAgeModel C (ell1 + 1) (original v))
    (hDelete : ¬ ∃ f : Fin r → Nat,
      (A1.withoutVertex ell1).Realizes P f)
    (hSameSignature :
      chosenAgeSignature C A0 original ell0 e0 hOriginal0 =
        chosenAgeSignature C A1 original ell1 e1 hOriginal1) :
    False := by
  classical
  let signature :=
    chosenAgeSignature C A0 original ell0 e0 hOriginal0
  have hCut0 : ∀ i, signature i = none ↔ e0 i ≤ ell0 := by
    intro i
    exact chosenAgeSignature_none_iff
      C A0 original ell0 e0 hOriginal0 i
  have hCut1 : ∀ i, signature i = none ↔ e1 i ≤ ell1 := by
    intro i
    change (chosenAgeSignature C A0 original ell0 e0 hOriginal0) i =
      none ↔ e1 i ≤ ell1
    rw [hSameSignature]
    exact chosenAgeSignature_none_iff
      C A1 original ell1 e1 hOriginal1 i
  have hTypes0 : ∀ b v, signature b = some v →
      RelationalPrefixType.ofAgeModel A0 (ell0 + 1) (e0 b) =
        RelationalPrefixType.ofAgeModel C (ell0 + 1) (original v) := by
    intro b v hb
    exact chosenAgeSignature_some_type
      C A0 original ell0 e0 hOriginal0 b v hb
  have hTypes1 : ∀ b v, signature b = some v →
      RelationalPrefixType.ofAgeModel A1 (ell1 + 1) (e1 b) =
        RelationalPrefixType.ofAgeModel C (ell1 + 1) (original v) := by
    intro b v hb
    have hb' :
        chosenAgeSignature C A1 original ell1 e1 hOriginal1 b = some v := by
      rw [←hSameSignature]
      exact hb
    exact chosenAgeSignature_some_type
      C A1 original ell1 e1 hOriginal1 b v hb'
  have hType0 : ∀ b v, signature b = some v →
      fullAtomicTypePrefix A0.binary A0.unary A0.diagonal
          (ell0 + 1) (e0 b) =
        fullAtomicTypePrefix C.binary C.unary C.diagonal
          (ell0 + 1) (original v) := by
    intro b v hb
    exact equal_reduct_types_imply_fullAtomic
      A0 C (ell0 + 1) (e0 b) (original v) (hTypes0 b v hb)
  have hType1 : ∀ b v, signature b = some v →
      fullAtomicTypePrefix A1.binary A1.unary A1.diagonal
          (ell1 + 1) (e1 b) =
        fullAtomicTypePrefix C.binary C.unary C.diagonal
          (ell1 + 1) (original v) := by
    intro b v hb
    exact equal_reduct_types_imply_fullAtomic
      A1 C (ell1 + 1) (e1 b) (original v) (hTypes1 b v hb)
  have hLaterSocle : ∀ x, x ≤ ell1 → x ∈ A1.carrier := by
    intro x hx
    exact (hSocle1.1 x hx).2 (hCInitial x hx)
  have hAway : ∀ (f : Fin r → Nat), A1.Realizes P f →
      (∀ i, f i ≠ ell1) → False := by
    intro f hf hDifferent
    apply hDelete
    refine ⟨f, ?_⟩
    exact AgeTestModel.realizes_restrictCarrier
      A1 (fun x => x ≠ ell1) P f hf hDifferent
  exact signature_collision_impossible_of_ambient_types
    P C A0 A1 original signature e0 e1 ell0 ell1
    hLevels hOld hNew hCut0 hCut1 hLaterSocle
    (fun x y hx hy t => hSocle0.2.1 x y hx hy t)
    (fun x y hx hy t => hSocle1.2.1 x y hx hy t)
    (fun x hx t => hSocle0.2.2.1 x hx t)
    (fun x hx t => hSocle1.2.2.1 x hx t)
    (fun x hx t => hSocle0.2.2.2 x hx t)
    (fun x hx t => hSocle1.2.2.2 x hx t)
    hType0 hType1 hAway

end SuccessorTree.V10

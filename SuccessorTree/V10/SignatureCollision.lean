import SuccessorTree.V10.SignatureTypePrefix

/-!
# The conditional age-signature collision contradiction

This is the finite L-structure conclusion of Observation 6.52. Two age
witnesses at ell0 < ell1 with the same signature cannot both exist if:

* they agree with one common ambient initial socle on all unary/diagonal
  and directed binary atoms through ell0;
* each upper vertex in the two witnesses has the SAME full atomic type
  through ell0+1 as specified by its common signature original;
* the later witness has no forbidden induced ordered copy omitting ell1.

We express the second bullet by equality of complete atomic type prefixes,
not by one-way relation containment. This theorem packages the earlier
splice/order/domain facts and gives the actual contradiction.

To instantiate it in the manuscript, still prove that each KFpt age-change
witness really satisfies the full-prefix equality and common-socle
conditions. The theorem does not supply those missing geometric facts.
-/

namespace SuccessorTree.V10

/-- An enumerated age-test structure with a finite unary/binary
signature. The binary coordinates encode off-diagonal directed relations,
while diagonal values are separate singleton data. The carrier may be
finite in applications; no finiteness is needed for the splice proof. -/
structure AgeTestModel (db du dd : Nat) where
  carrier : Set Nat
  binary : Nat → Nat → Fin db → Bool
  unary : Nat → Fin du → Bool
  diagonal : Nat → Fin dd → Bool

/-- Fixed abstract forbidden pattern; no assumption of symmetry of
binary predicates. -/
structure ForbiddenAtomicPattern (r db du dd : Nat) where
  binary : Fin r → Fin r → Fin db → Bool
  unary : Fin r → Fin du → Bool
  diagonal : Fin r → Fin dd → Bool

/-- An induced ordered copy is an increasing map into the actual carrier
preserving both present and absent atomic tuples. -/
def AgeTestModel.Realizes
    {r db du dd : Nat}
    (A : AgeTestModel db du dd) (F : ForbiddenAtomicPattern r db du dd)
    (f : Fin r → Nat) : Prop :=
  StrictMono f ∧
  (∀ i, f i ∈ A.carrier) ∧
  (∀ a b : Fin r, a ≠ b → ∀ t : Fin db,
    A.binary (f a) (f b) t = F.binary a b t) ∧
  (∀ a : Fin r, ∀ t : Fin du,
    A.unary (f a) t = F.unary a t) ∧
  (∀ a : Fin r, ∀ t : Fin dd,
    A.diagonal (f a) t = F.diagonal a t)

/-- A collision in the original-labelled age signatures gives a
forbidden ordered copy in the later age-test witness avoiding its
tested vertex. The assumed absence of such a copy makes the collision
impossible. Every geometric input remains an explicit premise. -/
theorem signature_collision_impossible_of_common_full_types
    {r M db du dd : Nat}
    (F : ForbiddenAtomicPattern r db du dd)
    (A0 A1 : AgeTestModel db du dd)
    (signature : Fin r → Option (Fin M))
    (e0 e1 : Fin r → Nat) (ell0 ell1 : Nat)
    (hLevels : ell0 < ell1)
    (hOld : A0.Realizes F e0)
    (hNew : A1.Realizes F e1)
    (hCutOld : ∀ i, signature i = none ↔ e0 i ≤ ell0)
    (hCutNew : ∀ i, signature i = none ↔ e1 i ≤ ell1)
    (hLaterSocle : ∀ x, x ≤ ell1 → x ∈ A1.carrier)
    (hCommonBinary : ∀ x y, x ≤ ell0 → y ≤ ell0 →
      ∀ t : Fin db, A1.binary x y t = A0.binary x y t)
    (hCommonUnary : ∀ x, x ≤ ell0 →
      ∀ t : Fin du, A1.unary x t = A0.unary x t)
    (hCommonDiagonal : ∀ x, x ≤ ell0 →
      ∀ t : Fin dd, A1.diagonal x t = A0.diagonal x t)
    (hOriginalTypes : ∀ b, signature b ≠ none →
      fullAtomicTypePrefix A0.binary A0.unary A0.diagonal
          (ell0 + 1) (e0 b) =
        fullAtomicTypePrefix A1.binary A1.unary A1.diagonal
          (ell0 + 1) (e1 b))
    (hNoForbiddenAway : ∀ f : Fin r → Nat,
      A1.Realizes F f → (∀ i, f i ≠ ell1) → False) :
    False := by
  rcases hOld with ⟨hOrder0, _, hB0, hU0, hD0⟩
  rcases hNew with ⟨hOrder1, hDomain1, hB1, hU1, hD1⟩
  let splice := signatureSplice signature e0 e1
  have hOrderAvoid :=
    signatureSplice_order_avoids signature e0 e1 ell0 ell1
      hLevels hOrder0 hOrder1 hCutOld hCutNew
  have hDomain : ∀ i, splice i ∈ A1.carrier :=
    signatureSplice_in_laterDomain signature e0 e1 ell0 ell1
      A1.carrier hLevels hCutOld hLaterSocle
      (by intro i _; exact hDomain1 i)
  have hCommonB : ∀ a b : Fin r, a ≠ b →
      signature a = none → signature b = none → ∀ t : Fin db,
      A1.binary (e0 a) (e0 b) t =
        A0.binary (e0 a) (e0 b) t := by
    intro a b _ ha hb t
    exact hCommonBinary (e0 a) (e0 b)
      ((hCutOld a).mp ha) ((hCutOld b).mp hb) t
  have hLower : ∀ a, signature a = none → e0 a < ell0 + 1 := by
    intro a ha
    have hle := (hCutOld a).mp ha
    omega
  have hCross :=
    signatureSplice_cross_of_fullTypePrefixes signature e0 e1
      A0.binary A1.binary A0.unary A1.unary
      A0.diagonal A1.diagonal (ell0 + 1) hLower hOriginalTypes
  have hBinary : ∀ a b : Fin r, a ≠ b → ∀ t : Fin db,
      A1.binary (splice a) (splice b) t =
        F.binary a b t :=
    signatureSplice_binary signature e0 e1
      A0.binary A1.binary F.binary hB0 hB1 hCommonB hCross
  have hCommonU : ∀ a : Fin r, ∀ t : Fin du,
      signature a = none →
      A1.unary (e0 a) t = A0.unary (e0 a) t := by
    intro a t ha
    exact hCommonUnary (e0 a) ((hCutOld a).mp ha) t
  have hCommonD : ∀ a : Fin r, ∀ t : Fin dd,
      signature a = none →
      A1.diagonal (e0 a) t = A0.diagonal (e0 a) t := by
    intro a t ha
    exact hCommonDiagonal (e0 a) ((hCutOld a).mp ha) t
  have hUnary : ∀ a : Fin r, ∀ t : Fin du,
      A1.unary (splice a) t = F.unary a t :=
    signatureSplice_singleton signature e0 e1
      A0.unary A1.unary F.unary hU0 hU1 hCommonU
  have hDiagonal : ∀ a : Fin r, ∀ t : Fin dd,
      A1.diagonal (splice a) t = F.diagonal a t :=
    signatureSplice_singleton signature e0 e1
      A0.diagonal A1.diagonal F.diagonal hD0 hD1 hCommonD
  exact hNoForbiddenAway splice
    ⟨hOrderAvoid.1, hDomain, hBinary, hUnary, hDiagonal⟩
    hOrderAvoid.2

end SuccessorTree.V10

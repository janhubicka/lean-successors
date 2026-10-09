import SuccessorTree.V10.SignatureCollision

/-!
# Transporting signatures through a common ambient partial structure

The v10 proof of Observation 6.52 uses one fixed ambient partial
structure C. At an age-change level ell an upper witness vertex is
prescribed to have, through ell+1, the type of a chosen original of C.
The same original can occur in a signature at two different levels.

This module formalizes the restriction of full atomic types and uses it
to assemble the signature-collision contradiction from precisely these
two *ambient* conditions:

1. both age-test witnesses have the induced initial L-socle of C;
2. an upper witness vertex labeled by original v has the complete
   L-type of C's vertex v through the corresponding cut.

The first condition is the manuscript's common socle. The second is
the one-level type-prescription condition and must eventually be
obtained from the actual KFpt crossing map. The auxiliary E predicate
belongs to the partial-type construction, not the forbidden L-copy.

For a language with nullary symbols, their interpretation is fixed
through the ambient class; these records encode its unary and binary
part only. No statement about nullary normalization is made here.
-/

namespace SuccessorTree.V10

/-- Restriction of the complete atomic type of a distinguished vertex
from a longer initial socle to a shorter one. -/
def FullAtomicTypePrefix.restrict
    {m n db du dd : Nat}
    (T : FullAtomicTypePrefix n db du dd)
    (h : m ≤ n) : FullAtomicTypePrefix m db du dd :=
  { unary := T.unary
    diagonal := T.diagonal
    fromSocle := fun x t =>
      T.fromSocle ⟨x.val, lt_of_lt_of_le x.isLt h⟩ t
    toSocle := fun x t =>
      T.toSocle ⟨x.val, lt_of_lt_of_le x.isLt h⟩ t }

/-- Cutting a complete atomic type agrees exactly with extracting that
type from the shorter socle. Both directed relation patterns are
preserved; the singleton data do not change. -/
@[simp] theorem fullAtomicTypePrefix_restrict
    {db du dd : Nat}
    (B : Nat → Nat → Fin db → Bool)
    (U : Nat → Fin du → Bool)
    (D : Nat → Fin dd → Bool)
    (m n v : Nat) (h : m ≤ n) :
    (fullAtomicTypePrefix B U D n v).restrict h =
      fullAtomicTypePrefix B U D m v := rfl

/-- An upper vertex in A0 has the earlier-cut type of original v in
C; an upper vertex in A1 has the later-cut type of that same original.
Consequently they have the same earlier-cut type. This is the
nontrivial functorial step missing in the unqualified signature proof. -/
theorem common_original_gives_equal_short_types
    {db du dd : Nat}
    (C A0 A1 : AgeTestModel db du dd)
    (original upper0 upper1 cut0 cut1 : Nat)
    (hCuts : cut0 ≤ cut1)
    (hEarlierType :
      fullAtomicTypePrefix A0.binary A0.unary A0.diagonal
          cut0 upper0 =
        fullAtomicTypePrefix C.binary C.unary C.diagonal
          cut0 original)
    (hLaterType :
      fullAtomicTypePrefix A1.binary A1.unary A1.diagonal
          cut1 upper1 =
        fullAtomicTypePrefix C.binary C.unary C.diagonal
          cut1 original) :
    fullAtomicTypePrefix A0.binary A0.unary A0.diagonal
        cut0 upper0 =
      fullAtomicTypePrefix A1.binary A1.unary A1.diagonal
        cut0 upper1 := by
  have hReduced := congrArg
    (fun T : FullAtomicTypePrefix cut1 db du dd =>
      T.restrict hCuts) hLaterType
  simp only [fullAtomicTypePrefix_restrict] at hReduced
  exact hEarlierType.trans hReduced.symm

/-- Every displayed signature is originally a map with optional
*vertex*-valued labels. Giving each label the actual ambient vertex
is enough to pull its two prescribed upper types to a common cut.

This is a genuine reduction of Observation 6.52: the single
paper-specific requirement left in these hypotheses is the exact
"prescribed type through ell+1" equality of the L-reducts in the
actual KFpt one-level age-test witnesses. -/
theorem signature_collision_impossible_of_ambient_types
    {r M db du dd : Nat}
    (F : ForbiddenAtomicPattern r db du dd)
    (C A0 A1 : AgeTestModel db du dd)
    (original : Fin M → Nat)
    (signature : Fin r → Option (Fin M))
    (e0 e1 : Fin r → Nat) (ell0 ell1 : Nat)
    (hLevels : ell0 < ell1)
    (hOld : A0.Realizes F e0)
    (hNew : A1.Realizes F e1)
    (hCutOld : ∀ i, signature i = none ↔ e0 i ≤ ell0)
    (hCutNew : ∀ i, signature i = none ↔ e1 i ≤ ell1)
    (hLaterSocle : ∀ x, x ≤ ell1 → x ∈ A1.carrier)
    (hSocle0B : ∀ x y, x ≤ ell0 → y ≤ ell0 →
      ∀ t : Fin db, A0.binary x y t = C.binary x y t)
    (hSocle1B : ∀ x y, x ≤ ell1 → y ≤ ell1 →
      ∀ t : Fin db, A1.binary x y t = C.binary x y t)
    (hSocle0U : ∀ x, x ≤ ell0 →
      ∀ t : Fin du, A0.unary x t = C.unary x t)
    (hSocle1U : ∀ x, x ≤ ell1 →
      ∀ t : Fin du, A1.unary x t = C.unary x t)
    (hSocle0D : ∀ x, x ≤ ell0 →
      ∀ t : Fin dd, A0.diagonal x t = C.diagonal x t)
    (hSocle1D : ∀ x, x ≤ ell1 →
      ∀ t : Fin dd, A1.diagonal x t = C.diagonal x t)
    (hType0 : ∀ b v, signature b = some v →
      fullAtomicTypePrefix A0.binary A0.unary A0.diagonal
          (ell0 + 1) (e0 b) =
        fullAtomicTypePrefix C.binary C.unary C.diagonal
          (ell0 + 1) (original v))
    (hType1 : ∀ b v, signature b = some v →
      fullAtomicTypePrefix A1.binary A1.unary A1.diagonal
          (ell1 + 1) (e1 b) =
        fullAtomicTypePrefix C.binary C.unary C.diagonal
          (ell1 + 1) (original v))
    (hNoForbiddenAway : ∀ f : Fin r → Nat,
      A1.Realizes F f → (∀ i, f i ≠ ell1) → False) :
    False := by
  have hCommonB : ∀ x y, x ≤ ell0 → y ≤ ell0 →
      ∀ t : Fin db, A1.binary x y t = A0.binary x y t := by
    intro x y hx hy t
    have hxl : x ≤ ell1 := le_trans hx (Nat.le_of_lt hLevels)
    have hyl : y ≤ ell1 := le_trans hy (Nat.le_of_lt hLevels)
    exact (hSocle1B x y hxl hyl t).trans
      (hSocle0B x y hx hy t).symm
  have hCommonU : ∀ x, x ≤ ell0 →
      ∀ t : Fin du, A1.unary x t = A0.unary x t := by
    intro x hx t
    exact (hSocle1U x (le_trans hx (Nat.le_of_lt hLevels)) t).trans
      (hSocle0U x hx t).symm
  have hCommonD : ∀ x, x ≤ ell0 →
      ∀ t : Fin dd, A1.diagonal x t = A0.diagonal x t := by
    intro x hx t
    exact (hSocle1D x (le_trans hx (Nat.le_of_lt hLevels)) t).trans
      (hSocle0D x hx t).symm
  have hCommonTypes : ∀ b, signature b ≠ none →
      fullAtomicTypePrefix A0.binary A0.unary A0.diagonal
          (ell0 + 1) (e0 b) =
        fullAtomicTypePrefix A1.binary A1.unary A1.diagonal
          (ell0 + 1) (e1 b) := by
    intro b hb
    cases hs : signature b with
    | none => exact False.elim (hb hs)
    | some v =>
      exact common_original_gives_equal_short_types
        C A0 A1 (original v) (e0 b) (e1 b)
        (ell0 + 1) (ell1 + 1)
        (by omega) (hType0 b v hs) (hType1 b v hs)
  exact signature_collision_impossible_of_common_full_types
    F A0 A1 signature e0 e1 ell0 ell1
    hLevels hOld hNew hCutOld hCutNew hLaterSocle
    hCommonB hCommonU hCommonD hCommonTypes hNoForbiddenAway

end SuccessorTree.V10

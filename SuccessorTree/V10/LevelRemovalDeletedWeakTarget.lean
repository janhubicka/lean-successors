import SuccessorTree.V10.LevelRemovalRawPrefix
import SuccessorTree.V10.AdmissibleKptPrefix
import Mathlib.Tactic

/-!
# Admissibility of a deleted complete predecessor is inherited from above

The intended M2 weak successor argument takes an actual weak image
step d≤F(b), deletes the fixed coordinate m, and needs the resulting
complete L+ record to be a genuine Kpt node.

There is no need to choose a fresh finite representative of d.
If the intrinsic deleted complete record of F(b) has already been
proved admissible, complete raw deletion/prefix compatibility makes
the deletion of d its actual shorter prefix. The already checked
admissible-prefix theorem supplies the witness.

This is valid for any two comparable admissible nodes and any common
deleted socle coordinate; it adds no E-age hypothesis, successor law,
or M2 axiom.
-/

namespace SuccessorTree.V10

/-- Deleting the same ordinary coordinate from a predecessor of a
type with admissible deleted output again gives an admissible
complete Kpt type. The output inherits a genuine finite witness from
the upper type; none is chosen from the original predecessor. -/
theorem admissible_deleted_raw_predecessor
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {d b : AdmissibleKptNode family}
    (hdb : d ≤ b)
    (m : Nat) (hmd : m < d.1.1)
    (hUpper : IsAdmissibleRawType family
      (rawPartialTypeDeleteAt b.1 m
        (lt_of_lt_of_le hmd (LevelTree.level_le_of_le hdb)))) :
    IsAdmissibleRawType family
      (rawPartialTypeDeleteAt d.1 m hmd) := by
  let hmb : m < b.1.1 :=
    lt_of_lt_of_le hmd (LevelTree.level_le_of_le hdb)
  let X := rawPartialTypeDeleteAt d.1 m hmd
  let Y := rawPartialTypeDeleteAt b.1 m hmb
  have hPrefix : X ≤ Y :=
    rawPartialTypeDeleteAt_prefix hdb m hmd
  obtain ⟨hCut,hRecord⟩ := hPrefix
  have hAdPrefix :
      IsAdmissibleRawType family
        (⟨X.1,Y.2.restrict hCut⟩ :
          RawPartialTypeNode db du dd) :=
    admissibleRawType_closed_under_prefix family
      hUpper X.1 hCut
  have hEq :
      (⟨X.1,Y.2.restrict hCut⟩ :
        RawPartialTypeNode db du dd) = X :=
    congrArg (Sigma.mk X.1) hRecord.symm
  have hAdX : IsAdmissibleRawType family X :=
    Eq.mp (congrArg (IsAdmissibleRawType family) hEq) hAdPrefix
  exact hAdX

/-- The same fact expressed with actual admissible source and upper
output nodes, giving the short Kpt node needed for a genuine
weak-successor witness after deletion. -/
theorem deleted_predecessor_node_of_admissible_upper
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (d b b' : AdmissibleKptNode family)
    (hdb : d ≤ b)
    (m : Nat) (hmd : m < d.1.1)
    (hb' : b'.1 =
      rawPartialTypeDeleteAt b.1 m
        (lt_of_lt_of_le hmd (LevelTree.level_le_of_le hdb))) :
    ∃ d' : AdmissibleKptNode family,
      d'.1 = rawPartialTypeDeleteAt d.1 m hmd ∧
      d' ≤ b' := by
  have hAdUpper : IsAdmissibleRawType family
      (rawPartialTypeDeleteAt b.1 m
        (lt_of_lt_of_le hmd (LevelTree.level_le_of_le hdb))) := by
    rw [←hb']
    exact b'.2
  have hAdLower :=
    admissible_deleted_raw_predecessor family hdb m hmd hAdUpper
  let d' : AdmissibleKptNode family :=
    ⟨rawPartialTypeDeleteAt d.1 m hmd, hAdLower⟩
  refine ⟨d',rfl,?_⟩
  change (rawPartialTypeDeleteAt d.1 m hmd) ≤ b'.1
  rw [hb']
  exact rawPartialTypeDeleteAt_prefix hdb m hmd

end SuccessorTree.V10

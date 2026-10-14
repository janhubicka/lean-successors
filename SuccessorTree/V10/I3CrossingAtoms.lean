import SuccessorTree.V10.RelationalTypeReduct
import SuccessorTree.V10.ChosenAgeSignatures
import Mathlib.Tactic

/-!
# Full directed crossing records of a named I3 upper original

In Lemma 6.53 the lower forbidden-copy vertices are moved inside
the common initial L-socle of the age witness, but the upper
vertices stay fixed. For the lower--upper zone, one needs equality
of BOTH directed binary relations to a chosen ambient original
through the entire tested cut, not merely one positive edge.

The complete induced L-type already contains exactly these bits.
The lemmas here project the source's full original-name equality
to all incident atoms and singleton facts. This gives a small,
kernel-checkable bridge from Observation 6.52 to the mixed
relocation argument without introducing E in the age witness.

The final numeric H-generation relocation remains separate. No
axioms or definitions of the successor manuscript are changed.
-/

namespace SuccessorTree.V10

/-- Equality of complete finite L-types determines every directed
edge, nonedge and loop between the distinguished upper vertex and
the initial socle, plus all unary and diagonal facts of that upper
vertex. The same argument works even if the old upper address is
outside the socle: `none` is the distinguished type vertex. -/
theorem fullOriginalType_all_incident_atoms
    {db du dd : Nat}
    (W C : AgeTestModel db du dd)
    (cut upper original : Nat)
    (hType :
      RelationalPrefixType.ofAgeModel W cut upper =
        RelationalPrefixType.ofAgeModel C cut original) :
    (∀ (x : Nat), x < cut → ∀ t : Fin db,
      W.binary x upper t = C.binary x original t ∧
      W.binary upper x t = C.binary original x t) ∧
    (∀ t : Fin db, W.binary upper upper t =
      C.binary original original t) ∧
    (∀ t : Fin du, W.unary upper t = C.unary original t) ∧
    (∀ t : Fin dd, W.diagonal upper t = C.diagonal original t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx t
    let ix : Fin cut := ⟨x, hx⟩
    have hForward := congrArg
      (fun T : RelationalPrefixType cut db du dd =>
        T.binary (some ix) none t) hType
    have hBackward := congrArg
      (fun T : RelationalPrefixType cut db du dd =>
        T.binary none (some ix) t) hType
    exact ⟨hForward, hBackward⟩
  · intro t
    exact congrArg
      (fun T : RelationalPrefixType cut db du dd =>
        T.binary none none t) hType
  · intro t
    exact congrArg
      (fun T : RelationalPrefixType cut db du dd =>
        T.unary none t) hType
  · intro t
    exact congrArg
      (fun T : RelationalPrefixType cut db du dd =>
        T.diagonal none t) hType

/-- An actual original name for an upper I3 witness vertex supplies
every incident atom through the tested coordinate ell. In particular,
`x=ell` is included: the named original controls the relation to
the new tested vertex itself, which is essential for Lemma 6.53. -/
theorem chosenAgeSignature_some_incident_atoms
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
    (∀ x, x ≤ ell → ∀ t : Fin db,
      W.binary x (e a) t = C.binary x (original v) t ∧
      W.binary (e a) x t = C.binary (original v) x t) ∧
    (∀ t : Fin db, W.binary (e a) (e a) t =
      C.binary (original v) (original v) t) ∧
    (∀ t : Fin du, W.unary (e a) t =
      C.unary (original v) t) ∧
    (∀ t : Fin dd, W.diagonal (e a) t =
      C.diagonal (original v) t) := by
  have hType := chosenAgeSignature_some_type
    C W original ell e hOriginal a v hSome
  simpa only [Nat.lt_succ_iff] using
    fullOriginalType_all_incident_atoms
      W C (ell + 1) (e a) (original v) hType

end SuccessorTree.V10

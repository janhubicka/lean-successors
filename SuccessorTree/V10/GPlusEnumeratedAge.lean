import SuccessorTree.V10.GPlusInducedAgeTransfer

/-!
# Lemma 6.41: the enumerated G+ L-reduct omits the forbidden family

Read the exact Definition 6.40 atoms along any size-nondecreasing sequence
of canonical G+ vertices. Every ordered induced forbidden copy would give
one of the finite candidates excluded by the full induced-age transfer.

This conclusion allows equal sizes in the enumeration. It does not assume
that the sequence is injective or onto: those properties are needed to
identify it with the paper's enumeration of ALL G+ vertices, but not for
the forbidden-age conclusion itself. Construction of such an exhaustive
size-respecting enumeration remains a separate obligation.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- Exact L-atoms read along a sequence of G+ vertices. The enumeration
order is the inherited order of the carrier Nat. -/
noncomputable def finiteGPlusEnumeratedL
    (enumerate : Nat → FiniteGPlusVertex family) : AgeTestModel db du dd where
  carrier := Set.univ
  binary := fun x y t => finiteGPlusBinary (enumerate x) (enumerate y) t
  unary := fun x t => finiteGPlusUnary (enumerate x) t
  diagonal := fun x t => finiteGPlusDiagonal (enumerate x) t

/-- Actual forbidden-age conclusion, for every normalized forbidden
pattern, not merely the positive-relation comparability argument. -/
theorem finiteGPlusEnumeratedL_avoids_family
    (enumerate : Nat → FiniteGPlusVertex family)
    (hSize : Monotone (fun x : Nat => (enumerate x).val.size)) :
    ∀ bad, bad ∈ family → bad.Avoids (finiteGPlusEnumeratedL enumerate) := by
  intro bad hMem
  cases bad with
  | singleton F hNeutral =>
      rintro ⟨e,hCopy⟩
      exact finiteGPlus_excludes_singleton F hNeutral hMem (enumerate (e 0))
        (hCopy.2.2.2.1 0) (hCopy.2.2.2.2 0)
  | nontrivial r F hr hIrred =>
      rintro ⟨e,hCopy⟩
      exact finiteGPlus_excludes_nontrivial F hr hIrred hMem
        (fun a => enumerate (e a)) (hSize.comp hCopy.1.monotone)
        hCopy.2.2.1 hCopy.2.2.2.1 hCopy.2.2.2.2

end SuccessorTree.V10

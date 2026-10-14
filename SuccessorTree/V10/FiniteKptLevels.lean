import SuccessorTree.V10.AdmissibleKptPrefix
import SuccessorTree.V10.RawPrefixOrder
import Mathlib.Tactic

/-!
# Finite levels of the actual normalized Kpt prefix forest

A complete finite unary/binary L+ partial-type record on a fixed
socle length d has only finitely many bits: the L-reduct contains
two-argument directed binary data, unary data, and diagonal
singleton data, while E is another binary Boolean matrix.
The record has NO unrestricted extra information.

Therefore the raw prefix forest has finite levels. This conclusion
passes automatically to the admissible forbidden-free family as
a subtype, *without* assuming any finite branching axiom of Kpt.
The argument does not require that every raw type be admissible.

This discharges the level-finiteness input of the paper's finite
Kpt tree. A genuine LevelTree instance still needs the conditional
meet and representation of predecessor order on the admissible
family, which are treated separately.
-/

namespace SuccessorTree.V10

/-- At a fixed socle length, the entire induced L-reduct is a
finite tuple of finite Boolean-valued function tables. -/
instance finiteRelationalPrefixType (cut db du dd : Nat) :
    Finite (RelationalPrefixType cut db du dd) := by
  classical
  refine Finite.of_injective
    (fun T : RelationalPrefixType cut db du dd =>
      ((T.binary, T.unary), T.diagonal)) ?_
  intro a b h
  have hBinary : a.binary = b.binary :=
    congrArg (fun x => x.1.1) h
  have hUnary : a.unary = b.unary :=
    congrArg (fun x => x.1.2) h
  have hDiagonal : a.diagonal = b.diagonal :=
    congrArg (fun x => x.2) h
  apply RelationalPrefixType.eq_of_atoms
  · intro x y t
    exact congrFun (congrFun (congrFun hBinary x) y) t
  · intro x t
    exact congrFun (congrFun hUnary x) t
  · intro x t
    exact congrFun (congrFun hDiagonal x) t

/-- Including the auxiliary E bits, a complete L+ type over a
fixed finite socle has finitely many possible values. -/
instance finitePartialTypeWithE (cut db du dd : Nat) :
    Finite (PartialTypeWithE cut db du dd) := by
  classical
  refine Finite.of_injective
    (fun T : PartialTypeWithE cut db du dd =>
      (T.lReduct, T.eRelation)) ?_
  intro a b h
  apply PartialTypeWithE.eq_of_atoms
  · exact congrArg (fun p => p.1) h
  · intro x y
    have hE := congrArg (fun p => p.2) h
    exact congrFun (congrFun hE x) y

/-- A level of the raw prefix forest consists of exactly the images
of all complete L+ records with that fixed socle length. -/
theorem rawPartialTypeLevel_finite
    (db du dd cut : Nat) :
    Set.Finite {N : RawPartialTypeNode db du dd | N.1 = cut} := by
  classical
  let embed : PartialTypeWithE cut db du dd →
      RawPartialTypeNode db du dd :=
    fun T => ⟨cut, T⟩
  have hLevel :
      {N : RawPartialTypeNode db du dd | N.1 = cut} =
        Set.range embed := by
    ext N
    constructor
    · intro h
      rcases N with ⟨n, T⟩
      change n = cut at h
      subst n
      exact ⟨T, rfl⟩
    · rintro ⟨T, h⟩
      exact congrArg Sigma.fst h.symm
  rw [hLevel]
  exact Set.finite_range embed

/-- The actual admissible, forbidden-free Kpt family also has finite
levels, as a subset of the finite raw level. No admissibility of
arbitrary raw records is asserted or used. -/
theorem admissibleRawTypeLevel_finite
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (cut : Nat) :
    Set.Finite
      {N : {N : RawPartialTypeNode db du dd //
          IsAdmissibleRawType family N} | N.1.1 = cut} := by
  classical
  let embedding :
      {N : RawPartialTypeNode db du dd //
        IsAdmissibleRawType family N} →
      RawPartialTypeNode db du dd :=
    fun N => N.1
  have hinj : Set.InjOn embedding
      (embedding ⁻¹'
        {N : RawPartialTypeNode db du dd | N.1 = cut}) := by
    intro a _ b _ heq
    exact Subtype.ext heq
  have hFinite :=
    (rawPartialTypeLevel_finite db du dd cut).preimage hinj
  change Set.Finite (embedding ⁻¹'
    {N : RawPartialTypeNode db du dd | N.1 = cut})
  exact hFinite

end SuccessorTree.V10

import SuccessorTree.V10.GPlusIrreducibleChain

/-!
# Lemma 6.41: full induced transfer into the maximal finite partial structure

An irreducible candidate in G+ lies on one prefix chain. Its vertex A+
represents coordinate |A+|-1 in the largest code on that chain. Prefix
restriction preserves every unary, diagonal and directed binary bit,
including false bits. Thus the entire induced candidate is realized in
one forbidden-free finite partial structure, a contradiction.

Only a nondecreasing size enumeration is needed: irreducibility itself
forces strictly increasing sizes inside a candidate. Singleton patterns
are included separately; no auxiliary E relation is imposed on L-copies.
This file does not construct the countable G-omega enumeration or finish
the later H-to-G-to-Ramsey transfer.
-/

namespace SuccessorTree.V10

namespace FinitePartialCode

variable {db du dd : Nat}

/-- Interpret the finite table on its actual carrier. Off-carrier values
are set to false and have no role in induced copies. -/
def toAgeModel (C : FinitePartialCode db du dd) : AgeTestModel db du dd where
  carrier := {x | x < C.size}
  binary := fun x y t =>
    if hx : x < C.size then
      if hy : y < C.size then C.binary ⟨x,hx⟩ ⟨y,hy⟩ t else false
    else false
  unary := fun x t =>
    if hx : x < C.size then C.unary ⟨x,hx⟩ t else false
  diagonal := fun x t =>
    if hx : x < C.size then C.diagonal ⟨x,hx⟩ t else false

/-- On-carrier induced copies of a code are copies in its original
partial structure; arbitrary off-carrier values are irrelevant. -/
theorem realizes_ofEnumerated
    {r : Nat} (A : EnumeratedPartialStructure db du dd)
    (F : ForbiddenAtomicPattern r db du dd) (f : Fin r → Nat)
    (h : (ofEnumerated A).toAgeModel.Realizes F f) :
    A.L.Realizes F f := by
  have hBound : ∀ a, f a < A.size := by
    intro a
    exact h.2.1 a
  refine ⟨h.1, fun a => (A.carrier_iff (f a)).2 (hBound a), ?_, ?_, ?_⟩
  · intro a b hab t
    simpa [toAgeModel, ofEnumerated, hBound a, hBound b]
      using h.2.2.1 a b hab t
  · intro a t
    simpa [toAgeModel, ofEnumerated, hBound a] using h.2.2.2.1 a t
  · intro a t
    simpa [toAgeModel, ofEnumerated, hBound a] using h.2.2.2.2 a t

/-- Initial-segment equality preserves both orientations and both
Boolean values of every on-carrier binary atom. -/
theorem IsPrefix.binary_eq
    {A B : FinitePartialCode db du dd} (h : A.IsPrefix B)
    (x y : Nat) (hx : x < A.size) (hy : y < A.size) (t : Fin db) :
    A.toAgeModel.binary x y t = B.toAgeModel.binary x y t := by
  obtain ⟨hSize,hCode⟩ := h
  have hxB := lt_of_lt_of_le hx hSize
  have hyB := lt_of_lt_of_le hy hSize
  have hAtom := congrArg (fun C : FinitePartialCode db du dd =>
    C.toAgeModel.binary x y t) hCode
  simpa [toAgeModel, restrict, hx, hy, hxB, hyB] using hAtom

theorem IsPrefix.unary_eq
    {A B : FinitePartialCode db du dd} (h : A.IsPrefix B)
    (x : Nat) (hx : x < A.size) (t : Fin du) :
    A.toAgeModel.unary x t = B.toAgeModel.unary x t := by
  obtain ⟨hSize,hCode⟩ := h
  have hxB := lt_of_lt_of_le hx hSize
  have hAtom := congrArg (fun C : FinitePartialCode db du dd =>
    C.toAgeModel.unary x t) hCode
  simpa [toAgeModel, restrict, hx, hxB] using hAtom

theorem IsPrefix.diagonal_eq
    {A B : FinitePartialCode db du dd} (h : A.IsPrefix B)
    (x : Nat) (hx : x < A.size) (t : Fin dd) :
    A.toAgeModel.diagonal x t = B.toAgeModel.diagonal x t := by
  obtain ⟨hSize,hCode⟩ := h
  have hxB := lt_of_lt_of_le hx hSize
  have hAtom := congrArg (fun C : FinitePartialCode db du dd =>
    C.toAgeModel.diagonal x t) hCode
  simpa [toAgeModel, restrict, hx, hxB] using hAtom

end FinitePartialCode

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- The canonical finite interpretation of a valid G+ vertex omits
every forbidden pattern, including forbidden singletons. -/
theorem finiteGPlus_code_avoids
    (C : FiniteGPlusVertex family)
    (bad : NormalizedForbidden db du dd) (hMem : bad ∈ family) :
    bad.Avoids C.val.toAgeModel := by
  obtain ⟨A,hCode,_hPos,hAvoid⟩ := C.property
  rw [hCode]
  cases bad with
  | singleton F hNeutral =>
      rintro ⟨f,hf⟩
      exact hAvoid (.singleton F hNeutral) hMem
        ⟨f, FinitePartialCode.realizes_ofEnumerated A F f hf⟩
  | nontrivial r F hr hIrred =>
      rintro ⟨f,hf⟩
      exact hAvoid (.nontrivial r F hr hIrred) hMem
        ⟨f, FinitePartialCode.realizes_ofEnumerated A F f hf⟩

/-- A size-nondecreasing irreducible candidate automatically has
strictly increasing sizes; no global strict-size enumeration is assumed. -/
theorem finiteGPlus_irreducible_copy_strictMono_size
    {r : Nat} (F : ForbiddenAtomicPattern r db du dd)
    (hIrred : F.Irreducible) (f : Fin r → FiniteGPlusVertex family)
    (hSize : Monotone (fun a : Fin r => (f a).val.size))
    (hBinary : ∀ a b : Fin r, a ≠ b → ∀ t : Fin db,
      finiteGPlusBinary (f a) (f b) t = F.binary a b t) :
    StrictMono (fun a : Fin r => (f a).val.size) := by
  intro a b hab
  obtain hAB | hBA := finiteGPlus_irreducible_copy_pairwise_comparable
    F hIrred f hBinary a b (ne_of_lt hab)
  · exact hAB.2
  · have hLe := hSize (le_of_lt hab)
    have hLt := hBA.2
    omega

/-- Forward atoms on a comparable pair are read unchanged in any
common larger code. In particular false atoms are preserved. -/
theorem finiteGPlus_binary_in_top_forward
    (A B C : FiniteGPlusVertex family)
    (hAB : A.IsProperPrefix B) (hBC : B.val.IsPrefix C.val) (t : Fin db) :
    C.val.toAgeModel.binary (A.val.size-1) (B.val.size-1) t =
      finiteGPlusBinary A B t := by
  have hA := finiteGPlusVertex_size_pos A
  have hB := finiteGPlusVertex_size_pos B
  have hLt := hAB.2
  have hx : A.val.size-1 < B.val.size := by omega
  have hy : B.val.size-1 < B.val.size := by omega
  have hRead :
      B.val.toAgeModel.binary (A.val.size-1) (B.val.size-1) t =
        B.val.binary (A.lowerLastIn B hAB) B.last t := by
    simp [FinitePartialCode.toAgeModel, FiniteGPlusVertex.lowerLastIn,
      FiniteGPlusVertex.last, hx, hy]
  exact (hBC.binary_eq _ _ hx hy t).symm.trans
    (hRead.trans (finiteGPlusBinary_forward A B t hAB).symm)

/-- Reverse atoms use the same larger code, with coordinates reversed. -/
theorem finiteGPlus_binary_in_top_reverse
    (A B C : FiniteGPlusVertex family)
    (hAB : A.IsProperPrefix B) (hBC : B.val.IsPrefix C.val) (t : Fin db) :
    C.val.toAgeModel.binary (B.val.size-1) (A.val.size-1) t =
      finiteGPlusBinary B A t := by
  have hB := finiteGPlusVertex_size_pos B
  have hLt := hAB.2
  have hx : A.val.size-1 < B.val.size := by omega
  have hy : B.val.size-1 < B.val.size := by omega
  have hRead :
      B.val.toAgeModel.binary (B.val.size-1) (A.val.size-1) t =
        B.val.binary B.last (A.lowerLastIn B hAB) t := by
    simp [FinitePartialCode.toAgeModel, FiniteGPlusVertex.lowerLastIn,
      FiniteGPlusVertex.last, hx, hy]
  exact (hBC.binary_eq _ _ hy hx t).symm.trans
    (hRead.trans (finiteGPlusBinary_reverse A B t hAB).symm)

theorem finiteGPlus_unary_in_top
    (A C : FiniteGPlusVertex family)
    (hAC : A.val.IsPrefix C.val) (t : Fin du) :
    C.val.toAgeModel.unary (A.val.size-1) t = finiteGPlusUnary A t := by
  have hPos := finiteGPlusVertex_size_pos A
  have hx : A.val.size-1 < A.val.size := by omega
  have hRead : A.val.toAgeModel.unary (A.val.size-1) t =
      finiteGPlusUnary A t := by
    simp [FinitePartialCode.toAgeModel, finiteGPlusUnary,
      FiniteGPlusVertex.last, hx]
  exact (hAC.unary_eq _ hx t).symm.trans hRead

theorem finiteGPlus_diagonal_in_top
    (A C : FiniteGPlusVertex family)
    (hAC : A.val.IsPrefix C.val) (t : Fin dd) :
    C.val.toAgeModel.diagonal (A.val.size-1) t =
      finiteGPlusDiagonal A t := by
  have hPos := finiteGPlusVertex_size_pos A
  have hx : A.val.size-1 < A.val.size := by omega
  have hRead : A.val.toAgeModel.diagonal (A.val.size-1) t =
      finiteGPlusDiagonal A t := by
    simp [FinitePartialCode.toAgeModel, finiteGPlusDiagonal,
      FiniteGPlusVertex.last, hx]
  exact (hAC.diagonal_eq _ hx t).symm.trans hRead

/-- Full induced transport, with the explicit coordinate map
A+ ↦ |A+|-1 into the candidate's largest finite partial structure. -/
theorem finiteGPlus_irreducible_copy_realizes_top
    {r : Nat} (F : ForbiddenAtomicPattern r db du dd)
    (hr : 0 < r) (hIrred : F.Irreducible)
    (f : Fin r → FiniteGPlusVertex family)
    (hSize : Monotone (fun a : Fin r => (f a).val.size))
    (hBinary : ∀ a b : Fin r, a ≠ b → ∀ t : Fin db,
      finiteGPlusBinary (f a) (f b) t = F.binary a b t)
    (hUnary : ∀ a : Fin r, ∀ t : Fin du,
      finiteGPlusUnary (f a) t = F.unary a t)
    (hDiagonal : ∀ a : Fin r, ∀ t : Fin dd,
      finiteGPlusDiagonal (f a) t = F.diagonal a t) :
    (f (⟨r-1,by omega⟩ : Fin r)).val.toAgeModel.Realizes F
      (fun a => (f a).val.size-1) := by
  let last : Fin r := ⟨r-1,by omega⟩
  let C := f last
  have hStrict := finiteGPlus_irreducible_copy_strictMono_size
    F hIrred f hSize hBinary
  have hBelow : ∀ a, (f a).val.IsPrefix C.val :=
    finiteGPlus_irreducible_copy_prefix_top F hIrred f hr hStrict hBinary
  have hChain := finiteGPlus_irreducible_copy_prefix_mono
    F hIrred f hStrict hBinary
  have hOrder : StrictMono (fun a : Fin r => (f a).val.size-1) := by
    intro a b hab
    have hPos := finiteGPlusVertex_size_pos (f a)
    have hLt := hStrict hab
    omega
  have hCarrier : ∀ a, (f a).val.size-1 ∈ C.val.toAgeModel.carrier := by
    intro a
    obtain ⟨hLe,_⟩ := hBelow a
    have hPos := finiteGPlusVertex_size_pos (f a)
    change (f a).val.size-1 < C.val.size
    omega
  refine ⟨hOrder, hCarrier, ?_, ?_, ?_⟩
  · intro a b hab t
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact (finiteGPlus_binary_in_top_forward
        (f a) (f b) C (hChain a b hlt) (hBelow b) t).trans
        (hBinary a b hab t)
    · exact (finiteGPlus_binary_in_top_reverse
        (f b) (f a) C (hChain b a hgt) (hBelow a) t).trans
        (hBinary a b hab t)
  · intro a t
    exact (finiteGPlus_unary_in_top (f a) C (hBelow a) t).trans (hUnary a t)
  · intro a t
    exact (finiteGPlus_diagonal_in_top (f a) C (hBelow a) t).trans
      (hDiagonal a t)

/-- Lemma 6.41's forbidden-age contradiction for every nontrivial
normalized forbidden pattern in a size-nondecreasing enumeration. -/
theorem finiteGPlus_excludes_nontrivial
    {r : Nat} (F : ForbiddenAtomicPattern r db du dd)
    (hr : 1 < r) (hIrred : F.Irreducible)
    (hMem : NormalizedForbidden.nontrivial r F hr hIrred ∈ family)
    (f : Fin r → FiniteGPlusVertex family)
    (hSize : Monotone (fun a : Fin r => (f a).val.size))
    (hBinary : ∀ a b : Fin r, a ≠ b → ∀ t : Fin db,
      finiteGPlusBinary (f a) (f b) t = F.binary a b t)
    (hUnary : ∀ a : Fin r, ∀ t : Fin du,
      finiteGPlusUnary (f a) t = F.unary a t)
    (hDiagonal : ∀ a : Fin r, ∀ t : Fin dd,
      finiteGPlusDiagonal (f a) t = F.diagonal a t) : False := by
  have hPositive : 0 < r := by omega
  have hCopy := finiteGPlus_irreducible_copy_realizes_top
    F hPositive hIrred f hSize hBinary hUnary hDiagonal
  exact finiteGPlus_code_avoids (f (⟨r-1,by omega⟩ : Fin r))
    (.nontrivial r F hr hIrred) hMem ⟨_,hCopy⟩

/-- Forbidden singleton types cannot appear either. No pair or
size-order premise is needed in this case. -/
theorem finiteGPlus_excludes_singleton
    (F : ForbiddenAtomicPattern 1 db du dd)
    (hNeutral : F.NonNeutralSingleton)
    (hMem : NormalizedForbidden.singleton F hNeutral ∈ family)
    (A : FiniteGPlusVertex family)
    (hUnary : ∀ t : Fin du, finiteGPlusUnary A t = F.unary 0 t)
    (hDiagonal : ∀ t : Fin dd, finiteGPlusDiagonal A t = F.diagonal 0 t) :
    False := by
  have hPos := finiteGPlusVertex_size_pos A
  have hCopy : A.val.toAgeModel.Realizes F (fun _ => A.val.size-1) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      have heq : a = b := Subsingleton.elim _ _
      exact (ne_of_lt hab heq).elim
    · intro a
      change A.val.size-1 < A.val.size
      omega
    · intro a b hab t
      exact (hab (Subsingleton.elim _ _)).elim
    · intro a t
      have ha : a = 0 := Subsingleton.elim _ _
      subst a
      exact (finiteGPlus_unary_in_top A A
        (FinitePartialCode.isPrefix_refl _) t).trans (hUnary t)
    · intro a t
      have ha : a = 0 := Subsingleton.elim _ _
      subst a
      exact (finiteGPlus_diagonal_in_top A A
        (FinitePartialCode.isPrefix_refl _) t).trans (hDiagonal t)
  exact finiteGPlus_code_avoids A (.singleton F hNeutral) hMem ⟨_,hCopy⟩

end SuccessorTree.V10

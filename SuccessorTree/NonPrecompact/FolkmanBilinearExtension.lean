import SuccessorTree.NonPrecompact.BananaAmalgam

/-!
# Bilinear extension layer for the Folkman--BANANA amalgam

After the Boolean-ring atom amalgam is constructed, the spans of the two
source images meet exactly in the common source.  On that span the bilinear
map is the usual BANANA zero-cross block amalgam.  The ambient Boolean-ring
vector spaces may contain further coordinates; the circulation proof extends
the pairing to them by choosing complements and putting zero on all new
blocks.

This file packages that standard-coordinate construction.
-/

namespace SuccessorTree.NonPrecompact

/-- Adjoin extra left/right coordinates to a pairing matrix and put zero on
every block involving one of the new coordinates. -/
def matrixExtendZero
    {I J XL XR : Type*}
    (M : Matrix I J F2) :
    Matrix (Sum I XL) (Sum J XR) F2
  | .inl i, .inl j => M i j
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0
  | .inr _, .inr _ => 0

/-- Restricting the zero extension to the old coordinates recovers the old
pairing matrix. -/
theorem matrixExtendZero_old
    {I J XL XR : Type*}
    (M : Matrix I J F2) :
    (matrixExtendZero (XL := XL) (XR := XR) M).submatrix
      (Sum.inl : I → Sum I XL)
      (Sum.inl : J → Sum J XR) = M := by
  ext i j
  rfl

/-- The extra left coordinates pair trivially with everything. -/
theorem matrixExtendZero_extra_left
    {I J XL XR : Type*}
    (M : Matrix I J F2)
    (x : XL) (j : Sum J XR) :
    matrixExtendZero M (Sum.inr x) j = 0 := by
  cases j <;> rfl

/-- The extra right coordinates pair trivially with everything. -/
theorem matrixExtendZero_extra_right
    {I J XL XR : Type*}
    (M : Matrix I J F2)
    (i : Sum I XL) (y : XR) :
    matrixExtendZero M i (Sum.inr y) = 0 := by
  cases i <;> rfl

/-- Standard-coordinate bilinear map used after the Folkman atom-ring
amalgam.  First perform the BANANA block amalgam on the span of the two old
images, then adjoin any remaining ambient coordinates with zero pairing. -/
def folkmanBilinearAmalgam
    {LA RA UB VB UC VC XL XR : Type*}
    (B : Matrix (Sum LA UB) (Sum RA VB) F2)
    (C : Matrix (Sum LA UC) (Sum RA VC) F2) :
    Matrix
      (Sum (Sum LA (Sum UB UC)) XL)
      (Sum (Sum RA (Sum VB VC)) XR)
      F2 :=
  matrixExtendZero (bananaBlockAmalgam B C)

/-- Coordinate embedding of the B-side left or right vector space into the
ambient Folkman amalgam coordinate space. -/
def folkmanAmalgamIndexLeft
    {A X Y Z : Type*} :
    Sum A X → Sum (Sum A (Sum X Y)) Z :=
  fun i => Sum.inl (sumAmalgamIndexLeft i)

/-- Coordinate embedding of the C-side left or right vector space. -/
def folkmanAmalgamIndexRight
    {A X Y Z : Type*} :
    Sum A Y → Sum (Sum A (Sum X Y)) Z :=
  fun i => Sum.inl (sumAmalgamIndexRight i)

/-- The Folkman ambient pairing restricts to the old B-pairing. -/
theorem folkmanBilinearAmalgam_left
    {LA RA UB VB UC VC XL XR : Type*}
    (B : Matrix (Sum LA UB) (Sum RA VB) F2)
    (C : Matrix (Sum LA UC) (Sum RA VC) F2) :
    (folkmanBilinearAmalgam (XL := XL) (XR := XR) B C).submatrix
      (folkmanAmalgamIndexLeft :
        Sum LA UB → Sum (Sum LA (Sum UB UC)) XL)
      (folkmanAmalgamIndexLeft :
        Sum RA VB → Sum (Sum RA (Sum VB VC)) XR) = B := by
  ext i j
  cases i <;> cases j <;> rfl

/-- The Folkman ambient pairing restricts to the old C-pairing, provided the
two source pairings agree on the common base block. -/
theorem folkmanBilinearAmalgam_right
    {LA RA UB VB UC VC XL XR : Type*}
    (B : Matrix (Sum LA UB) (Sum RA VB) F2)
    (C : Matrix (Sum LA UC) (Sum RA VC) F2)
    (hcommon :
      ∀ a r,
        B (.inl a) (.inl r) =
          C (.inl a) (.inl r)) :
    (folkmanBilinearAmalgam (XL := XL) (XR := XR) B C).submatrix
      (folkmanAmalgamIndexRight :
        Sum LA UC → Sum (Sum LA (Sum UB UC)) XL)
      (folkmanAmalgamIndexRight :
        Sum RA VC → Sum (Sum RA (Sum VB VC)) XR) = C := by
  ext i j
  cases i with
  | inl a =>
      cases j with
      | inl r =>
          exact hcommon a r
      | inr v =>
          rfl
  | inr u =>
      cases j <;> rfl

/-- Extend the B-side coordinate map by zero through both the C-complement
and the final ambient complement. -/
def folkmanAmalgamLinearLeft
    {A X Y Z : Type*} :
    (Sum A X → F2) →ₗ[F2]
      (Sum (Sum A (Sum X Y)) Z → F2) :=
  (sumCommonLinear :
      (Sum A (Sum X Y) → F2) →ₗ[F2]
        (Sum (Sum A (Sum X Y)) Z → F2)).comp
    (sumAmalgamLinearLeft :
      (Sum A X → F2) →ₗ[F2]
        (Sum A (Sum X Y) → F2))

/-- Extend the C-side coordinate map by zero through both the B-complement
and the final ambient complement. -/
def folkmanAmalgamLinearRight
    {A X Y Z : Type*} :
    (Sum A Y → F2) →ₗ[F2]
      (Sum (Sum A (Sum X Y)) Z → F2) :=
  (sumCommonLinear :
      (Sum A (Sum X Y) → F2) →ₗ[F2]
        (Sum (Sum A (Sum X Y)) Z → F2)).comp
    (sumAmalgamLinearRight :
      (Sum A Y → F2) →ₗ[F2]
        (Sum A (Sum X Y) → F2))

/-- Adding a final zero-pairing ambient complement does not create any new
intersection between the two old vector-space images. -/
theorem folkmanAmalgamLinear_eq_iff_common
    {A X Y Z : Type*}
    (v : Sum A X → F2)
    (w : Sum A Y → F2) :
    folkmanAmalgamLinearLeft (Y := Y) (Z := Z) v =
      folkmanAmalgamLinearRight (X := X) (Z := Z) w ↔
      ∃ a : A → F2,
        v = sumCommonLinear a ∧
        w = sumCommonLinear a := by
  constructor
  · intro h
    have hinner :
        sumAmalgamLinearLeft v =
          (sumAmalgamLinearRight w :
            Sum A (Sum X Y) → F2) := by
      funext i
      have hi := congrFun h (Sum.inl i)
      simpa [folkmanAmalgamLinearLeft, folkmanAmalgamLinearRight,
        sumCommonLinear] using hi
    exact (sumAmalgam_eq_iff_common v w).1 hinner
  · rintro ⟨a, rfl, rfl⟩
    funext i
    cases i with
    | inl z =>
        cases z with
        | inl a => rfl
        | inr xy =>
            cases xy <;> rfl
    | inr _ =>
        rfl

end SuccessorTree.NonPrecompact

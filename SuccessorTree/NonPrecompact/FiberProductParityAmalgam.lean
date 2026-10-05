import SuccessorTree.NonPrecompact.ParityStarMatrix
import SuccessorTree.NonPrecompact.FiberProductStrong

/-!
# Parity amalgamation on fibre-product atom grids

This file packages the finite atom-grid construction behind strong
amalgamation for pre-BANANA.

For surjections f : B → A and g : C → A, the amalgam atoms are triples
(a,b,c) with f(b)=a=g(c).  On each fibre rectangle we put the explicit
star matrix with the prescribed B-row and C-column F₂ marks.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- Left fibre over one base atom. -/
abbrev LeftFiber
    {A B : Type*} (f : B → A) (a : A) :=
  {b : B // f b = a}

/-- Right fibre over one base atom. -/
abbrev RightFiber
    {A C : Type*} (g : C → A) (a : A) :=
  {c : C // g c = a}

/-- Atom grid of the fibre-product amalgam, indexed by the common base atom. -/
abbrev FiberGrid
    {A B C : Type*} (f : B → A) (g : C → A) :=
  Σ a : A, LeftFiber f a × RightFiber g a

/-- A chosen row in every nonempty left fibre. -/
noncomputable def leftFiberBase
    {A B : Type*}
    (f : B → A) (hf : Function.Surjective f) (a : A) :
    LeftFiber f a :=
  ⟨Classical.choose (hf a), Classical.choose_spec (hf a)⟩

/-- A chosen column in every nonempty right fibre. -/
noncomputable def rightFiberBase
    {A C : Type*}
    (g : C → A) (hg : Function.Surjective g) (a : A) :
    RightFiber g a :=
  ⟨Classical.choose (hg a), Classical.choose_spec (hg a)⟩

/-- Marking on the fibre-product atom grid obtained by putting the explicit
star matrix on each source-atom rectangle. -/
noncomputable def fiberGridMark
    {A B C : Type*}
    [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (f : B → A) (g : C → A)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (markB : B → F2) (markC : C → F2)
    (p : FiberGrid f g) : F2 :=
  parityStarMatrix
    (fun b : LeftFiber f p.1 => markB b.1)
    (fun c : RightFiber g p.1 => markC c.1)
    (leftFiberBase f hf p.1)
    (rightFiberBase g hg p.1)
    p.2.1 p.2.2

/-- Every B-atom row of the fibre-product grid has the prescribed B mark. -/
theorem sum_fiberGridMark_right
    {A B C : Type*}
    [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (f : B → A) (g : C → A)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (markB : B → F2) (markC : C → F2)
    (b : B) :
    (∑ c : RightFiber g (f b),
      fiberGridMark f g hf hg markB markC
        ⟨f b, (⟨b, rfl⟩, c)⟩) =
      markB b := by
  simpa [fiberGridMark] using
    sum_row_parityStarMatrix
      (fun b' : LeftFiber f (f b) => markB b'.1)
      (fun c' : RightFiber g (f b) => markC c'.1)
      (leftFiberBase f hf (f b))
      (rightFiberBase g hg (f b))
      (⟨b, rfl⟩ : LeftFiber f (f b))

/-- If the B- and C-fibre totals agree over every base atom, then every
C-atom column of the fibre-product grid has the prescribed C mark. -/
theorem sum_fiberGridMark_left
    {A B C : Type*}
    [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (f : B → A) (g : C → A)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (markB : B → F2) (markC : C → F2)
    (htotal :
      ∀ a : A,
        (∑ b : LeftFiber f a, markB b.1) =
          ∑ c : RightFiber g a, markC c.1)
    (c : C) :
    (∑ b : LeftFiber f (g c),
      fiberGridMark f g hf hg markB markC
        ⟨g c, (b, ⟨c, rfl⟩)⟩) =
      markC c := by
  simpa [fiberGridMark] using
    sum_col_parityStarMatrix
      (fun b' : LeftFiber f (g c) => markB b'.1)
      (fun c' : RightFiber g (g c) => markC c'.1)
      (leftFiberBase f hf (g c))
      (rightFiberBase g hg (g c))
      (htotal (g c))
      (⟨c, rfl⟩ : RightFiber g (g c))

/-- Forgetting the explicit base coordinate identifies the sigma-type atom
grid with the usual compatible-pair fibre product. -/
noncomputable def fiberGridEquivCompatiblePair
    {A B C : Type*}
    (f : B → A) (g : C → A) :
    FiberGrid f g ≃ CompatiblePair f g where
  toFun p :=
    ⟨(p.2.1.1, p.2.2.1),
      p.2.1.2.trans p.2.2.2.symm⟩
  invFun p :=
    ⟨f p.1.1,
      (⟨p.1.1, rfl⟩,
        ⟨p.1.2, p.2.symm⟩)⟩
  left_inv p := by
    rcases p with ⟨a, ⟨b, c⟩⟩
    rcases b with ⟨b, hb⟩
    rcases c with ⟨c, hc⟩
    subst a
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> rfl

/-- Strong intersection for the sigma-type atom grid.  If membership pulled
back from B agrees with membership pulled back from C on every grid atom,
then both subsets come from one common subset of A. -/
theorem exists_common_subset_of_fiberGrid
    {A B C : Type*}
    (f : B → A) (g : C → A)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (SB : Set B) (SC : Set C)
    (hcompat :
      ∀ p : FiberGrid f g,
        p.2.1.1 ∈ SB ↔ p.2.2.1 ∈ SC) :
    ∃ SA : Set A,
      (∀ b, b ∈ SB ↔ f b ∈ SA) ∧
      (∀ c, c ∈ SC ↔ g c ∈ SA) := by
  apply exists_common_subset_of_fiberProduct
    f g hf hg SB SC
  intro p
  let q := (fiberGridEquivCompatiblePair f g).symm p
  simpa [q, fiberGridEquivCompatiblePair] using hcompat q

end SuccessorTree.NonPrecompact

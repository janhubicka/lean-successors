import SuccessorTree.HalesJewett.AlphabetLift
import SuccessorTree.HalesJewett.AlphabetEquiv
import SuccessorTree.HalesJewett.LineSchedule
import SuccessorTree.HalesJewett.ForcingProposition
import SuccessorTree.HalesJewett.ForcingLemmaTwo
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic

/-!
# Closing the combinatorial-forcing proof of Hales--Jewett

The induction hypothesis is the starred theorem for every finite colour type.
Proposition 1 upgrades it to the omega-dimensional theorem on the old
alphabet. We then add one distinguished new letter and use finitely many
nested homogeneous subspaces plus the pigeonhole principle.
-/

namespace SuccessorTree
namespace HalesJewett

/-- Starred Hales--Jewett for every finite colour type in the same universe. -/
def AllStarHJ (α : Type u) [Fintype α] : Prop :=
  ∀ (κ : Type u) [Fintype κ], StarHJ α κ

/-- The full finite-colour omega-dimensional theorem obtained from the
one-dimensional theorem through the forcing argument. -/
theorem omegaRamsey_of_allStarHJ
    [Fintype α]
    (hall : AllStarHJ α)
    [Fintype κ]
    (colour : List α → κ) :
    ∃ W : Subspace α, (subspaceAction α).Homogeneous colour W := by
  classical
  let force : LargeSetTheorem α :=
    largeSetTheorem_of_schedule
      (α := α)
      (fun n => hall (ExactWord α n → Bool))
      (finiteLineSchedule (α := α))
  exact finiteRamsey_of_largeSetTheorem force colour

/-- The homogeneous old-alphabet subspace chosen after a finite prefix of
earlier stages. -/
noncomputable def alphabetStepWord
    [Fintype α] [Fintype κ]
    (hall : AllStarHJ α)
    (colour : List (Option α) → κ)
    (Ws : List (Subspace α)) : Subspace α :=
  Classical.choose <|
    omegaRamsey_of_allStarHJ hall
      (fun v => colour (prefixApply Ws (optionWord v)))

theorem alphabetStepWord_homogeneous
    [Fintype α] [Fintype κ]
    (hall : AllStarHJ α)
    (colour : List (Option α) → κ)
    (Ws : List (Subspace α)) :
    ∀ x y : List α,
      colour (prefixApply Ws
        (optionWord ((alphabetStepWord hall colour Ws).eval x))) =
      colour (prefixApply Ws
        (optionWord ((alphabetStepWord hall colour Ws).eval y))) := by
  exact Classical.choose_spec <|
    omegaRamsey_of_allStarHJ hall
      (fun v => colour (prefixApply Ws (optionWord v)))

/-- The colour recorded at a stage. -/
noncomputable def alphabetStageColour
    [Fintype α] [Fintype κ]
    (hall : AllStarHJ α)
    (colour : List (Option α) → κ)
    (Ws : List (Subspace α)) : κ :=
  colour (prefixApply Ws
    (optionWord ((alphabetStepWord hall colour Ws).eval [])))

theorem alphabetStepWord_colour
    [Fintype α] [Fintype κ]
    (hall : AllStarHJ α)
    (colour : List (Option α) → κ)
    (Ws : List (Subspace α))
    (v : List α) :
    colour (prefixApply Ws
      (optionWord ((alphabetStepWord hall colour Ws).eval v))) =
      alphabetStageColour hall colour Ws := by
  exact alphabetStepWord_homogeneous hall colour Ws v []

/-- The recursively chosen list W_0,...,W_{n-1}. -/
noncomputable def alphabetWords
    [Fintype α] [Fintype κ]
    (hall : AllStarHJ α)
    (colour : List (Option α) → κ) :
    Nat → List (Subspace α)
  | 0 => []
  | n + 1 =>
      let Ws := alphabetWords hall colour n
      Ws ++ [alphabetStepWord hall colour Ws]

@[simp] theorem alphabetWords_zero
    [Fintype α] [Fintype κ]
    (hall : AllStarHJ α)
    (colour : List (Option α) → κ) :
    alphabetWords hall colour 0 = [] := rfl

theorem alphabetWords_succ
    [Fintype α] [Fintype κ]
    (hall : AllStarHJ α)
    (colour : List (Option α) → κ)
    (n : Nat) :
    alphabetWords hall colour (n + 1) =
      alphabetWords hall colour n ++
        [alphabetStepWord hall colour (alphabetWords hall colour n)] := rfl

@[simp] theorem alphabetWords_length
    [Fintype α] [Fintype κ]
    (hall : AllStarHJ α)
    (colour : List (Option α) → κ) :
    ∀ n : Nat, (alphabetWords hall colour n).length = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [alphabetWords_succ]
      simp [ih]

theorem alphabetWords_prefix_succ
    [Fintype α] [Fintype κ]
    (hall : AllStarHJ α)
    (colour : List (Option α) → κ)
    (n : Nat) :
    alphabetWords hall colour n <+:
      alphabetWords hall colour (n + 1) := by
  rw [alphabetWords_succ]
  exact (alphabetWords hall colour n).prefix_append _

theorem alphabetWords_prefix
    [Fintype α] [Fintype κ]
    (hall : AllStarHJ α)
    (colour : List (Option α) → κ)
    {m n : Nat} (h : m ≤ n) :
    alphabetWords hall colour m <+:
      alphabetWords hall colour n := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact ⟨[], rfl⟩
  | succ n ih =>
      by_cases hm : m = n + 1
      · subst m
        exact ⟨[], by simp⟩
      · have hmn : m ≤ n := by omega
        exact (ih hmn).trans (alphabetWords_prefix_succ hall colour n)

/-- Decomposition of a later stage list immediately after stage p. -/
theorem alphabetWords_decompose
    [Fintype α] [Fintype κ]
    (hall : AllStarHJ α)
    (colour : List (Option α) → κ)
    {p R : Nat} (h : p < R) :
    ∃ Cs : List (Subspace α),
      alphabetWords hall colour R =
        alphabetWords hall colour p ++
          alphabetStepWord hall colour (alphabetWords hall colour p) :: Cs := by
  have hpref :=
    alphabetWords_prefix hall colour (Nat.succ_le_of_lt h)
  rcases hpref with ⟨Cs, hCs⟩
  refine ⟨Cs, ?_⟩
  rw [alphabetWords_succ] at hCs
  simpa [List.append_assoc] using hCs.symm

/-- The simple one-variable input pattern: p copies of the new letter, then
d copies of the parameter. -/
def repetitionLine (p d : Nat) (hd : 0 < d) :
    StarLine (Option α) where
  word :=
    constants (List.replicate p (none : Option α)) ++
      List.replicate d LineSymbol.parameter
  hasParameter := by
    simp [hd]

@[simp] theorem repetitionLine_star
    (p d : Nat) (hd : 0 < d) :
    (repetitionLine (α := α) p d hd).star =
      List.replicate p (none : Option α) := by
  cases d with
  | zero => omega
  | succ d =>
      simp [repetitionLine, List.replicate_succ]

@[simp] theorem repetitionLine_eval
    (p d : Nat) (hd : 0 < d) (x : Option α) :
    (repetitionLine (α := α) p d hd).eval x =
      List.replicate p (none : Option α) ++ List.replicate d x := by
  cases d with
  | zero => omega
  | succ d =>
      simp [repetitionLine, StarLine.eval, evalWord,
        List.replicate_succ, List.map_replicate]

/-- Image of a one-variable line under a subspace. -/
def subspaceImageLine
    (U : Subspace α) (L : StarLine α) : StarLine α :=
  (U.compose (linePrefixSubspace L)).firstLine

@[simp] theorem subspaceImageLine_star
    (U : Subspace α) (L : StarLine α) :
    (subspaceImageLine U L).star = U.eval L.star := by
  change (U.compose (linePrefixSubspace L)).head = U.eval L.star
  rfl

@[simp] theorem subspaceImageLine_eval
    (U : Subspace α) (L : StarLine α) (a : α) :
    (subspaceImageLine U L).eval a = U.eval (L.eval a) := by
  rw [subspaceImageLine, Subspace.firstLine_eval, Subspace.compose_eval]
  simp

/-- The induction step: if starred Hales--Jewett holds for every finite
colouring of α, then it holds for every finite colouring of Option α. -/
theorem allStarHJ_option
    [Fintype α]
    (hall : AllStarHJ α) :
    AllStarHJ (Option α) := by
  classical
  intro κ _instκ
  intro colour

  let R : Nat := Fintype.card κ + 1
  let Ws : List (Subspace α) := alphabetWords hall colour R
  let U : Subspace (Option α) := nestedSubspace Ws
  let gamma : Nat → κ := fun n =>
    alphabetStageColour hall colour (alphabetWords hall colour n)

  have finish :
      ∀ p q : Nat, p < q → q < R → gamma p = gamma q →
        ∃ K : StarLine (Option α),
          StarMonochromatic colour K := by
    intro p q hpq hqR hpqColour
    have hpR : p < R := lt_trans hpq hqR
    obtain ⟨Cp, hpdec⟩ :=
      alphabetWords_decompose hall colour hpR
    obtain ⟨Cq, hqdec⟩ :=
      alphabetWords_decompose hall colour hqR

    let Wp : Subspace α :=
      alphabetStepWord hall colour (alphabetWords hall colour p)
    let Wq : Subspace α :=
      alphabetStepWord hall colour (alphabetWords hall colour q)
    let d : Nat := q - p
    have hd : 0 < d := by
      dsimp [d]
      omega
    let B : StarLine (Option α) := repetitionLine p d hd
    let K : StarLine (Option α) := subspaceImageLine U B

    have hstageNone :
        ∀ r : Nat, r < R →
          colour (U.eval (List.replicate r (none : Option α))) =
            gamma r := by
      intro r hr
      obtain ⟨Cr, hrdec⟩ :=
        alphabetWords_decompose hall colour hr
      let Wr : Subspace α :=
        alphabetStepWord hall colour (alphabetWords hall colour r)
      have hlen :
          (alphabetWords hall colour r).length = r :=
        alphabetWords_length hall colour r
      change
        colour ((nestedSubspace Ws).eval
          (List.replicate r (none : Option α))) =
          alphabetStageColour hall colour (alphabetWords hall colour r)
      rw [show Ws =
          alphabetWords hall colour r ++ Wr :: Cr by
            simpa [Ws, Wr] using hrdec]
      rw [← hlen]
      have hsplit :=
        nestedSubspace_eval_none_prefix
          (alphabetWords hall colour r) (Wr :: Cr) []
      simp only [List.append_nil] at hsplit
      rw [hsplit, nestedSubspace_cons_eval_nil]
      exact alphabetStepWord_colour hall colour
        (alphabetWords hall colour r) []

    have hstar :
        colour K.star = gamma p := by
      rw [show K = subspaceImageLine U B by rfl,
        subspaceImageLine_star]
      rw [show B.star = List.replicate p (none : Option α) by
        exact repetitionLine_star p d hd]
      exact hstageNone p hpR

    refine ⟨K, ?_⟩
    intro x
    cases x with
    | none =>
        rw [show K = subspaceImageLine U B by rfl,
          subspaceImageLine_eval]
        rw [show B.eval (none : Option α) =
            List.replicate p (none : Option α) ++
              List.replicate d none by
          exact repetitionLine_eval p d hd none]
        have hpqd : p + d = q := by
          dsimp [d]
          omega
        have hrep :
            List.replicate p (none : Option α) ++
                List.replicate d none =
              List.replicate q none := by
          rw [← List.replicate_add, hpqd]
        rw [hrep]
        exact (hstageNone q hqR).trans (hpqColour.trans hstar.symm)
    | some a =>
        rw [show K = subspaceImageLine U B by rfl,
          subspaceImageLine_eval]
        rw [show B.eval (some a) =
            List.replicate p (none : Option α) ++
              List.replicate d (some a) by
          exact repetitionLine_eval p d hd (some a)]

        have hlen :
            (alphabetWords hall colour p).length = p :=
          alphabetWords_length hall colour p
        change
          colour ((nestedSubspace Ws).eval
            (List.replicate p (none : Option α) ++
              List.replicate d (some a))) =
            colour K.star
        rw [show Ws =
            alphabetWords hall colour p ++ Wp :: Cp by
              simpa [Ws, Wp] using hpdec]
        rw [← hlen]
        have hsplit :=
          nestedSubspace_eval_none_prefix
            (alphabetWords hall colour p) (Wp :: Cp)
            (List.replicate d (some a))
        rw [hsplit]

        have hdEq : d = (d - 1) + 1 := by omega
        have hrepOld :
            List.replicate d a =
              a :: List.replicate (d - 1) a := by
          rw [hdEq, List.replicate_succ]
        obtain ⟨t, ht⟩ :=
          nestedSubspace_cons_eval_optionWord
            Wp Cp a (List.replicate (d - 1) a)
        have ht' :
            (nestedSubspace (Wp :: Cp)).eval
                (List.replicate d (some a)) =
              optionWord (Wp.eval t) := by
          rw [show List.replicate d (some a) =
              optionWord (List.replicate d a) by
                simp [optionWord]]
          rw [hrepOld]
          exact ht
        rw [ht']
        have hpcolour :=
          alphabetStepWord_colour hall colour
            (alphabetWords hall colour p) t
        change
          colour (prefixApply (alphabetWords hall colour p)
            (optionWord (Wp.eval t))) = colour K.star
        exact hpcolour.trans hstar.symm

  obtain ⟨i, j, hij, hcolour⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun x : Fin (Fintype.card κ + 1) => gamma x)
      (by simp)
  have hvne : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  by_cases hijlt : i.val < j.val
  · exact finish i.val j.val hijlt j.isLt hcolour
  · have hjilt : j.val < i.val := by omega
    exact finish j.val i.val hjilt i.isLt hcolour.symm

/-- Property independent of a particular Fintype instance, convenient for
finite-type induction. -/
def FiniteStarHJ (α : Type u) : Prop :=
  ∀ hα : Fintype α, @AllStarHJ α hα

theorem finiteStarHJ_empty : FiniteStarHJ PEmpty := by
  intro hα
  intro κ hκ
  intro colour
  let L : StarLine PEmpty :=
    ⟨[LineSymbol.parameter], by simp⟩
  refine ⟨L, ?_⟩
  intro a
  exact PEmpty.elim a

theorem finiteStarHJ_equiv
    {α β : Type u}
    (e : α ≃ β)
    (h : FiniteStarHJ α) :
    FiniteStarHJ β := by
  intro hβ
  let hα : Fintype α := Fintype.ofEquiv β e.symm
  letI : Fintype α := hα
  letI : Fintype β := hβ
  intro κ hκ
  letI : Fintype κ := hκ
  exact starHJ_equiv e (h hα κ)

theorem finiteStarHJ_option
    {α : Type u} [Fintype α]
    (h : FiniteStarHJ α) :
    FiniteStarHJ (Option α) := by
  intro hOpt
  letI : Fintype (Option α) := hOpt
  exact allStarHJ_option (h inferInstance)

/-- Starred Hales--Jewett for every finite alphabet and every finite colour
type in the same universe. -/
theorem allStarHJ_finite
    (α : Type u) [Fintype α] :
    AllStarHJ α := by
  have hfinite : FiniteStarHJ α := by
    apply Finite.induction_empty_option
      (P := FiniteStarHJ)
    · intro γ δ e hγ
      exact finiteStarHJ_equiv e hγ
    · exact finiteStarHJ_empty
    · intro γ hγFintype hγ
      exact finiteStarHJ_option hγ
    · exact α
  exact hfinite inferInstance

/-- The fully discharged starred Hales--Jewett theorem. -/
theorem starHJ_finite
    [Fintype α] [Fintype κ] :
    StarHJ α κ :=
  allStarHJ_finite α κ

end HalesJewett
end SuccessorTree

import SuccessorTree.FatTree.A4Trace
import SuccessorTree.ShapeDirectLine
import Mathlib.Data.Fintype.Pi

/-!
# Finite successor-fan profiles for fat-tree A4

The manuscript's successor-fan set is raw finite successor data, not a family
of admissible M-maps. This file gives that object a concrete finite Lean type.
It is the alphabet from which the simultaneous trace-profile Hales--Jewett
argument will be built.

No A4 conclusion is assumed here.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- Raw successor-fan data for a finite one-block map q.

Below the source level the table is the identity. On the source level it
chooses one immediate successor of q(x). The target is bounded by one
level above the final image level of q; no admissibility or total M-map
extension is part of the structure. -/
structure RawSuccessorFan {c : Nat} (q : AM H c 1) where
  toFun :
    InitialNode T c →
      InitialNode T (q.rowEndLevel H + 1)
  eq_id_below :
    ∀ x : InitialNode T c,
      LevelTree.lev x.1 < c →
        (toFun x).1 = x.1
  top_covBy :
    ∀ x : InitialNode T c,
      LevelTree.lev x.1 = c →
        q.representative H x.1 ⋖ (toFun x).1

namespace RawSuccessorFan

/-- Raw successor fans are determined by the underlying finite table. -/
theorem ext {c : Nat} {q : AM H c 1}
    {e f : RawSuccessorFan H q}
    (h : e.toFun = f.toFun) :
    e = f := by
  cases e
  cases f
  cases h
  rfl

/-- The raw successor-fan type is finite. This uses only finiteness of the
two relevant initial tree segments; it does not use admissibility. -/
noncomputable instance finite {c : Nat} (q : AM H c 1) :
    Finite (RawSuccessorFan H q) := by
  classical
  letI src : Fintype (InitialNode T c) :=
    initialNodeFintype T c
  letI dst : Fintype (InitialNode T (q.rowEndLevel H + 1)) :=
    initialNodeFintype T (q.rowEndLevel H + 1)
  exact Finite.of_injective
    (fun e : RawSuccessorFan H q => e.toFun)
    (by
      intro e f hef
      exact ext H hef)

/-- A concrete finite enumeration can therefore be chosen whenever the
profile argument needs a Hales--Jewett alphabet or finite product. -/
noncomputable instance fintype {c : Nat} (q : AM H c 1) :
    Fintype (RawSuccessorFan H q) :=
  Fintype.ofFinite _

end RawSuccessorFan

/-- A finite profile over a finite family of traces: at each trace we either
record a raw successor fan or none. The latter is the manuscript's bottom
symbol recording failure to match that fan. -/
abbrev FanProfile {c : Nat}
    (C : Type*) [Fintype C]
    (trace : C → AM H c 1) :=
  ∀ i : C, Option (RawSuccessorFan H (trace i))

noncomputable instance fanProfileFintype
    {c : Nat} {C : Type*} [Fintype C]
    (trace : C → AM H c 1) :
    Fintype (FanProfile H C trace) := by
  classical
  letI fans :
      ∀ i : C, Fintype (RawSuccessorFan H (trace i)) :=
    fun i => RawSuccessorFan.fintype H (trace i)
  infer_instance

/-- The exact traces of one finite fat-tree prefix form a concrete
finite type, not merely a finite set. -/
noncomputable instance exactTraceFintype
    (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height) :
    Fintype (FiniteFatTree.ExactTrace H y n hn) :=
  Set.Finite.fintype
    (FiniteFatTree.exactTraces_finite H y n hn)

/-- The simultaneous raw successor-fan profile over every exact trace of a
finite prefix.  This is the finite product alphabet used by the manuscript's
all-trace stabilization step. -/
abbrev ExactFanProfile
    (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height) :=
  FanProfile H
    (FiniteFatTree.ExactTrace H y n hn)
    (fun q => q.1)

noncomputable instance exactFanProfileFintype
    (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height) :
    Fintype (ExactFanProfile H y n hn) := by
  letI :=
    exactTraceFintype H y n hn
  exact fanProfileFintype H (fun q : FiniteFatTree.ExactTrace H y n hn => q.1)

/-- Starred Hales--Jewett simultaneously homogenizes every coordinate
of a finite profile.  This is the pure finite combinatorial core of the
manuscript's good-pair argument. -/
theorem finiteProfileStarHJ
    {α : Type*} {C : Type*} {κ : Type*}
    [Fintype α] [Fintype C] [Fintype κ]
    (colour : List α → C → κ) :
    ∃ L : StarLine α,
      ∀ a : α, ∀ i : C,
        colour (L.eval a) i = colour L.star i := by
  classical
  letI : Fintype (C → κ) := Pi.fintype
  obtain ⟨L, hL⟩ :=
    HalesJewett.starHJ_finite
      (α := α) (κ := C → κ) colour
  refine ⟨L, ?_⟩
  intro a i
  exact congrFun (hL a) i

/-- In particular, a word-colouring by the complete exact-trace fan profile
has a line on which the entire profile is constant. -/
theorem exactFanProfileStarHJ
    {α : Type*} [Fintype α]
    (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height)
    (colour : List α → ExactFanProfile H y n hn) :
    ∃ L : StarLine α,
      ∀ a : α,
        colour (L.eval a) = colour L.star := by
  classical
  letI := exactTraceFintype H y n hn
  letI := exactFanProfileFintype H y n hn
  exact HalesJewett.starHJ_finite
    (α := α)
    (κ := ExactFanProfile H y n hn)
    colour

/-- An exact finite-prefix trace is an exact one-moving word from
its source cut to the terminal cut of the prefix. -/
def exactTraceToAMExact
    (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height)
    (q : FiniteFatTree.ExactTrace H y n hn) :
    AMExact H
      (FiniteFatTree.traceSourceCut H y n hn)
      (FiniteFatTree.traceTargetCut H y) :=
  ⟨q.1, q.rowEndLevel H⟩

theorem exactTraceToAMExact_injective
    (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height) :
    Function.Injective (exactTraceToAMExact H y n hn) := by
  intro q r hqr
  apply Subtype.ext
  change q.1 = r.1
  exact congrArg
    (fun z : AMExact H
      (FiniteFatTree.traceSourceCut H y n hn)
      (FiniteFatTree.traceTargetCut H y) => z.1)
    hqr

/-- Compose an exact word ending at the trace source cut with an exact trace.
This is the Lean version of the manuscript composite `p q` in the finite
family `C = {p q : p in R, q in Q}`. -/
noncomputable def traceComposite
    {c : Nat}
    (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height)
    (q : AMExact H c
      (FiniteFatTree.traceSourceCut H y n hn))
    (p : FiniteFatTree.ExactTrace H y n hn) :
    AM H c 1 :=
  H.composeAcross q p.1

theorem traceComposite_representative_agrees
    {c : Nat}
    (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height)
    (q : AMExact H c
      (FiniteFatTree.traceSourceCut H y n hn))
    (p : FiniteFatTree.ExactTrace H y n hn)
    (x : T) (hx : LevelTree.lev x ≤ c) :
    (traceComposite H y n hn q p).representative H x =
      p.1.representative H (q.1.representative H x) := by
  exact H.composeAcross_representative_agrees q p.1 x hx

/-- A raw exact-trace update canonically yields a finite successor
fan. The existential successor choices in IsRawTraceUpdate are made
only on the finite source level; below it the table is the identity. -/
noncomputable def rawSuccessorFanOfUpdate
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1)
    (n : Nat) (hn : n ≤ y.height)
    (q : FiniteFatTree.ExactTrace H y n hn)
    (theta : FiniteFatTree.ExactTrace H
      (FiniteFatTree.appendRow H y h) n (by
        rw [FiniteFatTree.appendRow_height]
        omega))
    (hupdate :
      FiniteFatTree.IsRawTraceUpdate H y h n hn q theta) :
    RawSuccessorFan H q.1 := by
  classical
  let c0 : Nat := FiniteFatTree.traceSourceCut H y n hn
  have hct :
      c0 ≤ q.1.rowEndLevel H := by
    calc
      c0 ≤ FiniteFatTree.traceTargetCut H y :=
        FiniteFatTree.traceSourceCut_le_target H y n hn
      _ = q.1.rowEndLevel H :=
        (q.rowEndLevel H).symm
  let chosen : InitialNode T c0 → T := fun x =>
    if hx : LevelTree.lev x.1 = c0 then
      Classical.choose (hupdate x.1 hx)
    else
      x.1
  have chosen_bound :
      ∀ x : InitialNode T c0,
        LevelTree.lev (chosen x) ≤ q.1.rowEndLevel H + 1 := by
    intro x
    by_cases hx : LevelTree.lev x.1 = c0
    · let hz := Classical.choose_spec (hupdate x.1 hx)
      have hqlev :
          LevelTree.lev (q.1.representative H x.1) =
            q.1.rowEndLevel H := by
        calc
          LevelTree.lev (q.1.representative H x.1) =
              H.levelMap (q.1.representative H).map
                (LevelTree.lev x.1) :=
            (H.levelMap_eq (q.1.representative H).map
              (a := x.1)).symm
          _ = H.levelMap (q.1.representative H).map c0 := by
            rw [hx]
          _ = q.1.rowEndLevel H := rfl
      have hzlev :=
        LevelTree.covBy_level_eq hz.1
      dsimp [chosen]
      rw [dif_pos hx]
      rw [hzlev, hqlev]
    · have hxlt : LevelTree.lev x.1 < c0 := by
        omega
      dsimp [chosen]
      rw [dif_neg hx]
      omega
  refine {
    toFun := fun x => ⟨chosen x, chosen_bound x⟩
    eq_id_below := ?_
    top_covBy := ?_
  }
  · intro x hx
    have hne : LevelTree.lev x.1 ≠ c0 := by omega
    dsimp [chosen]
    rw [dif_neg hne]
  · intro x hx
    let hz := Classical.choose_spec (hupdate x.1 hx)
    dsimp [chosen]
    rw [dif_pos hx]
    exact hz.1

/-- The fan chosen from a raw update records the same top-level successor
which appears in that update. -/
theorem rawSuccessorFanOfUpdate_realizes
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1)
    (n : Nat) (hn : n ≤ y.height)
    (q : FiniteFatTree.ExactTrace H y n hn)
    (theta : FiniteFatTree.ExactTrace H
      (FiniteFatTree.appendRow H y h) n (by
        rw [FiniteFatTree.appendRow_height]
        omega))
    (hupdate :
      FiniteFatTree.IsRawTraceUpdate H y h n hn q theta)
    (x : T)
    (hx : LevelTree.lev x =
      FiniteFatTree.traceSourceCut H y n hn) :
    theta.1.representative H x =
      H.canonicalExtension (h.representative H) y.terminalCut
        ((rawSuccessorFanOfUpdate H y h n hn q theta hupdate).toFun
          ⟨x, by omega⟩).1 := by
  classical
  let hz := Classical.choose_spec (hupdate x hx)
  have hfan :
      ((rawSuccessorFanOfUpdate H y h n hn q theta hupdate).toFun
        ⟨x, by omega⟩).1 =
        Classical.choose (hupdate x hx) := by
    simp [rawSuccessorFanOfUpdate, hx]
  rw [hfan]
  exact hz.2

end FatTree
end SMTree
end SuccessorTree

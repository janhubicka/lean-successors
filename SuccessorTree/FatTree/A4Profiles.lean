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

/-- The successor decomposition carried by one top-level entry of a
raw fan. -/
noncomputable def RawSuccessorFan.code
    {c : Nat} {q : AM H c 1}
    (e : RawSuccessorFan H q)
    (x : InitialNode T c)
    (hx : LevelTree.lev x.1 = c) :
    SuccCode S (q.representative H x.1) (e.toFun x).1 :=
  succCodeOfCovBy S (e.top_covBy x hx)

/-- A total history map followed by a one-level skip realizes a raw fan when
it repeats that fan's successor data over every source-top node.  No
admissibility of the raw fan is assumed. -/
def HistoryRealizesFan
    {c r : Nat}
    (q : AM H c 1)
    (P : MMap H)
    (E : OneLevelLetter H r)
    (e : RawSuccessorFan H q) : Prop :=
  ∀ (x : InitialNode T c)
    (hx : LevelTree.lev x.1 = c),
      S.succ
          (P (q.representative H x.1))
          (e.code H x hx).params
          (e.code H x hx).char =
        some (E (P (q.representative H x.1)))

/-- A history step can realize at most one raw fan at a fixed trace.  This is
the formal uniqueness behind the manuscript's successor-fan profile. -/
theorem historyRealizesFan_unique
    {c r : Nat}
    (q : AM H c 1)
    (P : MMap H)
    (E : OneLevelLetter H r)
    {e f : RawSuccessorFan H q}
    (he : HistoryRealizesFan H q P E e)
    (hf : HistoryRealizesFan H q P E f) :
    e = f := by
  apply RawSuccessorFan.ext H
  funext x
  apply Subtype.ext
  by_cases hxlt : LevelTree.lev x.1 < c
  · rw [e.eq_id_below x hxlt, f.eq_id_below x hxlt]
  · have hx : LevelTree.lev x.1 = c := by
      have hxle := x.2
      omega
    let ce := e.code H x hx
    let cf := f.code H x hx
    have hsame :=
      S.s2 (he x hx) (hf x hx)
    have hparams : ce.params = cf.params := hsame.2.1
    have hchar : ce.char = cf.char := hsame.2.2
    have he0 := ce.succ_eq
    have hf0 := cf.succ_eq
    rw [hparams, hchar] at he0
    exact Option.some.inj (he0.symm.trans hf0)

/-- Package the M3 duplication from a trace terminal level to a later
history level as a one-level letter at that later level. -/
noncomputable def duplicateHistoryLetter
    (n m : Nat) (hnm : n < m) : OneLevelLetter H m where
  toMMap := H.duplicate n m hnm
  skips := H.duplicate_skips n m hnm

/-- Once a later history point lies above every chosen successor in a raw
fan, the single M3 duplication at that later level realizes the whole raw fan
simultaneously.  This is the bridge which lets the A4 argument work with raw
finite successor tables rather than assuming that those tables themselves
extend to admissible one-level maps. -/
theorem historyRealizesFan_of_below
    {c m : Nat}
    (q : AM H c 1)
    (P : MMap H)
    (e : RawSuccessorFan H q)
    (hqm : q.rowEndLevel H < m)
    (hPtop : H.levelMap P.map (q.rowEndLevel H) = m)
    (hbelow :
      ∀ (x : InitialNode T c)
        (hx : LevelTree.lev x.1 = c),
          (e.toFun x).1 ≤ P (q.representative H x.1)) :
    HistoryRealizesFan H q P
      (duplicateHistoryLetter H (q.rowEndLevel H) m hqm) e := by
  intro x hx
  let code := e.code H x hx
  have hqlev :
      LevelTree.lev (q.representative H x.1) = q.rowEndLevel H := by
    calc
      LevelTree.lev (q.representative H x.1) =
          H.levelMap (q.representative H).map (LevelTree.lev x.1) :=
        (H.levelMap_eq (q.representative H).map (a := x.1)).symm
      _ = H.levelMap (q.representative H).map c := by rw [hx]
      _ = q.rowEndLevel H := rfl
  have hPlev :
      LevelTree.lev (P (q.representative H x.1)) = m := by
    calc
      LevelTree.lev (P (q.representative H x.1)) =
          H.levelMap P.map (LevelTree.lev (q.representative H x.1)) :=
        (H.levelMap_eq P.map
          (a := q.representative H x.1)).symm
      _ = H.levelMap P.map (q.rowEndLevel H) := by rw [hqlev]
      _ = m := hPtop
  have hdup :=
    H.duplicate_rule
      (q.rowEndLevel H) m hqm
      (q.representative H x.1)
      (P (q.representative H x.1))
      code.params code.char (e.toFun x).1
      hqlev hPlev code.succ_eq (hbelow x hx)
  simpa [duplicateHistoryLetter, code] using hdup

/-- The profile coordinate of a history step at one trace: record the unique
realized raw fan when it exists, and bottom otherwise. -/
noncomputable def historyProfile
    {c r : Nat}
    (q : AM H c 1)
    (P : MMap H)
    (E : OneLevelLetter H r) :
    Option (RawSuccessorFan H q) := by
  classical
  by_cases h :
      ∃ e : RawSuccessorFan H q,
        HistoryRealizesFan H q P E e
  · exact some (Classical.choose h)
  · exact none

theorem historyProfile_eq_some
    {c r : Nat}
    (q : AM H c 1)
    (P : MMap H)
    (E : OneLevelLetter H r)
    (e : RawSuccessorFan H q)
    (he : HistoryRealizesFan H q P E e) :
    historyProfile H q P E = some e := by
  classical
  unfold historyProfile
  rw [dif_pos ⟨e, he⟩]
  congr 1
  exact historyRealizesFan_unique H q P E
    (Classical.choose_spec ⟨e, he⟩) he

/-- A finite profile over a finite family of traces: at each trace we either
record a raw successor fan or none. The latter is the manuscript's bottom
symbol recording failure to match that fan. -/
abbrev FanProfile {c : Nat}
    (C : Type*) [Fintype C]
    (trace : C → AM H c 1) :=
  ∀ i : C, Option (RawSuccessorFan H (trace i))

noncomputable instance fanProfileDecidableEq
    {c : Nat} {C : Type*} [Fintype C]
    (trace : C → AM H c 1) :
    DecidableEq (FanProfile H C trace) :=
  Classical.decEq _

noncomputable instance fanProfileFintype
    {c : Nat} {C : Type*} [Fintype C]
    (trace : C → AM H c 1) :
    Fintype (FanProfile H C trace) := by
  classical
  letI fans :
      ∀ i : C, Fintype (RawSuccessorFan H (trace i)) :=
    fun i => RawSuccessorFan.fintype H (trace i)
  infer_instance

/-- Simultaneous successor-fan profile of one history step over a
finite trace family. -/
noncomputable def historyFanProfile
    {c r : Nat}
    {C : Type*} [Fintype C]
    (trace : C → AM H c 1)
    (P : MMap H)
    (E : OneLevelLetter H r) :
    FanProfile H C trace :=
  fun i => historyProfile H (trace i) P E

theorem historyFanProfile_eq_some
    {c r : Nat}
    {C : Type*} [Fintype C]
    (trace : C → AM H c 1)
    (P : MMap H)
    (E : OneLevelLetter H r)
    (i : C)
    (e : RawSuccessorFan H (trace i))
    (he : HistoryRealizesFan H (trace i) P E e) :
    historyFanProfile H trace P E i = some e :=
  historyProfile_eq_some H (trace i) P E e he

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
  letI : Fintype (C → κ) := Fintype.ofFinite _
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

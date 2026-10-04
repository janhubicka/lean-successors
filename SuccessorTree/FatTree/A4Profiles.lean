import SuccessorTree.FatTree.A4Trace
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

end FatTree
end SMTree
end SuccessorTree

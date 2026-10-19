import SuccessorTree.V10.PrescribedBoringData
import SuccessorTree.V10.ConcreteKptM1
import Mathlib.Tactic

/-!
# Intrinsic finite full type profiles in the binary presentation

A finite base carries its actual auxiliary E relation. Its profile contains
every admissible partial type over every initial ordinary socle, including
types not realized by a later vertex of the base. The distinguished type
vertex does not belong to the ordinary socle.

Type-respecting maps are specified by their finite action, their coherent
cut map, the canonical successor law and preservation of finite labelled
L-continuations. Extendability to a global shape map is not part of any
definition in this file.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- A finite enumerated partial structure in the prescribed free amalgamation
class. Off-carrier data are immaterial to the profile. -/
structure FiniteTypeBase (family : List (NormalizedForbidden db du dd)) where
  str : EnumeratedPartialStructure db du dd
  avoids : ∀ bad, bad ∈ family → bad.Avoids str.L

namespace FiniteTypeBase

abbrev size (A : FiniteTypeBase family) : Nat := A.str.size

/-- All admissible full types over one of the initial socles of `A`. The
arbitrary vertex `0` on the right is discarded by `SameOrdinaryAtCut`. -/
def profile (A : FiniteTypeBase family) : Set (AdmissibleKptNode family) :=
  {u | u.1.1 ≤ A.size ∧
    SameOrdinaryAtCut u.1.2 (A.str.partialTypeAt u.1.1 0)}

end FiniteTypeBase

/-- The finite domain of a type-respecting approximation. -/
abbrev TypeProfile (A : FiniteTypeBase family) : Type := A.profile

namespace TypeProfile

variable {A : FiniteTypeBase family}

abbrev level (u : TypeProfile A) : Nat := u.1.1.1

def cut (u : TypeProfile A) : Fin (A.size + 1) :=
  ⟨u.level, Nat.lt_succ_iff.mpr u.2.1⟩

theorem level_le_size (u : TypeProfile A) : u.level ≤ A.size := u.2.1

theorem same_socle (u : TypeProfile A) :
    SameOrdinaryAtCut u.1.1.2 (A.str.partialTypeAt u.level 0) := u.2.2

end TypeProfile

/-- One full compatible front, with its common level explicit in the type. -/
abbrev TypeProfileFront (A : FiniteTypeBase family)
    (i : Fin (A.size + 1)) :=
  {T : PartialTypeWithE i.val db du dd //
    IsAdmissibleRawType family (⟨i.val, T⟩ : RawPartialTypeNode db du dd) ∧
      SameOrdinaryAtCut T (A.str.partialTypeAt i.val 0)}

namespace TypeProfileFront

variable {A : FiniteTypeBase family} {i : Fin (A.size + 1)}

def toProfile (T : TypeProfileFront A i) : TypeProfile A :=
  ⟨⟨⟨i.val, T.val⟩, T.property.1⟩,
    Nat.le_of_lt_succ i.isLt, T.property.2⟩

@[simp] theorem toProfile_level (T : TypeProfileFront A i) :
    T.toProfile.level = i.val := rfl

@[simp] theorem toProfile_cut (T : TypeProfileFront A i) :
    T.toProfile.cut = i := by apply Fin.ext; rfl

theorem toProfile_injective : Function.Injective
    (toProfile : TypeProfileFront A i → TypeProfile A) := by
  intro T U h
  apply Subtype.ext
  have hRaw := congrArg (fun u : TypeProfile A => u.1.1) h
  exact eq_of_heq (Sigma.mk.inj_iff.mp hRaw).2

end TypeProfileFront

theorem TypeProfile.exists_front {A : FiniteTypeBase family}
    (u : TypeProfile A) (i : Fin (A.size + 1)) (hu : u.level = i.val) :
    ∃ T : TypeProfileFront A i, T.toProfile = u := by
  rcases u with ⟨⟨⟨n, Q⟩, hAd⟩, hBound, hSame⟩
  change n = i.val at hu
  subst n
  exact ⟨⟨Q, hAd, hSame⟩, rfl⟩

/-- A level together with a complete relational type; this dependent pair
lets continuation labels be compared without choosing transports of indices. -/
abbrev RawRelationalTypeNode (db du dd : Nat) :=
  (n : Nat) × RelationalPrefixType n db du dd

def AdmissibleKptNode.relationalNode (u : AdmissibleKptNode family) :
    RawRelationalTypeNode db du dd := ⟨u.1.1, u.1.2.lReduct⟩

/-- A finite L-only continuation over the indicated initial socle. Its upper
carrier is a subset `P` of a bounded ordinal, preserving its induced order.
Taking `P = Set.univ` gives a consecutive enumeration. Labels may repeat;
there is no condition on unused slots and no auxiliary E on the continuation. -/
structure ProfileContinuation (A : FiniteTypeBase family)
    (i : Fin (A.size + 1)) (r : Nat) (P : Set (Fin r))
    (labels : Fin r → AdmissibleKptNode family)
    (W : AgeTestModel db du dd) : Prop where
  carrier : ∀ x, x ∈ W.carrier ↔
    x < i.val ∨ ∃ y : Fin r, y ∈ P ∧ x = i.val + y.val
  binary_socle : ∀ x y : Fin i.val, ∀ t : Fin db,
    W.binary x.val y.val t = A.str.L.binary x.val y.val t
  unary_socle : ∀ x : Fin i.val, ∀ t : Fin du,
    W.unary x.val t = A.str.L.unary x.val t
  diagonal_socle : ∀ x : Fin i.val, ∀ t : Fin dd,
    W.diagonal x.val t = A.str.L.diagonal x.val t
  upper_types : ∀ x : Fin r, x ∈ P →
    (⟨i.val, RelationalPrefixType.ofAgeModel W i.val (i.val + x.val)⟩ :
      RawRelationalTypeNode db du dd) = (labels x).relationalNode

/-- Equality of the entire induced upper L-structures, under their increasing
enumerations. Both directed binary orientations and singleton data remain. -/
structure SameUpperL (W V : AgeTestModel db du dd)
    (i j r : Nat) (P : Set (Fin r)) : Prop where
  binary : ∀ x y : Fin r, x ∈ P → y ∈ P → ∀ t : Fin db,
    W.binary (i + x.val) (i + y.val) t =
      V.binary (j + x.val) (j + y.val) t
  unary : ∀ x : Fin r, x ∈ P → ∀ t : Fin du,
    W.unary (i + x.val) t = V.unary (j + x.val) t
  diagonal : ∀ x : Fin r, x ∈ P → ∀ t : Fin dd,
    W.diagonal (i + x.val) t = V.diagonal (j + x.val) t

/-- The finite coherent part of a type-respecting map. The successor law is
the literal weak canonical law on every equation contained in the domain. -/
structure CoherentTypeProfileMap (A B : FiniteTypeBase family) where
  toFun : TypeProfile A → AdmissibleKptNode family
  injective' : Function.Injective toFun
  cutMap : Fin (A.size + 1) → Fin (B.size + 1)
  cut_strictMono : StrictMono cutMap
  cut_zero : cutMap ⟨0, Nat.zero_lt_succ A.size⟩ =
    ⟨0, Nat.zero_lt_succ B.size⟩
  cut_top : cutMap (Fin.last A.size) = Fin.last B.size
  level_eq : ∀ u, (toFun u).1.1 = (cutMap u.cut).val
  maps_socle : ∀ u,
    SameOrdinaryAtCut (toFun u).1.2
      (B.str.partialTypeAt (toFun u).1.1 0)
  root_fixed : ∀ u, u.level = 0 → toFun u = u.1
  «prefix» : ∀ u v, u.1 ≤ v.1 → toFun u ≤ toFun v
  weak_succ : ∀ (u v : TypeProfile A) (p : List (TypeProfile A))
      (c : AdmissibleKptSigma family),
    (admissibleKptSTree family).succ u.1 (p.map Subtype.val) c = some v.1 →
    ∃ d : AdmissibleKptNode family,
      (admissibleKptSTree family).succ (toFun u) (p.map toFun) c = some d ∧
        d ≤ toFun v

namespace CoherentTypeProfileMap

variable {A B C : FiniteTypeBase family}

instance : CoeFun (CoherentTypeProfileMap A B)
    (fun _ => TypeProfile A → AdmissibleKptNode family) := ⟨toFun⟩

/-- The codomain profile membership is determined by the cut and ordinary
socle clauses; it is not a separate completion requirement. -/
def mapNode (h : CoherentTypeProfileMap A B) (u : TypeProfile A) :
    TypeProfile B :=
  ⟨h u, by
    refine ⟨?_, h.maps_socle u⟩
    rw [h.level_eq]
    exact Nat.le_of_lt_succ (h.cutMap u.cut).isLt⟩

@[simp] theorem mapNode_val (h : CoherentTypeProfileMap A B)
    (u : TypeProfile A) : (h.mapNode u).1 = h u := rfl

/-- Every allowed finite labelled continuation has an allowed continuation
with the transported labels and the same upper structure. The witnesses are
finite L-models. No global map appears in this intrinsic age condition. -/
def PreservesAge (h : CoherentTypeProfileMap A B) : Prop :=
  ∀ (i : Fin (A.size + 1)) (r : Nat) (P : Set (Fin r))
    (labels : Fin r → TypeProfile A)
    (W : AgeTestModel db du dd),
    ProfileContinuation A i r P (fun x => (labels x).1) W →
    (∀ bad, bad ∈ family → bad.Avoids W) →
    ∃ V : AgeTestModel db du dd,
      ProfileContinuation B (h.cutMap i) r P (fun x => h (labels x)) V ∧
      SameUpperL W V i.val (h.cutMap i).val r P ∧
      (∀ bad, bad ∈ family → bad.Avoids V)

end CoherentTypeProfileMap

/-- An intrinsic type-respecting finite full-profile map. -/
structure FiniteTypeProfileMap (A B : FiniteTypeBase family)
    extends CoherentTypeProfileMap A B where
  age : toCoherentTypeProfileMap.PreservesAge

namespace FiniteTypeProfileMap

variable {A B : FiniteTypeBase family}

instance : CoeFun (FiniteTypeProfileMap A B)
    (fun _ => TypeProfile A → AdmissibleKptNode family) :=
  ⟨fun h => h.toCoherentTypeProfileMap.toFun⟩

end FiniteTypeProfileMap

/-- Approximation maps are identified by their actual finite functions. The
existential target is a finite base and finite intrinsic certificate, not a
global shape map. This discards irrelevant representations of the target. -/
def TypeRespectingEmbedding (A : FiniteTypeBase family) :=
  {f : TypeProfile A → AdmissibleKptNode family //
    ∃ (B : FiniteTypeBase family) (h : FiniteTypeProfileMap A B),
      f = h.toCoherentTypeProfileMap.toFun}

end SuccessorTree.V10

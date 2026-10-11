import SuccessorTree.V10.PrescribedETransport
import SuccessorTree.V10.PartialTypeRestriction
import Mathlib.Tactic

/-!
# Recover upper original's complete type from a larger Kpt record

The prescribed non-neutral extension uses f(type_A^ell(u)) to choose the
inserted L-relations with each old upper ordinary vertex u. For a uniform
operation on genuine admissible Kpt nodes, that source type must be
determined by the complete original type at the longer free cut.

It is: if two ambient finite partial structures A,C realize the same
complete L+ partial type through cut at possibly different type vertices
v,w, then each ordinary source vertex u<cut has EXACTLY the same complete
L+ type through every ell<=cut in both structures.

The extraction selects an ordinary coordinate u of the longer type,
rather than its distinguished type vertex. All directed binary positive
and absent tuples, unary, diagonal and auxiliary E atoms are retained.

This is one key representation-independent input for the prescribed
upper columns; lower column/cut choice independence is already proved
in PrescribedSocleColumn and PrescribedBoringData. The full map is
still an independent obligation.
-/

namespace SuccessorTree.V10

/-- Read an ordinary socle vertex u<cut as the distinguished type
coordinate of an extracted shorter source type, while retaining
all other ordinary coordinates of the shorter socle. -/
def ordinarySourceCoordinate
    {ell cut : Nat} (hEll : ell ≤ cut) (u : Fin cut) :
    Option (Fin ell) → Option (Fin cut)
  | none => some u
  | some i => some ⟨i.val, lt_of_lt_of_le i.isLt hEll⟩

/-- The literal original coordinate at which an extracted atom is
read does not change under this ordinary-source recoding. -/
@[simp] theorem prefixVertexIndex_ordinarySourceCoordinate
    {ell cut : Nat} (hEll : ell ≤ cut) (u : Fin cut)
    (v : Nat) (a : Option (Fin ell)) :
    prefixVertexIndex v (ordinarySourceCoordinate hEll u a) =
      prefixVertexIndex u.val a := by
  cases a with
  | none => rfl
  | some a => rfl

/-- TWO ambient structures agreeing on a complete partial type at cut
must agree on the entire induced L+ type of EVERY ordinary u<cut over
the earlier ell-socle; both ambient type vertices may differ. -/
theorem partialTypeAt_ordinary_eq_of_fullType_eq
    {db du dd : Nat}
    (A C : EnumeratedPartialStructure db du dd)
    (ell cut u v w : Nat)
    (hEll : ell ≤ cut) (hu : u < cut)
    (hFull : A.partialTypeAt cut v = C.partialTypeAt cut w) :
    A.partialTypeAt ell u = C.partialTypeAt ell u := by
  let fu : Fin cut := ⟨u,hu⟩
  let enc := ordinarySourceCoordinate hEll fu
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b t
      have h :=
        congrArg (fun T : PartialTypeWithE cut db du dd =>
          T.lReduct.binary (enc a) (enc b) t) hFull
      change A.L.binary
          (prefixVertexIndex v (enc a))
          (prefixVertexIndex v (enc b)) t =
        C.L.binary
          (prefixVertexIndex w (enc a))
          (prefixVertexIndex w (enc b)) t at h
      change A.L.binary (prefixVertexIndex u a)
          (prefixVertexIndex u b) t =
        C.L.binary (prefixVertexIndex u a)
          (prefixVertexIndex u b) t
      simpa only [enc, fu, prefixVertexIndex_ordinarySourceCoordinate]
        using h
    · intro a t
      have h :=
        congrArg (fun T : PartialTypeWithE cut db du dd =>
          T.lReduct.unary (enc a) t) hFull
      change A.L.unary (prefixVertexIndex v (enc a)) t =
        C.L.unary (prefixVertexIndex w (enc a)) t at h
      change A.L.unary (prefixVertexIndex u a) t =
        C.L.unary (prefixVertexIndex u a) t
      simpa only [enc, fu, prefixVertexIndex_ordinarySourceCoordinate]
        using h
    · intro a t
      have h :=
        congrArg (fun T : PartialTypeWithE cut db du dd =>
          T.lReduct.diagonal (enc a) t) hFull
      change A.L.diagonal (prefixVertexIndex v (enc a)) t =
        C.L.diagonal (prefixVertexIndex w (enc a)) t at h
      change A.L.diagonal (prefixVertexIndex u a) t =
        C.L.diagonal (prefixVertexIndex u a) t
      simpa only [enc, fu, prefixVertexIndex_ordinarySourceCoordinate]
        using h
  · intro a b
    have h :=
      congrArg (fun T : PartialTypeWithE cut db du dd =>
        T.eRelation (enc a) (enc b)) hFull
    change A.E (prefixVertexIndex v (enc a))
        (prefixVertexIndex v (enc b)) =
      C.E (prefixVertexIndex w (enc a))
        (prefixVertexIndex w (enc b)) at h
    change A.E (prefixVertexIndex u a) (prefixVertexIndex u b) =
      C.E (prefixVertexIndex u a) (prefixVertexIndex u b)
    simpa only [enc, fu, prefixVertexIndex_ordinarySourceCoordinate]
      using h

end SuccessorTree.V10

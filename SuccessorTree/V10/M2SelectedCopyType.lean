import SuccessorTree.V10.M2BoundedCopyRecords
import SuccessorTree.V10.ShapeMapFullRecovery
import Mathlib.Tactic

/-!
# Identify actual selected source types in the M2 nonedge witness

The dense source L-age model is pulled back only on genuine selected
coordinates; neutral fillers have no prescribed Kpt type.  At a selected
upper vertex, the complete L type is exactly the pullback of the ambient
finite target age.  When that target type is an actual F-image of an
admissible source type, full retained-record recovery identifies the
pullback with that source type, including all absent directed relations,
singletons, loops and diagonal facts.
-/
namespace SuccessorTree.V10

/-- Send the distinguished type vertex to the selected upper position,
and the old ordinary vertices through the level map. -/
def boundedCopyTypeAddress {n : Nat} (lambda : Nat → Nat) (upper : Nat) :
    Option (Fin n) → Nat
  | none => upper
  | some i => lambda i.val

private theorem boundedCopySourceAge_type_binary
    {n m r db du dd : Nat}
    (V : AgeTestModel db du dd) (lambda : Nat → Nat)
    (e : Fin r → Nat) (a : Fin r) (ha : m < e a)
    (x y : Option (Fin n)) (t : Fin db) :
    (boundedCopySourceAge V lambda n m r e).binary
      (prefixVertexIndex (n+a.val) x) (prefixVertexIndex (n+a.val) y) t =
      V.binary (boundedCopyTypeAddress lambda (e a) x)
        (boundedCopyTypeAddress lambda (e a) y) t := by
  have hu : boundedCopyReal n m r e (n+a.val) := Or.inr ⟨a,rfl,ha⟩
  cases x with
  | none =>
      cases y with
      | none =>
          simpa only [prefixVertexIndex, boundedCopyTypeAddress,
            boundedCopyAddress_upper] using
            (boundedCopySourceAge_real_binary V lambda n m r e
              (n+a.val) (n+a.val) (by omega) (by omega) hu hu t)
      | some j =>
          simpa only [prefixVertexIndex, boundedCopyTypeAddress,
            boundedCopyAddress_upper,
            boundedCopyAddress_low lambda n r e j.val j.isLt] using
            (boundedCopySourceAge_real_binary V lambda n m r e
              (n+a.val) j.val (by omega) (by omega) hu (Or.inl j.isLt) t)
  | some i =>
      cases y with
      | none =>
          simpa only [prefixVertexIndex, boundedCopyTypeAddress,
            boundedCopyAddress_upper,
            boundedCopyAddress_low lambda n r e i.val i.isLt] using
            (boundedCopySourceAge_real_binary V lambda n m r e
              i.val (n+a.val) (by omega) (by omega) (Or.inl i.isLt) hu t)
      | some j =>
          simpa only [prefixVertexIndex, boundedCopyTypeAddress,
            boundedCopyAddress_low lambda n r e i.val i.isLt,
            boundedCopyAddress_low lambda n r e j.val j.isLt] using
            (boundedCopySourceAge_real_binary V lambda n m r e
              i.val j.val (by omega) (by omega)
              (Or.inl i.isLt) (Or.inl j.isLt) t)

private theorem boundedCopySourceAge_type_unary
    {n m r db du dd : Nat}
    (V : AgeTestModel db du dd) (lambda : Nat → Nat)
    (e : Fin r → Nat) (a : Fin r) (ha : m < e a)
    (x : Option (Fin n)) (t : Fin du) :
    (boundedCopySourceAge V lambda n m r e).unary
      (prefixVertexIndex (n+a.val) x) t =
      V.unary (boundedCopyTypeAddress lambda (e a) x) t := by
  have hu : boundedCopyReal n m r e (n+a.val) := Or.inr ⟨a,rfl,ha⟩
  cases x with
  | none =>
      simpa only [prefixVertexIndex,boundedCopyTypeAddress,
        boundedCopyAddress_upper] using
        (boundedCopySourceAge_real_unary V lambda n m r e
          (n+a.val) (by omega) hu t)
  | some i =>
      simpa only [prefixVertexIndex,boundedCopyTypeAddress,
        boundedCopyAddress_low lambda n r e i.val i.isLt] using
        (boundedCopySourceAge_real_unary V lambda n m r e
          i.val (by omega) (Or.inl i.isLt) t)

private theorem boundedCopySourceAge_type_diagonal
    {n m r db du dd : Nat}
    (V : AgeTestModel db du dd) (lambda : Nat → Nat)
    (e : Fin r → Nat) (a : Fin r) (ha : m < e a)
    (x : Option (Fin n)) (t : Fin dd) :
    (boundedCopySourceAge V lambda n m r e).diagonal
      (prefixVertexIndex (n+a.val) x) t =
      V.diagonal (boundedCopyTypeAddress lambda (e a) x) t := by
  have hu : boundedCopyReal n m r e (n+a.val) := Or.inr ⟨a,rfl,ha⟩
  cases x with
  | none =>
      simpa only [prefixVertexIndex,boundedCopyTypeAddress,
        boundedCopyAddress_upper] using
        (boundedCopySourceAge_real_diagonal V lambda n m r e
          (n+a.val) (by omega) hu t)
  | some i =>
      simpa only [prefixVertexIndex,boundedCopyTypeAddress,
        boundedCopyAddress_low lambda n r e i.val i.isLt] using
        (boundedCopySourceAge_real_diagonal V lambda n m r e
          i.val (by omega) (Or.inl i.isLt) t)

/-- The full selected source type is obtained by extracting its induced
L record from the target finite age, with the ordinary coordinates
reindexed through lambda.  In particular negative directed atoms survive. -/
theorem boundedCopySourceAge_selected_ltype
    {n m r db du dd : Nat}
    (V : AgeTestModel db du dd) (lambda : Nat → Nat)
    (e : Fin r → Nat) (a : Fin r) (ha : m < e a)
    (Q : RelationalPrefixType n db du dd)
    (hB : ∀ x y : Option (Fin n), ∀ t : Fin db,
      V.binary (boundedCopyTypeAddress lambda (e a) x)
        (boundedCopyTypeAddress lambda (e a) y) t = Q.binary x y t)
    (hU : ∀ x : Option (Fin n), ∀ t : Fin du,
      V.unary (boundedCopyTypeAddress lambda (e a) x) t = Q.unary x t)
    (hD : ∀ x : Option (Fin n), ∀ t : Fin dd,
      V.diagonal (boundedCopyTypeAddress lambda (e a) x) t = Q.diagonal x t) :
    RelationalPrefixType.ofAgeModel
      (boundedCopySourceAge V lambda n m r e) n (n+a.val) = Q := by
  apply RelationalPrefixType.eq_of_atoms
  · intro x y t
    exact (boundedCopySourceAge_type_binary V lambda e a ha x y t).trans (hB x y t)
  · intro x t
    exact (boundedCopySourceAge_type_unary V lambda e a ha x t).trans (hU x t)
  · intro x t
    exact (boundedCopySourceAge_type_diagonal V lambda e a ha x t).trans (hD x t)

/-- Key M2 identification: if a selected upper vertex in the target
finite witness has the *genuine* complete F-image type, its pullback in
the bounded source model has precisely the original complete source
L-type.  This is independent of B3 and M2. -/
theorem boundedCopySourceAge_selected_type_of_shapeMap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (u : AdmissibleKptNode family)
    (V : AgeTestModel db du dd) (m r : Nat)
    (e : Fin r → Nat) (a : Fin r) (ha : m < e a)
    (hImage : RelationalPrefixType.ofAgeModel V
        (LevelTree.lev (F u)) (e a) = (F u).1.2.lReduct) :
    RelationalPrefixType.ofAgeModel
      (boundedCopySourceAge V (kptShapeLevelMap family F)
        (LevelTree.lev u) m r e)
      (LevelTree.lev u) (LevelTree.lev u+a.val) = u.1.2.lReduct := by
  let lambda := kptShapeLevelMap family F
  let rho := retainedSocleIndex family F u
  have hRec := shapeMap_recovers_complete_record family F u
  have hAddr (x : Option (Fin (LevelTree.lev u))) :
      prefixVertexIndex (e a) (Option.map rho x) =
        boundedCopyTypeAddress lambda (e a) x := by
    cases x with
    | none => rfl
    | some i => rfl
  have hB : ∀ x y : Option (Fin (LevelTree.lev u)), ∀ t : Fin db,
      V.binary (boundedCopyTypeAddress lambda (e a) x)
        (boundedCopyTypeAddress lambda (e a) y) t = u.1.2.lReduct.binary x y t := by
    intro x y t
    have hA := congrArg
      (fun Q : RelationalPrefixType (LevelTree.lev (F u)) db du dd =>
        Q.binary (Option.map rho x) (Option.map rho y) t) hImage
    have hR := congrArg
      (fun Q : PartialTypeWithE (LevelTree.lev u) db du dd =>
        Q.lReduct.binary x y t) hRec
    change V.binary (prefixVertexIndex (e a) (Option.map rho x))
      (prefixVertexIndex (e a) (Option.map rho y)) t =
        (F u).1.2.lReduct.binary (Option.map rho x) (Option.map rho y) t at hA
    change (F u).1.2.lReduct.binary (Option.map rho x)
      (Option.map rho y) t = u.1.2.lReduct.binary x y t at hR
    simpa only [hAddr] using hA.trans hR
  have hU : ∀ x : Option (Fin (LevelTree.lev u)), ∀ t : Fin du,
      V.unary (boundedCopyTypeAddress lambda (e a) x) t =
        u.1.2.lReduct.unary x t := by
    intro x t
    have hA := congrArg
      (fun Q : RelationalPrefixType (LevelTree.lev (F u)) db du dd =>
        Q.unary (Option.map rho x) t) hImage
    have hR := congrArg
      (fun Q : PartialTypeWithE (LevelTree.lev u) db du dd =>
        Q.lReduct.unary x t) hRec
    change V.unary (prefixVertexIndex (e a) (Option.map rho x)) t =
      (F u).1.2.lReduct.unary (Option.map rho x) t at hA
    change (F u).1.2.lReduct.unary (Option.map rho x) t =
      u.1.2.lReduct.unary x t at hR
    simpa only [hAddr] using hA.trans hR
  have hD : ∀ x : Option (Fin (LevelTree.lev u)), ∀ t : Fin dd,
      V.diagonal (boundedCopyTypeAddress lambda (e a) x) t =
        u.1.2.lReduct.diagonal x t := by
    intro x t
    have hA := congrArg
      (fun Q : RelationalPrefixType (LevelTree.lev (F u)) db du dd =>
        Q.diagonal (Option.map rho x) t) hImage
    have hR := congrArg
      (fun Q : PartialTypeWithE (LevelTree.lev u) db du dd =>
        Q.lReduct.diagonal x t) hRec
    change V.diagonal (prefixVertexIndex (e a) (Option.map rho x)) t =
      (F u).1.2.lReduct.diagonal (Option.map rho x) t at hA
    change (F u).1.2.lReduct.diagonal (Option.map rho x) t =
      u.1.2.lReduct.diagonal x t at hR
    simpa only [hAddr] using hA.trans hR
  exact boundedCopySourceAge_selected_ltype V lambda e a ha u.1.2.lReduct
    hB hU hD

end SuccessorTree.V10
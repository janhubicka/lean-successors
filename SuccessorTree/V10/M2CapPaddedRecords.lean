import SuccessorTree.V10.M2CapRetainedAtoms
import SuccessorTree.V10.M2SelectedCopyPadded
import Mathlib.Tactic

/-!
# Pair and singleton records in the image of a padded common cap

Nonedge padding retains all relations between real vertices, even
upper--upper relations. Complete ShapeMap retained-record recovery
therefore reproduces each full pair and singleton at the image-level
coordinates in ONE capped admissible node. No M2 or B3 is assumed.
-/
namespace SuccessorTree.V10

/-- Both directed atoms (including absent ones) of every real pair of
the original source L-model survive padding and the capped image. -/
theorem shapeMap_padded_cap_real_binary
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : AgeTestModel db du dd)
    (B : EnumeratedPartialStructure db du dd)
    (hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L)
    (n N : Nat) (hSize : B.size = NonedgePadding.size n N)
    (hL : B.L = NonedgePadding.model A n N)
    (i j : Nat) (hi : i < N) (hj : j < N) (t : Fin db) :
    let u := NonedgePadding.socleCapNode family B hAvoidB
    ∃ (_hiF : kptShapeLevelMap family F (NonedgePadding.address n i) <
          LevelTree.lev (F u))
      (_hjF : kptShapeLevelMap family F (NonedgePadding.address n j) <
          LevelTree.lev (F u)),
      (F u).1.2.ageModel.binary
          (kptShapeLevelMap family F (NonedgePadding.address n i))
          (kptShapeLevelMap family F (NonedgePadding.address n j)) t =
        A.binary i j t := by
  have hiB : NonedgePadding.address n i < B.size := by
    rw [hSize]
    exact NonedgePadding.address_lt_size n N i hi
  have hjB : NonedgePadding.address n j < B.size := by
    rw [hSize]
    exact NonedgePadding.address_lt_size n N j hj
  obtain ⟨hiF,hjF,hPair⟩ :=
    shapeMap_socleCap_all_binary family F B hAvoidB
      (NonedgePadding.address n i) (NonedgePadding.address n j) hiB hjB t
  refine ⟨hiF,hjF,hPair.trans ?_⟩
  rw [hL]
  simp [NonedgePadding.model, NonedgePadding.address_real,
    NonedgePadding.project_address]

/-- Every real vertex also keeps its unary and diagonal L atoms,
including negative singleton facts. -/
theorem shapeMap_padded_cap_real_singletons
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : AgeTestModel db du dd)
    (B : EnumeratedPartialStructure db du dd)
    (hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L)
    (n N : Nat) (hSize : B.size = NonedgePadding.size n N)
    (hL : B.L = NonedgePadding.model A n N)
    (i : Nat) (hi : i < N) :
    let u := NonedgePadding.socleCapNode family B hAvoidB
    ∃ (_hiF : kptShapeLevelMap family F (NonedgePadding.address n i) <
          LevelTree.lev (F u)),
      (∀ t : Fin du,
        (F u).1.2.ageModel.unary
          (kptShapeLevelMap family F (NonedgePadding.address n i)) t =
            A.unary i t) ∧
      (∀ t : Fin dd,
        (F u).1.2.ageModel.diagonal
          (kptShapeLevelMap family F (NonedgePadding.address n i)) t =
            A.diagonal i t) := by
  have hiB : NonedgePadding.address n i < B.size := by
    rw [hSize]
    exact NonedgePadding.address_lt_size n N i hi
  obtain ⟨hiF,hU,hD⟩ :=
    shapeMap_socleCap_all_singletons family F B hAvoidB
      (NonedgePadding.address n i) hiB
  refine ⟨hiF,?_,?_⟩
  · intro t
    calc
      (F (NonedgePadding.socleCapNode family B hAvoidB)).1.2.ageModel.unary
          (kptShapeLevelMap family F (NonedgePadding.address n i)) t =
        B.L.unary (NonedgePadding.address n i) t := hU t
      _ = A.unary i t := by
        rw [hL]
        simp [NonedgePadding.model, NonedgePadding.address_real,
          NonedgePadding.project_address]
  · intro t
    calc
      (F (NonedgePadding.socleCapNode family B hAvoidB)).1.2.ageModel.diagonal
          (kptShapeLevelMap family F (NonedgePadding.address n i)) t =
        B.L.diagonal (NonedgePadding.address n i) t := hD t
      _ = A.diagonal i t := by
        rw [hL]
        simp [NonedgePadding.model, NonedgePadding.address_real,
          NonedgePadding.project_address]

/-- Upper--upper pair record for two selected forbidden-copy vertices,
in the same capped image. This preserves *negative* directed atoms as
well as positive ones; it does not merely give a homomorphism. -/
theorem shapeMap_boundedCopy_cap_upper_pair
    {n m r db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (V : AgeTestModel db du dd) (e : Fin r → Nat)
    (B : EnumeratedPartialStructure db du dd)
    (hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L)
    (hSize : B.size = NonedgePadding.size n (n+r))
    (hL : B.L = NonedgePadding.model
      (boundedCopySourceAge V (kptShapeLevelMap family F) n m r e) n (n+r))
    (a b : Fin r) (ha : m < e a) (hb : m < e b)
    (t : Fin db) :
    let u := NonedgePadding.socleCapNode family B hAvoidB
    ∃ (_haF : kptShapeLevelMap family F
            (NonedgePadding.address n (n+a.val)) < LevelTree.lev (F u))
      (_hbF : kptShapeLevelMap family F
            (NonedgePadding.address n (n+b.val)) < LevelTree.lev (F u)),
      (F u).1.2.ageModel.binary
          (kptShapeLevelMap family F (NonedgePadding.address n (n+a.val)))
          (kptShapeLevelMap family F (NonedgePadding.address n (n+b.val))) t =
        V.binary (e a) (e b) t := by
  obtain ⟨haF,hbF,hPair⟩ :=
    shapeMap_padded_cap_real_binary family F
      (boundedCopySourceAge V (kptShapeLevelMap family F) n m r e)
      B hAvoidB n (n+r) hSize hL
      (n+a.val) (n+b.val) (by omega) (by omega) t
  refine ⟨haF,hbF,?_⟩
  exact hPair.trans (boundedCopySourceAge_upper_pair V
    (kptShapeLevelMap family F) n m r e a b ha hb t)

end SuccessorTree.V10

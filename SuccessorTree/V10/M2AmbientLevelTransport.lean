import SuccessorTree.V10.ShapeMapAmbientOrdinaryTransport
import SuccessorTree.V10.LevelRemovalSkipsOnly
import Mathlib.Tactic

/-!
# Complete ambient ordinary type at the explicit ShapeMap image coordinate

The canonical parameter-prefix theorem provides an ancestor a at level j.
Replace its image level by the common concrete level function λ(j).
This is essential for the final B3 forbidden-copy embedding: the same
numerical coordinate is used for upper--upper retained-record recovery.
-/

namespace SuccessorTree.V10

/-- A selected ordinary source vertex has in F(u) the entire image
parameter type F(t), at its **actual** coordinate λ(j), and through
all levels of F(t), including those skipped by λ on the source socle.
No extra age or M2 hypothesis is used. -/
theorem shapeMap_transports_ambient_ordinary_type_at_levelMap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : EnumeratedPartialStructure db du dd)
    (v j n : Nat) (hv : v < A.size)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hCut : j + 1 ≤ A.freeLevel v)
    (hPos : 0 < A.freeLevel j)
    (hn : n ≤ A.freeLevel j)
    (u t : AdmissibleKptNode family)
    (hu : u.1 = A.rawTypeAtFree v)
    (ht : t.1 =
      (⟨n, A.partialTypeAt n j⟩ : RawPartialTypeNode db du dd)) :
    ∃ (hAddress : kptShapeLevelMap family F j < LevelTree.lev (F u))
      (hSocle : LevelTree.lev (F t) ≤ LevelTree.lev (F u)),
      (F u).1.2.ordinaryType
        (kptShapeLevelMap family F j) hAddress
        (LevelTree.lev (F t)) hSocle = (F t).1.2 := by
  obtain ⟨a,hAddress,hSocle,hLevelA,hType⟩ :=
    shapeMap_transports_ambient_ordinary_type
      family F A v j n hv hAvoid hCut hPos hn u t hu ht
  have hImage : LevelTree.lev (F a) = kptShapeLevelMap family F j := by
    simpa only [hLevelA] using (kptShapeLevelMap_eq family F a).symm
  have hAddressNew : kptShapeLevelMap family F j < LevelTree.lev (F u) := by
    rw [← hImage]
    exact hAddress
  refine ⟨hAddressNew,hSocle,?_⟩
  simpa only [← hImage] using hType

end SuccessorTree.V10

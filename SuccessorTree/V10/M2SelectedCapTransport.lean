import SuccessorTree.V10.M2AmbientLevelTransport
import SuccessorTree.V10.M2TwoTypeImageCompatibility
import SuccessorTree.V10.NonedgePaddingSocleCap
import Mathlib.Tactic

/-!
# Transport a selected padded source vertex into one capped ShapeMap image

Nonedge padding makes selected complete source types genuine parameter
prefixes. The neutral socle cap puts ALL these selected vertices below
one common top node. The canonical parameter-prefix theorem therefore
recovers their entire image types at the explicit retained numerical
coordinates, including the omitted level of the M2 gap.
-/
namespace SuccessorTree.V10

/-- Every selected type realized by a padded witness occurs with the
ENTIRE prescribed L+ image type at its actual level-map address in the
image of that witness's single neutral cap.  The source type need not
coincide with the distinguished type of the cap vertex. -/
theorem shapeMap_transports_padded_selected_type
    {n db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (B : EnumeratedPartialStructure db du dd)
    (hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L)
    (j : Nat) (hnPos : 0 < n) (hnj : n ≤ j) (hj : j < B.size)
    (T : PartialTypeWithE n db du dd)
    (hAd : IsAdmissibleRawType family
      (⟨n,T⟩ : RawPartialTypeNode db du dd))
    (hType : B.partialTypeAt n j = T) :
    let u := NonedgePadding.socleCapNode family B hAvoidB
    let t : AdmissibleKptNode family := ⟨⟨n,T⟩,hAd⟩
    ∃ (hAddress : kptShapeLevelMap family F j < LevelTree.lev (F u))
      (hSocle : LevelTree.lev (F t) ≤ LevelTree.lev (F u)),
      (F u).1.2.ordinaryType
        (kptShapeLevelMap family F j) hAddress
        (LevelTree.lev (F t)) hSocle = (F t).1.2 := by
  let A := NonedgePadding.socleCap B
  let v := B.size+1
  let u := NonedgePadding.socleCapNode family B hAvoidB
  let t : AdmissibleKptNode family := ⟨⟨n,T⟩,hAd⟩
  have hv : v < A.size := by change B.size+1 < B.size+2; omega
  have hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    NonedgePadding.socleCap_avoids family B hAvoidB
  have hCapFree : A.freeLevel v = B.size :=
    NonedgePadding.socleCap_freeLevel B
  have hCut : j+1 ≤ A.freeLevel v := by rw [hCapFree]; omega
  have hOldFree : A.freeLevel j = B.freeLevel j :=
    NonedgePadding.socleCap_old_freeLevel B j hj
  have hSourceFree : n ≤ B.freeLevel j :=
    partialTypeAt_freeLevel_ge_of_admissible family B j T hAd hType
  have hPos : 0 < A.freeLevel j := by rw [hOldFree]; omega
  have hn : n ≤ A.freeLevel j := by rw [hOldFree]; exact hSourceFree
  have hu : u.1 = A.rawTypeAtFree v := by
    change (⟨B.size,A.partialTypeAt B.size (B.size+1)⟩ :
      RawPartialTypeNode db du dd) =
      (⟨A.freeLevel v,A.partialTypeAt (A.freeLevel v) v⟩ :
      RawPartialTypeNode db du dd)
    rw [hCapFree]
  have ht : t.1 =
      (⟨n,A.partialTypeAt n j⟩ : RawPartialTypeNode db du dd) := by
    apply congrArg (Sigma.mk n)
    calc
      T = B.partialTypeAt n j := hType.symm
      _ = A.partialTypeAt n j :=
        (NonedgePadding.socleCap_partialTypeAt B n j hnj hj).symm
  exact shapeMap_transports_ambient_ordinary_type_at_levelMap
    family F A v j n hv hAvoidA hCut hPos hn u t hu ht

end SuccessorTree.V10
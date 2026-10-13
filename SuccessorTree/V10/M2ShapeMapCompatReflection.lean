import SuccessorTree.V10.ShapeMapFullRecovery
import SuccessorTree.V10.PrescribedBoringData
import Mathlib.Tactic

/-!
# Reflection of complete ordinary L+ compatibility under a Kpt shape map

The checked retained-record theorem gives back the original source
L+ record by reindexing the full image at retained coordinates.
Consequently equality of the image ordinary socles forces equality
of the original ordinary socles.  This is needed when the deleted
boundary images have a common socle in the M2 B2 proof.
-/
namespace SuccessorTree.V10

noncomputable def PartialTypeWithE.reindexOrdinary
    {n m db du dd : Nat}
    (Q : PartialTypeWithE m db du dd) (rho : Fin n → Fin m) :
    PartialTypeWithE n db du dd :=
  let idx := Option.map rho
  { lReduct :=
      { binary := fun x y t => Q.lReduct.binary (idx x) (idx y) t
        unary := fun x t => Q.lReduct.unary (idx x) t
        diagonal := fun x t => Q.lReduct.diagonal (idx x) t }
    eRelation := fun x y => Q.eRelation (idx x) (idx y) }

/-- Equality of ordinary L+ socles survives any shared induced
reindexing of their ordinary coordinates, even at dependent sizes. -/
theorem sameOrdinaryAtCut_reindex
    {n m k db du dd : Nat}
    (Q : PartialTypeWithE m db du dd)
    (R : PartialTypeWithE k db du dd)
    (h : m = k)
    (hComp : SameOrdinaryAtCut Q
      (cast (congrArg (fun l => PartialTypeWithE l db du dd) h.symm) R))
    (rhoQ : Fin n → Fin m) (rhoR : Fin n → Fin k)
    (hRho : ∀ i, rhoQ i = Fin.cast h.symm (rhoR i)) :
    SameOrdinaryAtCut (Q.reindexOrdinary rhoQ) (R.reindexOrdinary rhoR) := by
  cases h
  have hSame : rhoQ = rhoR := by
    funext i
    exact hRho i
  subst rhoR
  change SameOrdinaryAtCut Q R at hComp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j t
    exact hComp.1 (rhoQ i) (rhoQ j) t
  · intro i t
    exact hComp.2.1 (rhoQ i) t
  · intro i t
    exact hComp.2.2.1 (rhoQ i) t
  · intro i j
    exact hComp.2.2.2 (rhoQ i) (rhoQ j)

/-- Source ordinary L+ compatibility is reflected by EVERY genuine
shape-preserving map, not only by intrinsic M2 deletion.  This uses the
full retained source record, including absent directed L and E bits. -/
theorem shapeMap_reflects_source_compatibility
    {n db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (T U : PartialTypeWithE n db du dd)
    (hT : IsAdmissibleRawType family
      (⟨n,T⟩ : RawPartialTypeNode db du dd))
    (hU : IsAdmissibleRawType family
      (⟨n,U⟩ : RawPartialTypeNode db du dd))
    (hImage :
      let ti : AdmissibleKptNode family := ⟨⟨n,T⟩,hT⟩
      let tj : AdmissibleKptNode family := ⟨⟨n,U⟩,hU⟩
      ∃ h : LevelTree.lev (F ti) = LevelTree.lev (F tj),
        SameOrdinaryAtCut (F ti).1.2
          (cast (congrArg (fun k => PartialTypeWithE k db du dd)
            h.symm) (F tj).1.2)) :
    SameOrdinaryAtCut T U := by
  let ti : AdmissibleKptNode family := ⟨⟨n,T⟩,hT⟩
  let tj : AdmissibleKptNode family := ⟨⟨n,U⟩,hU⟩
  obtain ⟨h,hComp⟩ := hImage
  have hRho (i : Fin n) :
      retainedSocleIndex family F ti i =
        Fin.cast h.symm (retainedSocleIndex family F tj i) := by
    apply Fin.ext
    rfl
  have hPul := sameOrdinaryAtCut_reindex (F ti).1.2 (F tj).1.2
    h hComp (retainedSocleIndex family F ti)
    (retainedSocleIndex family F tj) hRho
  change SameOrdinaryAtCut (shapeMapRetainedRecord family F ti)
    (shapeMapRetainedRecord family F tj) at hPul
  rw [shapeMap_recovers_complete_record family F ti,
      shapeMap_recovers_complete_record family F tj] at hPul
  exact hPul

end SuccessorTree.V10
